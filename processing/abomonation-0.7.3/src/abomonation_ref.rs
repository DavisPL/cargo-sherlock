//! AbomonationRef<'a> (spelling intentional) is a fast serialization / deserialization crate.
//!
//! AbomonationRef<'a> takes typed elements and simply writes their contents as binary.
//! It then gives the element the opportunity to serialize more data, which is
//! useful for types with owned memory such as `String` and `Vec`.
//! The result is effectively a copy of reachable memory.
//! Deserialization results in a shared reference to the type, pointing at the binary data itself.
//!
//! AbomonationRef<'a> does several unsafe things, and should ideally be used only through the methods
//! `encode` and `decode` on types implementing the `AbomonationRef<'a>` trait. Implementing the
//! `AbomonationRef<'a>` trait is highly discouraged; instead, you can use the [`AbomonationRef<'a>_derive` crate](https://crates.io/crates/AbomonationRef<'a>_derive).
//!
//! **Very important**: AbomonationRef<'a> reproduces the memory as laid out by the serializer, which will
//! reveal architectural variations. Data encoded on a 32bit big-endian machine will not decode
//! properly on a 64bit little-endian machine. Moreover, it could result in undefined behavior if
//! the deserialization results in invalid typed data. Please do not do this.
//!
//!
//! # Examples
//! ```
//! use abomonation::abomonation_ref::{encode, decode};
//!
//! // create some test data out of AbomonationRef-approved types
//! let vector = (0..256u64).map(|i| (i, "hello"))
//!                         .collect::<Vec<_>>();
//!
//! // encode a &[(u64, &str)] into a Vec<u8>
//! let mut bytes = Vec::new();
//! unsafe { encode(&&vector[..], &mut bytes); }
//!
//! // decode a &[(u64, &str)] from &mut [u8] binary data
//! if let Some((result, remaining)) = unsafe { decode::<&[(u64, &str)]>(&mut bytes) } {
//!     assert!(result == &&vector[..]);
//!     assert!(remaining.len() == 0);
//! }
//! ```

use ::std::mem;       // yup, used pretty much everywhere.
use ::std::io::Write; // for bytes.write_all; push_all is unstable and extend is slow.
use ::std::io::Result as IOResult;
use ::std::marker::PhantomData;

/// Encodes a typed reference into a binary buffer.
///
/// # Safety
///
/// This method is unsafe because it is unsafe to transmute typed allocations to binary.
/// Furthermore, Rust currently indicates that it is undefined behavior to observe padding
/// bytes, which will happen when we `memmcpy` structs which contain padding bytes.
///
/// # Examples
/// ```
/// use abomonation::abomonation_ref::{encode, decode};
///
/// // create some test data out of AbomonationRef-approved types
/// let vector = (0..256u64).map(|i| (i, "hello"))
///                         .collect::<Vec<_>>();
///
/// // encode a &[(u64, &str)] into a Vec<u8>
/// let mut bytes = Vec::new();
/// unsafe { encode(&&vector[..], &mut bytes); }
///
/// // decode a &[(u64, &str)] from &mut [u8] binary data
/// if let Some((result, remaining)) = unsafe { decode::<&[(u64, &str)]>(&mut bytes) } {
///     assert!(result == &&vector[..]);
///     assert!(remaining.len() == 0);
/// }
/// ```
///
#[inline]
pub unsafe fn encode<'a, T: AbomonationRef<'a>, W: Write>(typed: &T, write: &mut W) -> IOResult<()> {
    let slice = ::std::slice::from_raw_parts(mem::transmute(typed), mem::size_of::<T>());
    write.write_all(slice)?;
    typed.entomb(write)?;
    Ok(())
}

/// Decodes a mutable binary slice into an immutable typed reference.
///
/// `decode` treats the first `mem::size_of::<T>()` bytes as a `T`, and will then `exhume` the
/// element, offering it the ability to consume prefixes of `bytes` to back any owned data.
/// The return value is either a pair of the typed reference `&T` and the remaining `&mut [u8]`
/// binary data, or `None` if decoding failed due to lack of data.
///
/// # Safety
///
/// The `decode` method is unsafe due to a number of unchecked invariants.
///
/// Decoding arbitrary `&[u8]` data can
/// result in invalid utf8 strings, enums with invalid discriminants, etc. `decode` *does*
/// perform bounds checks, as part of determining if enough data are present to completely decode,
/// and while it should only write within the bounds of its `&mut [u8]` argument, the use of invalid
/// utf8 and enums are undefined behavior.
///
/// Please do not decode data that was not encoded by the corresponding implementation.
///
/// In addition, `decode` does not ensure that the bytes representing types will be correctly aligned.
/// On several platforms unaligned reads are undefined behavior, but on several other platforms they
/// are only a performance penalty.
///
/// # Examples
/// ```
/// use abomonation::abomonation_ref::{encode, decode};
///
/// // create some test data out of AbomonationRef-approved types
/// let vector = (0..256u64).map(|i| (i, "hello"))
///                         .collect::<Vec<_>>();
///
/// // encode a &[(u64, &str)] into a Vec<u8>
/// let mut bytes = Vec::new();
/// unsafe { encode(&&vector[..], &mut bytes); }
///
/// // decode a &[(u64, &str)] from &mut [u8] binary data
/// if let Some((result, remaining)) = unsafe { decode::<&[(u64, &str)]>(&mut bytes) } {
///     assert!(result == &&vector[..]);
///     assert!(remaining.len() == 0);
/// }
/// ```
#[inline]
pub unsafe fn decode<'a, T: AbomonationRef<'a>>(bytes: &'a mut [u8]) -> Option<(&'a T, &'a mut [u8])> {
    if bytes.len() < mem::size_of::<T>() { None }
    else {
        let (split1, split2) = bytes.split_at_mut(mem::size_of::<T>());
        let result: &mut T = mem::transmute(split1.get_unchecked_mut(0));
        if let Some(remaining) = result.exhume(split2) {
            Some((result, remaining))
        }
        else {
            None
        }
    }
}

/// Reports the number of bytes required to encode `self`.
///
/// # Safety
///
/// The `measure` method is safe. It neither produces nor consults serialized representations.
#[inline]
pub fn measure<'a, T: AbomonationRef<'a>>(typed: &T) -> usize {
    mem::size_of::<T>() + typed.extent()
}

/// AbomonationRef<'a> provides methods to serialize any heap data the implementor owns.
///
/// The default implementations for AbomonationRef<'a>'s methods are all empty. Many types have no owned
/// data to transcribe. Some do, however, and need to carefully implement these unsafe methods.
///
/// # Safety
///
/// AbomonationRef<'a> has no safe methods. Please do not call them. They should be called only by
/// `encode` and `decode`, each of which impose restrictions on ownership and lifetime of the data
/// they take as input and return as output.
///
/// If you are concerned about safety, it may be best to avoid AbomonationRef<'a> all together. It does
/// several things that may be undefined behavior, depending on how undefined behavior is defined.
pub trait AbomonationRef<'a> {

    /// Write any additional information about `&self` beyond its binary representation.
    ///
    /// Most commonly this is owned data on the other end of pointers in `&self`. The return value
    /// reports any failures in writing to `write`.
    #[inline(always)] unsafe fn entomb<W: Write>(&self, _write: &mut W) -> IOResult<()> { Ok(()) }

    /// Recover any information for `&mut self` not evident from its binary representation.
    ///
    /// Most commonly this populates pointers with valid references into `bytes`.
    #[inline(always)] unsafe fn exhume<'b>(&'b mut self, bytes: &'a mut [u8]) -> Option<&'a mut [u8]> { Some(bytes) }

    /// Reports the number of further bytes required to entomb `self`.
    #[inline(always)] fn extent(&self) -> usize { 0 }
}

/// The `unsafe_abomonate!` macro takes a type name with an optional list of fields, and implements
/// `AbomonationRef<'a>` for the type, following the pattern of the tuple implementations: each method
/// calls the equivalent method on each of its fields.
///
/// It is strongly recommended that you use the `AbomonationRef<'a>_derive` crate instead of this macro.
///
/// # Safety
/// `unsafe_abomonate` is unsafe because if you fail to specify a field it will not be properly
/// re-initialized from binary data. This can leave you with a dangling pointer, or worse.
///
/// # Examples
/// ```
/// #[macro_use]
/// extern crate abomonation;
/// use abomonation::abomonation_ref::{encode, decode, AbomonationRef};
///
/// #[derive(Eq, PartialEq)]
/// struct MyStruct {
///     a: String,
///     b: u64,
///     c: Vec<u8>,
/// }
///
/// unsafe_abomonate_ref!(MyStruct : a, b, c);
///
/// fn main() {
///
///     // create some test data out of recently-abomonable types
///     let my_struct = MyStruct { a: "grawwwwrr".to_owned(), b: 0, c: vec![1,2,3] };
///
///     // encode a &MyStruct into a Vec<u8>
///     let mut bytes = Vec::new();
///     unsafe { encode(&my_struct, &mut bytes); }
///
///     // decode a &MyStruct from &mut [u8] binary data
///     if let Some((result, remaining)) = unsafe { decode::<MyStruct>(&mut bytes) } {
///         assert!(result == &my_struct);
///         assert!(remaining.len() == 0);
///     }
/// }
/// ```
#[macro_export]
#[deprecated(since="0.5", note="please use the AbomonationRef<'a>_derive crate")]
macro_rules! unsafe_abomonate_ref {
    ($t:ty) => {
        impl<'a> AbomonationRef<'a> for $t { }
    };
    ($t:ty : $($field:ident),*) => {
        impl<'a> AbomonationRef<'a> for $t {
            #[inline] unsafe fn entomb<W: ::std::io::Write>(&self, write: &mut W) -> ::std::io::Result<()> {
                $( self.$field.entomb(write)?; )*
                Ok(())
            }
            #[inline] unsafe fn exhume<'b>(&'b mut self, mut bytes: &'a mut [u8]) -> Option<&'a mut [u8]> {
                $( let temp = bytes; bytes = self.$field.exhume(temp)?; )*
                Some(bytes)
            }
            #[inline] fn extent(&self) -> usize {
                let mut size = 0;
                $( size += self.$field.extent(); )*
                size
            }
        }
    };
}

// general code for tuples (can't use '0', '1', ... as field identifiers)
macro_rules! tuple_abomonate {
    ( $($name:ident)+) => (
        impl<'a, $($name: AbomonationRef<'a>),*> AbomonationRef<'a> for ($($name,)*) {
            #[allow(non_snake_case)]
            #[inline(always)] unsafe fn entomb<WRITE: Write>(&self, write: &mut WRITE) -> IOResult<()> {
                let ($(ref $name,)*) = *self;
                $($name.entomb(write)?;)*
                Ok(())
            }
            #[allow(non_snake_case)]
            #[inline(always)] unsafe fn exhume<'b>(&'b mut self, mut bytes: &'a mut [u8]) -> Option<&'a mut [u8]> {
                let ($(ref mut $name,)*) = *self;
                $( let temp = bytes; bytes = $name.exhume(temp)?; )*
                Some(bytes)
            }
            #[allow(non_snake_case)]
            #[inline(always)] fn extent(&self) -> usize {
                let mut size = 0;
                let ($(ref $name,)*) = *self;
                $( size += $name.extent(); )*
                size
            }
        }
    );
}

impl<'a> AbomonationRef<'a> for u8 { }
impl<'a> AbomonationRef<'a> for u16 { }
impl<'a> AbomonationRef<'a> for u32 { }
impl<'a> AbomonationRef<'a> for u64 { }
impl<'a> AbomonationRef<'a> for usize { }

impl<'a> AbomonationRef<'a> for i8 { }
impl<'a> AbomonationRef<'a> for i16 { }
impl<'a> AbomonationRef<'a> for i32 { }
impl<'a> AbomonationRef<'a> for i64 { }
impl<'a> AbomonationRef<'a> for isize { }

impl<'a> AbomonationRef<'a> for f32 { }
impl<'a> AbomonationRef<'a> for f64 { }

impl<'a> AbomonationRef<'a> for bool { }
impl<'a> AbomonationRef<'a> for () { }

impl<'a> AbomonationRef<'a> for char { }

impl<'a> AbomonationRef<'a> for ::std::time::Duration { }

impl<'a, T> AbomonationRef<'a> for PhantomData<T> {}

impl<'a, T: AbomonationRef<'a>> AbomonationRef<'a> for Option<T> {
    #[inline(always)] unsafe fn entomb<W: Write>(&self, write: &mut W) -> IOResult<()> {
        if let &Some(ref inner) = self {
            inner.entomb(write)?;
        }
        Ok(())
    }
    #[inline(always)] unsafe fn exhume<'b>(&'b mut self, mut bytes: &'a mut[u8]) -> Option<&'a mut [u8]> {
        if let &mut Some(ref mut inner) = self {
            let tmp = bytes; bytes = inner.exhume(tmp)?;
        }
        Some(bytes)
    }
    #[inline] fn extent(&self) -> usize {
        self.as_ref().map(|inner| inner.extent()).unwrap_or(0)
    }
}

impl<'a, T: AbomonationRef<'a>, E: AbomonationRef<'a>> AbomonationRef<'a> for Result<T, E> {
    #[inline(always)] unsafe fn entomb<W: Write>(&self, write: &mut W) -> IOResult<()> {
        match self {
            &Ok(ref inner) => inner.entomb(write)?,
            &Err(ref inner) => inner.entomb(write)?,
        };
        Ok(())
    }
    #[inline(always)] unsafe fn exhume<'b>(&'b mut self, bytes: &'a mut[u8]) -> Option<&'a mut [u8]> {
        match self {
            &mut Ok(ref mut inner) => inner.exhume(bytes),
            &mut Err(ref mut inner) => inner.exhume(bytes),
        }
    }
    #[inline] fn extent(&self) -> usize {
        match self {
            &Ok(ref inner) => inner.extent(),
            &Err(ref inner) => inner.extent(),
        }
    }
}

tuple_abomonate!(A);
tuple_abomonate!(A B);
tuple_abomonate!(A B C);
tuple_abomonate!(A B C D);
tuple_abomonate!(A B C D E);
tuple_abomonate!(A B C D E F);
tuple_abomonate!(A B C D E F G);
tuple_abomonate!(A B C D E F G H);
tuple_abomonate!(A B C D E F G H I);
tuple_abomonate!(A B C D E F G H I J);
tuple_abomonate!(A B C D E F G H I J K);
tuple_abomonate!(A B C D E F G H I J K L);
tuple_abomonate!(A B C D E F G H I J K L M);
tuple_abomonate!(A B C D E F G H I J K L M N);
tuple_abomonate!(A B C D E F G H I J K L M N O);
tuple_abomonate!(A B C D E F G H I J K L M N O P);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T U);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T U V);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T U V W);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T U V W X);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T U V W X Y);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T U V W X Y Z);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T U V W X Y Z AA);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T U V W X Y Z AA AB);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T U V W X Y Z AA AB AC);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T U V W X Y Z AA AB AC AD);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T U V W X Y Z AA AB AC AD AE);
tuple_abomonate!(A B C D E F G H I J K L M N O P Q R S T U V W X Y Z AA AB AC AD AE AF);


macro_rules! array_abomonate {
    ($size:expr) => (
        impl<'a, T: AbomonationRef<'a>> AbomonationRef<'a> for [T; $size] {
            #[inline(always)]
            unsafe fn entomb<W: Write>(&self, write: &mut W) ->  IOResult<()> {
                for element in self { element.entomb(write)?; }
                Ok(())
            }
            #[inline(always)]
            unsafe fn exhume<'b>(&'b mut self, mut bytes: &'a mut[u8]) -> Option<&'a mut [u8]> {
                for element in self {
                    let tmp = bytes; bytes = element.exhume(tmp)?;
                }
                Some(bytes)
            }
            #[inline(always)] fn extent(&self) -> usize {
                let mut size = 0;
                for element in self {
                    size += element.extent();
                }
                size
            }
        }
    )
}

array_abomonate!(0);
array_abomonate!(1);
array_abomonate!(2);
array_abomonate!(3);
array_abomonate!(4);
array_abomonate!(5);
array_abomonate!(6);
array_abomonate!(7);
array_abomonate!(8);
array_abomonate!(9);
array_abomonate!(10);
array_abomonate!(11);
array_abomonate!(12);
array_abomonate!(13);
array_abomonate!(14);
array_abomonate!(15);
array_abomonate!(16);
array_abomonate!(17);
array_abomonate!(18);
array_abomonate!(19);
array_abomonate!(20);
array_abomonate!(21);
array_abomonate!(22);
array_abomonate!(23);
array_abomonate!(24);
array_abomonate!(25);
array_abomonate!(26);
array_abomonate!(27);
array_abomonate!(28);
array_abomonate!(29);
array_abomonate!(30);
array_abomonate!(31);
array_abomonate!(32);

impl<'a> AbomonationRef<'a> for String {
    #[inline]
    unsafe fn entomb<W: Write>(&self, write: &mut W) -> IOResult<()> {
        write.write_all(self.as_bytes())?;
        Ok(())
    }
    #[inline]
    unsafe fn exhume<'b>(&'b mut self, bytes: &'a mut [u8]) -> Option<&'a mut [u8]> {
        if self.len() > bytes.len() { None }
        else {
            let (mine, rest) = bytes.split_at_mut(self.len());
            ::std::ptr::write(self, String::from_raw_parts(mem::transmute(mine.as_ptr()), self.len(), self.len()));
            Some(rest)
        }
    }
    #[inline] fn extent(&self) -> usize {
        self.len()
    }
}

impl<'a, T: AbomonationRef<'a>> AbomonationRef<'a> for Vec<T> {
    #[inline]
    unsafe fn entomb<W: Write>(&self, write: &mut W) -> IOResult<()> {
        write.write_all(typed_to_bytes(&self[..]))?;
        for element in self.iter() { element.entomb(write)?; }
        Ok(())
    }
    #[inline]
    unsafe fn exhume<'b>(&'b mut self, bytes: &'a mut [u8]) -> Option<&'a mut [u8]> {

        // extract memory from bytes to back our vector
        let binary_len = self.len() * mem::size_of::<T>();
        if binary_len > bytes.len() { None }
        else {
            let (mine, mut rest) = bytes.split_at_mut(binary_len);
            let slice = ::std::slice::from_raw_parts_mut(mine.as_mut_ptr() as *mut T, self.len());
            ::std::ptr::write(self, Vec::from_raw_parts(slice.as_mut_ptr(), self.len(), self.len()));
            for element in self.iter_mut() {
                let temp = rest;             // temp variable explains lifetimes (mysterious!)
                rest = element.exhume(temp)?;
            }
            Some(rest)
        }
    }
    #[inline]
    fn extent(&self) -> usize {
        let mut sum = mem::size_of::<T>() * self.len();
        for element in self.iter() {
            sum += element.extent();
        }
        sum
    }
}

impl<'a, T: AbomonationRef<'a>> AbomonationRef<'a> for Box<T> {
    #[inline]
    unsafe fn entomb<W: Write>(&self, bytes: &mut W) -> IOResult<()> {
        bytes.write_all(::std::slice::from_raw_parts(mem::transmute(&**self), mem::size_of::<T>()))?;
        (**self).entomb(bytes)?;
        Ok(())
    }
    #[inline]
    unsafe fn exhume<'b>(&'b mut self, bytes: &'a mut [u8]) -> Option<&'a mut [u8]> {
        let binary_len = mem::size_of::<T>();
        if binary_len > bytes.len() { None }
        else {
            let (mine, mut rest) = bytes.split_at_mut(binary_len);
            ::std::ptr::write(self, mem::transmute(mine.as_mut_ptr() as *mut T));
            let temp = rest; rest = (**self).exhume(temp)?;
            Some(rest)
        }
    }
    #[inline] fn extent(&self) -> usize {
        mem::size_of::<T>() + (&**self).extent()
    }
}

// NEW IMPLEMENTATIONS

impl<'a, 'c, T: AbomonationRef<'a>> AbomonationRef<'a> for &'c T where 'a : 'c {
    #[inline]
    unsafe fn entomb<W: Write>(&self, bytes: &mut W) -> IOResult<()> {
        bytes.write_all(::std::slice::from_raw_parts(mem::transmute(&**self), mem::size_of::<T>()))?;
        (**self).entomb(bytes)?;
        Ok(())
    }
    #[inline]
    unsafe fn exhume<'b>(&'b mut self, bytes: &'a mut [u8]) -> Option<&'a mut [u8]> {
        let binary_len = mem::size_of::<T>();
        if binary_len > bytes.len() { None }
        else {
            let (mine, mut rest) = bytes.split_at_mut(binary_len);
            let mut_ref: &mut T = mem::transmute(mine.as_mut_ptr() as *mut T);
            let temp = rest; rest = (*mut_ref).exhume(temp)?;
            *self = mut_ref;
            Some(rest)
        }
    }
    #[inline] fn extent(&self) -> usize {
        mem::size_of::<T>() + (&**self).extent()
    }
}

impl<'a, 'c> AbomonationRef<'a> for &'c str where 'a : 'c {
    #[inline]
    unsafe fn entomb<W: Write>(&self, write: &mut W) -> IOResult<()> {
        write.write_all(self.as_bytes())?;
        Ok(())
    }
    #[inline]
    unsafe fn exhume<'b>(&'b mut self, bytes: &'a mut [u8]) -> Option<&'a mut [u8]> {
        if self.len() > bytes.len() { None }
        else {
            let (mine, rest) = bytes.split_at_mut(self.len());
            let slice = ::std::slice::from_raw_parts(mine.as_ptr(), self.len());
            *self = ::std::str::from_utf8_unchecked(slice);
            Some(rest)
        }
    }
    #[inline] fn extent(&self) -> usize {
        self.len()
    }
}

impl<'a, 'c, T: AbomonationRef<'a>> AbomonationRef<'a> for &'c [T] where 'a : 'c {
    #[inline]
    unsafe fn entomb<W: Write>(&self, write: &mut W) -> IOResult<()> {
        write.write_all(typed_to_bytes(&self[..]))?;
        for element in self.iter() { element.entomb(write)?; }
        Ok(())
    }
    #[inline]
    unsafe fn exhume<'b>(&'b mut self, bytes: &'a mut [u8]) -> Option<&'a mut [u8]> {

        // extract memory from bytes to back our vector
        let binary_len = self.len() * mem::size_of::<T>();
        if binary_len > bytes.len() { None }
        else {
            let (mine, mut rest) = bytes.split_at_mut(binary_len);
            let slice = ::std::slice::from_raw_parts_mut(mine.as_mut_ptr() as *mut T, self.len());
            for element in slice.iter_mut() {
                let temp = rest;             // temp variable explains lifetimes (mysterious!)
                rest = element.exhume(temp)?;
            }
            *self = slice;
            Some(rest)
        }
    }
    #[inline]
    fn extent(&self) -> usize {
        let mut sum = mem::size_of::<T>() * self.len();
        for element in self.iter() {
            sum += element.extent();
        }
        sum
    }
}

// This method currently enables undefined behavior, by exposing padding bytes.
#[inline] unsafe fn typed_to_bytes<T>(slice: &[T]) -> &[u8] {
    ::std::slice::from_raw_parts(slice.as_ptr() as *const u8, slice.len() * mem::size_of::<T>())
}