//! Build script for compiling TEI protobuf definitions.
//!
//! Uses tonic-build to generate Rust code from proto files.

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Rerun build if proto files change
    println!("cargo:rerun-if-changed=proto/tei.proto");

    // Compile the TEI proto file with tonic-build 0.12 API
    tonic_build::configure()
        .build_server(false) // Only need client stubs
        .build_client(true)
        .compile_protos(&["proto/tei.proto"], &["proto/"])?;

    Ok(())
}
