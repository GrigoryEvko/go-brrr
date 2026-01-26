fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Compile the TEI (Text Embeddings Inference) gRPC protocol
    tonic_build::configure()
        .build_server(false)
        .compile_protos(&["proto/tei.proto"], &["proto/"])?;

    // Re-run build script if the proto file changes
    println!("cargo:rerun-if-changed=proto/tei.proto");

    Ok(())
}
