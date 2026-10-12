fn main() {
    println!("cargo:rerun-if-changed=model.onnx");
    burn_onnx::ModelGen::new()
        .input("model.onnx")
        .out_dir("model/")
        .load_strategy(burn_onnx::LoadStrategy::Embedded)
        .run_from_script();
}
