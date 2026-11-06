use proc_macro::TokenStream;

#[proc_macro_derive(DocWitness)]
pub fn doc_witness(input: TokenStream) -> TokenStream {
    let source = input.to_string();
    let value = if source.contains("proof: alpha") {
        1
    } else if source.contains("proof: beta") {
        2
    } else {
        0
    };
    format!("impl Marker {{ const DOC_TAG: usize = {value}; }}")
        .parse()
        .expect("fixed generated item parses")
}
