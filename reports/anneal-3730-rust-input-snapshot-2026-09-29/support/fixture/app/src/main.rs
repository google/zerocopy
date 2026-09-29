use doc_macro::DocWitness;

/// proof: alpha
#[derive(DocWitness)]
struct Marker;

const INCLUDED: &str = include_str!("proof_note.txt");

fn main() {
    #[cfg(feature = "selected")]
    let feature = 10;
    #[cfg(not(feature = "selected"))]
    let feature = 0;
    println!("macro={} included={} feature={}", Marker::DOC_TAG, INCLUDED.trim(), feature);
}
