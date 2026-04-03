
use tree_sitter::Language;

extern "C" {
    fn tree_sitter_lean() -> Language;
}


pub fn language() -> Language {
    unsafe { tree_sitter_lean() }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_can_load_grammar() {
        let mut parser = tree_sitter::Parser::new();
        parser
            .set_language(&super::language())
            .expect("Error loading lean language");
    }
}
