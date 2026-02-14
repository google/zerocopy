
macro_rules! hygiene_check {
    () => {
        let x = 1;
        let x = x + 1;
    };
}

pub fn check_hygiene() {
    hygiene_check!();
}
