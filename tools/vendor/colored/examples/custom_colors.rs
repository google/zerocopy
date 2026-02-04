use colored::*;
fn main() {
    let my_color = CustomColor::new(0, 120, 120);
    println!("{}", "Greetings from Ukraine".custom_color(my_color));
    println!("{}", "Slava Ukraini!".on_custom_color(my_color));
    println!("{}", "Hello World!".on_custom_color((0, 120, 120)));
}
