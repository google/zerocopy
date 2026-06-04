require 'spec_helper'
require 'support/editor'

RSpec.feature "Automatically selecting the primary action", type: :feature, js: true do
  before { visit '/' }

  scenario "when the crate is a binary" do
    editor.set <<~EOF
      #![crate_type="bin"]
      fn main() {
          println!("Hello, world");
      }
    EOF
    click_on("Run")

    within(:output, :stdout) do
      expect(page).to have_content 'Hello, world'
    end
  end

  scenario "when the crate is a library" do
    editor.set <<~EOF
      #![crate_type="lib"]
      fn main() {
          println!("Hello, world");
      }
    EOF
    click_on("Build")

    within(:output, :stderr) do
      expect(page).to have_content 'function `main` is never used'
    end
  end

  scenario "when the crate is a procedural macro" do
    editor.set <<~EOF
      #![crate_type = "proc-macro"]

      use proc_macro::TokenStream;

      /// Example:
      /// ```
      /// playground::demo!();
      /// type T = aaa;
      /// ```
      #[proc_macro]
      pub fn demo(_input: TokenStream) -> TokenStream {
          eprintln!("wow wow");
          "struct Aaa;".parse().unwrap()
      }

      /*
      #[test]*/
    EOF
    click_on("Test")

    within(:output) do
      expect(page).to_not have_selector(:loader, wait: 15)
    end
    within(:output, :stdout) do
      expect(page).to have_content 'a struct with a similar name exists'
    end
  end

  scenario "when the crate is a library with tests" do
    editor.set <<~EOF
      #![crate_type="lib"]

      #[test]
      fn test() {
          assert_eq!(1 + 2, 3);
      }

      fn main() {
          println!("Hello, world");
      }
    EOF
    click_on("Build")

    within(:output, :stderr) do
      expect(page).to have_content 'function `main` is never used'
    end
  end

  scenario "when tests are present" do
    editor.set <<~EOF
      #[test]
      fn awesome() {}
    EOF
    click_on("Test")

    within(:output, :stdout) do
      expect(page).to have_content 'running 1 test'
      expect(page).to have_content 'test awesome ... ok'
      expect(page).to have_content 'test result: ok'
      expect(page).to have_content '1 passed'
      expect(page).to have_content '0 failed'
    end
  end

  scenario "when tests and a main method are present" do
    editor.set <<~EOF
      #[test]
      fn awesome() {}

      fn main() {
          println!("Running in main");
      }
    EOF
    click_on("Test")

    within(:output, :stdout) do
      expect(page).to have_content 'running 1 test'
      expect(page).to_not have_content 'Running in main'
    end
  end

  scenario "when a main method is present" do
    editor.set <<~EOF
      fn main() {
          println!("Running in main");
      }
    EOF
    click_on("Run")

    within(:output, :stdout) do
      expect(page).to have_content 'Running in main'
    end
  end

  scenario "when neither tests nor a main method are present" do
    editor.set <<~EOF
      fn arbitrary_code() {
          println!("I am code");
      }
    EOF
    click_on("Build")

    within(:output, :stderr) do
      expect(page).to have_content 'function `arbitrary_code` is never used'
    end
  end

  private

  def editor
    Editor.new(page)
  end
end
