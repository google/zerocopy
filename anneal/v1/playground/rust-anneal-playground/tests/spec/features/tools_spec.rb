# coding: utf-8

require 'spec_helper'
require 'support/editor'
require 'support/playground_actions'

RSpec.feature "Using third-party Rust tools", type: :feature, js: true do
  include PlaygroundActions

  before { visit '/' }

  scenario "formatting code" do
    editor.set 'fn main() { [1,2,3,4]; }'
    in_tools_menu { click_on("Rustfmt") }

    expect(editor).to have_line '[1, 2, 3, 4];'
  end

  scenario "linting code with Clippy" do
    editor.set code_with_lint_warnings
    in_tools_menu { click_on("Clippy") }

    within(:output, :stderr) do
      expect(page).to have_content 'deny(clippy::eq_op)'
      expect(page).to have_content 'warn(clippy::zero_divided_by_zero)'
    end
  end

  def code_with_lint_warnings
    <<~EOF
    use itertools::Itertools;

    fn example() {
        let a = 0.0 / 0.0;
        println!("NaN is {}", a);
    }
    EOF
  end

  scenario "sanitize code with Miri" do
    editor.set code_with_undefined_behavior
    in_tools_menu { click_on("Miri") }

    within(:output, :stderr) do
      expect(page).to have_content %r{reading memory at alloc.*, but memory is uninitialized at .*, and this operation requires initialized memory}, wait: 10
    end
  end

  def code_with_undefined_behavior
    <<~EOF
    fn main() {
        unsafe { core::mem::MaybeUninit::<u8>::uninit().assume_init() };
    }
    EOF
  end

  scenario "configure Miri for tree borrows" do
    editor.set code_valid_under_tree_borrows_but_not_stacked_borrows
    in_advanced_options_menu { choose("tree") }
    in_tools_menu { click_on("Miri") }

    within(:output, :stdout) do
      expect(page).to have_content %r{[1, 2]}, wait: 10
    end

    within(:output, :stderr) do
      expect(page).to_not have_content %r{Undefined Behavior}
    end
  end

  def code_valid_under_tree_borrows_but_not_stacked_borrows
    <<~EOF
    fn main() {
        let val = [1u8, 2];
        let ptr = &val[0] as *const u8;
        let _val = unsafe { *ptr.add(1) };
    }
    EOF
  end

  scenario "expand macros with the nightly compiler" do
    editor.set code_that_uses_macros
    in_tools_menu { click_on("Expand macros") }

    within(:output, :stdout) do
      # First-party
      expect(page).to have_content('::std::io::_print')

      # Third-party procedural macro
      expect(page).to have_content('block_on(body)')

      # User-specified declarative macro
      expect(page).to have_content('fn created_by_macro() -> i32 { 42 }')
    end
  end

  def code_that_uses_macros
    <<~EOF
    macro_rules! demo {
        ($name:ident) => {
            fn $name() -> i32 { 42 }
        }
    }

    demo!(created_by_macro);

    #[tokio::main]
    async fn example() {
        println!("a value: {}", created_by_macro());
    }
    EOF
  end

  def editor
    Editor.new(page)
  end
end
