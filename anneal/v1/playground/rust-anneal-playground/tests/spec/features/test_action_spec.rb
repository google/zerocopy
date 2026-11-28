require 'spec_helper'
require 'support/editor'
require 'support/playground_actions'

RSpec.feature "Testing the code", type: :feature, js: true do
  include PlaygroundActions

  before { visit '/' }

  scenario "when a crate type is provided" do
    code = <<~EOF
      #![crate_type = "proc-macro"]

      use proc_macro::TokenStream;

      #[proc_macro]
      pub fn demo(input: TokenStream) -> TokenStream {
          input
      }
    EOF
    editor.set(code)

    in_build_menu { click_on(build_button: "Test") }
    within(:output, :stdout) do
      expect(page).to have_content "running 0 tests"
    end
  end

  def editor
    Editor.new(page)
  end
end
