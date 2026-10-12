require 'spec_helper'
require 'support/editor'
require 'support/playground_actions'

RSpec.feature "Highlighting MIR output", type: :feature, js: true do
  include PlaygroundActions

  before do
    visit '/'
    editor.set(code)
    in_build_menu { click_on("MIR") }
  end

  scenario "error locations are links" do
    pending "This feature was removed in Rust 1.72, enabling it again is nightly-only"

    within(:output, :mir) do
      click_link('src/main.rs:4:14: 4:19', match: :first)
    end
    expect(editor).to have_highlighted_text('a + b')
  end

  def editor
    Editor.new(page)
  end

  def code
    <<~EOF
    fn main() {
        let a = 1;
        let b = 2;
        let _c = a + b;
    }
    EOF
  end
end
