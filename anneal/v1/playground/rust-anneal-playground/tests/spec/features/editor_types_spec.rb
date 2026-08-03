require 'spec_helper'
require 'support/playground_actions'

RSpec.feature "Editing in different editors", type: :feature, js: true do
  include PlaygroundActions

  before { visit '/' }

  scenario "using the simple editor" do
    in_config_menu { select("simple") }

    fill_in('editor-simple', with: simple_editor_code)

    click_on("Run")

    within(:output, :stdout) do
      expect(page).to have_content 'simple editor'
    end
  end

  def simple_editor_code
    <<~EOF
    fn main() {
        println!("Using the simple editor");
    }
    EOF
  end

  scenario "using the Monaco editor" do
    in_config_menu { select("monaco") }

    editor = page.find('.monaco-editor')

    # Click on the last line as that will replace the entire content
    editor.find('.view-line:last-child').click
    t = editor.find('textarea', visible: false)
    t.set(monaco_editor_code, clear: :backspace)

    click_on("Run")

    within(:output, :stdout) do
      expect(page).to have_content 'Monaco editor'
    end
  end

  # Missing indentation and closing curly braces as those are auto-inserted
  def monaco_editor_code
    <<~EOF
    fn main() {
    println!("Using the Monaco editor");
    EOF
  end
end
