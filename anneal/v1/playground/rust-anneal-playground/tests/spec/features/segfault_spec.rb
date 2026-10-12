require 'spec_helper'
require 'support/editor'
require 'support/playground_actions'

RSpec.feature "When the code triggers a signal", type: :feature, js: true do
  include PlaygroundActions

  before { visit '/' }

  scenario "when a crate type is provided" do
    code = <<~EOF
      fn main() {
          unsafe { *(0xDECAF_000 as *mut usize) = 1 };
      }
    EOF
    editor.set(code)

    click_on("Run")
    within(:output, :error) do
      expect(page).to have_content "signal 11"
      expect(page).to have_content "SIGSEGV"
      expect(page).to have_content "segmentation violation"
    end
  end

  def editor
    Editor.new(page)
  end
end
