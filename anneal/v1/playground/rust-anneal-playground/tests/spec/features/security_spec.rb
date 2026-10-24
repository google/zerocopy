require 'spec_helper'
require 'support/editor'
require 'support/playground_actions'

RSpec.feature "Security concerns", type: :feature, js: true do
  include PlaygroundActions

  before do
    visit '/'
    editor.set(code)
  end

  scenario "a notice is present for filesystem snoopers" do
    within(:header) { click_on("Run") }
    within(:output, :stdout) do
      expect(page).to have_content 'www.rust-lang.org/policies/security'
    end
  end

  def editor
    Editor.new(page)
  end

  def code
    <<~EOF
    fn main() {
        println!("{}", std::fs::read_to_string("/etc/passwd").unwrap());
    }
    EOF
  end
end
