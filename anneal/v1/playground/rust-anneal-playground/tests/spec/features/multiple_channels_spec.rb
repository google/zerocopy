require 'spec_helper'
require 'support/editor'
require 'support/playground_actions'

RSpec.feature "Multiple Rust versions", type: :feature, js: true do
  include PlaygroundActions

  before do
    visit '/'
    editor.set(version_code)
  end

  scenario "using stable Rust" do
    in_channel_menu { click_on("Stable") }
    click_on("Run")

    within(:output, :stdout) do
      expect(page).to have_content 'rustc'
      expect(page).to_not have_content 'beta'
      expect(page).to_not have_content 'nightly'
    end
  end

  scenario "using beta Rust" do
    in_channel_menu { click_on("Beta") }
    click_on("Run")

    within(:output, :stdout) do
      expect(page).to have_content 'rustc'
      expect(page).to have_content 'beta'
      expect(page).to_not have_content 'nightly'
    end
  end

  scenario "using nightly Rust" do
    in_channel_menu { click_on("Nightly") }
    click_on("Run")

    within(:output, :stdout) do
      expect(page).to have_content 'rustc'
      expect(page).to_not have_content 'beta'
      expect(page).to have_content 'nightly'
    end
  end

  def editor
    Editor.new(page)
  end

  def version_code
    <<~EOF
    use std::process::Command;

    fn main() {
        let output = Command::new("rustc").arg("--version").output().unwrap();
        let output = String::from_utf8(output.stdout).unwrap();
        println!("{}", output);
    }
    EOF
  end
end
