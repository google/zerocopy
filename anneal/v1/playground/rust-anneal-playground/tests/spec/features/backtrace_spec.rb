require 'spec_helper'
require 'support/editor'
require 'support/playground_actions'

RSpec.feature "A backtrace is shown for certain errors", type: :feature, js: true do
  include PlaygroundActions

  before do
    visit '/'
    editor.set(code)
  end

  context "backtraces are enabled" do
    before do
      in_advanced_options_menu { within(:config_option, 'Backtrace') { choose 'On' } }
      within(:header) { click_on("Run") }
    end

    scenario "a backtrace is shown" do
      within(:output, :stderr) do
        expect(page).to have_content 'stack backtrace:'
        expect(page).to have_content 'rust_begin_unwind'
      end
    end

    scenario "filenames link to that line of code" do
      within(:output, :stderr) do
        expect(page).to have_link('main.rs:2')
        expect(page).to have_link('main.rs:6')
      end
    end
  end

  context "backtraces are disabled" do
    before do
      within(:header) { click_on("Run") }
    end

    scenario "the backtrace suggestion is a link" do
      within(:output, :stderr) do
        expect(page).to have_link(text: /Run with .* a backtrace/i)
      end
    end
  end

  def editor
    Editor.new(page)
  end

  def code
    <<~EOF
    fn trigger_the_problem() {
        None::<u8>.unwrap();
    }

    fn main() {
        trigger_the_problem()
    }
    EOF
  end
end
