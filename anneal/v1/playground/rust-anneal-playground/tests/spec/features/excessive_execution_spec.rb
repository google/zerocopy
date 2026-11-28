require 'json'

require 'spec_helper'
require 'support/editor'
require 'support/playground_actions'

RSpec.feature "Excessive executions", type: :feature, js: true do
  include PlaygroundActions

  before do
    visit "/?#{config_overrides}"
    editor.set(code)
  end

  scenario "a notification is shown" do
    within(:header) { click_on("Run") }
    within(:notification, text: 'will be automatically killed') do
      expect(page).to have_button 'Kill the process now'
      expect(page).to have_button 'Allow the process to continue'
    end
  end

  scenario "the process is automatically killed if nothing is done" do
    within(:header) { click_on("Run") }
    expect(page).to have_selector(:notification, text: 'will be automatically killed', wait: 2)
    expect(page).to_not have_selector(:notification, text: 'will be automatically killed', wait: 4)
    expect(page).to have_content("Exited with signal 9")
  end

  scenario "the process can continue running" do
    within(:header) { click_on("Run") }
    within(:notification, text: 'will be automatically killed') do
      click_on 'Allow the process to continue'
    end
    within(:output, :stdout) do
      expect(page).to have_content("Exited normally")
    end
  end

  def editor
    Editor.new(page)
  end

  def code
    <<~EOF
    use std::time::{Duration, Instant};

    fn main() {
        let start = Instant::now();
        while start.elapsed() < Duration::from_secs(5) {}
        println!("Exited normally");
    }
    EOF
  end

  def config_overrides
    config = {
      killGracePeriodS: 3.0,
      excessiveExecutionTimeS: 0.5,
    }

    "whte_rbt.obj=#{config.to_json}"
  end
end
