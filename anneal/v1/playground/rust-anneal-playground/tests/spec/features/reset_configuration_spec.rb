require 'json'

require 'spec_helper'
require 'support/editor'
require 'support/playground_actions'

RSpec.feature "Resetting the configuration to defaults", type: :feature, js: true do
  include PlaygroundActions

  describe "after not visiting in a while" do
    before do
      visit "/"
      editor.set(code)

      sleep(0.002)
      visit "/?#{config_overrides}"
    end

    scenario "the default values are restored" do
      within(:notification) { click_on 'Reset all code and configuration' }

      expect(editor).to_not have_line(code)
      expect(editor).to have_line(some_default_code)
    end

    scenario "the current values are kept" do
      within(:notification) { click_on 'Keep the current code and configuration' }

      expect(editor).to have_line(code)
      expect(editor).to_not have_line(some_default_code)
    end

    def config_overrides
      config = {
        oldConfigurationThresholdS: 0.001,
      }

      "whte_rbt.obj=#{config.to_json}"
    end
  end

  describe "manually" do
    before do
      visit "/"
      editor.set(code)
    end

    scenario "the default values are restored" do
      in_config_menu { click_on 'Reset all code and configuration to default values' }
      within(:notification) { click_on 'Reset all code and configuration' }

      expect(editor).to_not have_line(code)
      expect(editor).to have_line(some_default_code)
    end

    scenario "the current values are kept" do
      in_config_menu { click_on 'Reset all code and configuration to default values' }
      within(:notification) { click_on 'Keep the current code and configuration' }

      expect(editor).to have_line(code)
      expect(editor).to_not have_line(some_default_code)
    end
  end

  def editor
    Editor.new(page)
  end

  def code
    'This is my old code'
  end

  def some_default_code
    'Hello, world!'
  end
end
