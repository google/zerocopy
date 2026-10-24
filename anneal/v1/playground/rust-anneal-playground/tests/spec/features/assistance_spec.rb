require 'spec_helper'
require 'support/editor'
require 'support/notifications'
require 'support/playground_actions'

RSpec.feature "Editor assistance for common code modifications", type: :feature, js: true do
  include PlaygroundActions

  before do
    visit '/'
    Notifications.new(page).close_all
  end

  scenario "building code without a main method offers adding one" do
    editor.set <<~EOF
      fn example() {}
    EOF
    click_on("Build")

    within(:output, :warning) do
      click_on("add a main function")
    end

    expect(editor).to have_line 'println!("Hello, world!")'
  end

  scenario "using an unstable feature offers adding the feature flag" do
    in_channel_menu { click_on("Nightly") }
    editor.set <<~EOF
      extern "avr-interrupt" fn dummy() {}
    EOF
    click_on("Build")

    within(:output, :stderr) do
      click_on("add `#![feature(abi_avr_interrupt)]`")
    end

    expect(editor).to have_line '#![feature(abi_avr_interrupt)]'
  end

  scenario "using a type that hasn't been imported offers importing it" do
    editor.set <<~EOF
      fn example(_: NonZeroU128) {}
    EOF
    click_on("Build")

    within(:output, :stderr) do
      click_on("use std::num::NonZeroU128;")
    end

    expect(editor).to have_line 'use std::num::NonZeroU128;'
  end

  scenario "triggering a panic offers enabling backtraces" do
    editor.set <<~EOF
      fn main() {
          panic!("Oops");
      }
    EOF
    click_on("Run")

    within(:output, :stderr) do
      click_on("run with `RUST_BACKTRACE=1` environment variable to display a backtrace")
    end

    within(:output, :stderr) do
      expect(page).to have_content("stack backtrace:")
    end
  end

  private

  def editor
    Editor.new(page)
  end
end
