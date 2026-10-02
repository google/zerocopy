require 'spec_helper'
require 'support/editor'
require 'support/matchers/be_at_url'
require 'support/playground_actions'

RSpec.feature "Navigating between pages", type: :feature, js: true do
  include PlaygroundActions

  # This is kind of a test of the router library too, so if that ever
  # gets extracted, a chunk of these tests can be removed.

  scenario "Mode and channel buttons update the URL" do
    visit '/'
    expect(page).to have_content('RUN')

    editor.set("dummy")
    expect(page).to be_at_url('/')

    in_mode_menu { click_on('Release') }
    expect(page).to be_at_url('/', version: 'stable', mode: 'release')

    go_back
    expect(page).to be_at_url('/')

    in_mode_menu { click_on('Release') }
    in_channel_menu { click_on('Beta') }
    expect(page).to be_at_url('/', version: 'beta', mode: 'release')

    go_back
    expect(page).to be_at_url('/')
  end

  scenario "Navigating to help changes the URL" do
    visit '/'
    expect(page).to have_content('RUN')

    click_on 'View help'
    expect(page).to be_at_url('/help')
    expect(page).to have_content('The Rust Playground')

    go_back
    expect(page).to be_at_url('/')
    expect(page).to have_content('RUN')

    go_forward
    expect(page).to be_at_url('/help')
    expect(page).to have_content('The Rust Playground')

    click_on "Return to the playground"
    expect(page).to be_at_url('/')
    expect(page).to have_content('RUN')
  end

  scenario "Navigating from help changes the URL" do
    visit '/help'
    expect(page).to have_content('The Rust Playground')

    click_on "Return to the playground"
    expect(page).to be_at_url('/')
    expect(page).to have_content('RUN')
  end

  def editor
    Editor.new(page)
  end

  # It probably would be worth figuring out why
  # `page.go_{back,forward}` doesn't work... :-(
  # Maybe https://github.com/teampoltergeist/poltergeist/issues/624
  def go_back
    page.execute_script('window.history.go(-1);')
  end

  def go_forward
    page.execute_script('window.history.go(1);')
  end
end
