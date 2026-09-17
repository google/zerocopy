require 'tmpdir'

RSpec.configure do |config|
  config.expect_with :rspec do |expectations|
    expectations.include_chain_clauses_in_custom_matcher_descriptions = true
  end

  config.mock_with :rspec do |mocks|
    mocks.verify_partial_doubles = true
  end

  config.disable_monkey_patching!

  # We aren't really testing Ruby code, so let's assume the Ruby code
  # of the tests is good enough
  config.warnings = false

  if config.files_to_run.one?
    config.default_formatter = 'doc'
  end

  config.example_status_persistence_file_path = "#{Dir.tmpdir()}/playground-test-failures"

  config.order = :random

  Kernel.srand config.seed
end

require 'capybara/rspec'
require 'capybara-screenshot/rspec'

PROTOCOL = ENV.fetch('PLAYGROUND_UI_PROTOCOL', 'http')
ADDRESS = ENV.fetch('PLAYGROUND_UI_ADDRESS', '127.0.0.1')
PORT = ENV.fetch('PLAYGROUND_UI_PORT', '5000')

Capybara.register_driver :firefox do |app|
  Capybara::Selenium::Driver.load_selenium

  capture_js_log = ENV.fetch('CAPTURE_JS_LOG', 'false').casecmp?('true')
  Selenium::WebDriver.logger.level = :debug if capture_js_log
  Selenium::WebDriver.logger.ignore(:clear_local_storage, :clear_session_storage)

  browser_options = ::Selenium::WebDriver::Firefox::Options.new
  browser_options.add_argument('-headless') if ENV.fetch('HEADLESS', 'true').casecmp?('true')
  browser_options.add_preference('devtools.console.stdout.content', true) if capture_js_log

  Capybara::Selenium::Driver.new(
    app,
    browser: :firefox,
    options: browser_options,
    clear_local_storage: true,
    clear_session_storage: true,
  )
end

Capybara.default_driver = Capybara.javascript_driver = :firefox
Capybara.app_host = "#{PROTOCOL}://#{ADDRESS}:#{PORT}"
Capybara.run_server = false
Capybara.default_max_wait_time = ENV.fetch('CAPYBARA_WAIT', 5).to_f
Capybara.automatic_label_click = true

Capybara::Screenshot.register_driver(:firefox) do |driver, path|
  driver.browser.save_screenshot(path)
end
Capybara.save_path = "./test-failures"

Capybara.modify_selector(:link_or_button) do
  expression_filter(:build_button) {|xpath, name| xpath[XPath.css('[data-test-id="button-menu-item__name"]').contains(name)] }
end

Capybara.add_selector(:header) do
  css { |_id| "[data-test-id = 'header']" }
end

Capybara.add_selector(:output) do
  css do |id|
    id_s = 'output'
    id_s += "-#{id}" if id
    "[data-test-id = '#{id_s}']"
  end
end

Capybara.add_selector(:stdin) do
  css { '[data-test-id = "stdin"]' }
end

Capybara.add_selector(:loader) do
  css { '[data-test-id = "loader"]' }
end

Capybara.add_selector(:notification) do
  css { '[data-test-id = "notification"]' }
end

Capybara.add_selector(:config_option) do
  xpath do |label|
    ".//div[span[contains(., '#{label}')]]"
  end
end

RSpec.configure do |config|
  config.after(:example, :js) do
    page.execute_script <<~JS
      (() => {
        if (window.rustPlayground) {
           window.rustPlayground.disableSyncChangesToStorage();
        }
      })()
    JS
  end
end
