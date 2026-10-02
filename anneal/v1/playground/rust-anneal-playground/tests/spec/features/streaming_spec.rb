require 'spec_helper'
require 'support/editor'
require 'support/playground_actions'

RSpec.feature "Streaming interaction using WebSockets", type: :feature, js: true do
  include PlaygroundActions

  before do
    visit '/?features=true'
  end

  scenario "output comes when it is available" do
    editor.set <<~EOF
      use std::time::Duration;

      fn main() {
          println!("First");
          std::thread::sleep(Duration::from_millis(750));
          println!("Second");
          std::thread::sleep(Duration::from_millis(750));
          println!("Third");
      }
    EOF

    click_on("Run")

    within(:output, :stdout) do
      expect(page).to have_content 'First'
      expect(page).to_not have_content 'Second'

      expect(page).to have_content 'Second', wait: 0.8
      expect(page).to_not have_content 'Third'

      expect(page).to have_content 'Third', wait: 0.8
    end
  end

  scenario "input can be supplied" do
    editor.set <<~EOF
      fn main() {
          println!("Enter some text!");
          let mut input = String::new();
          std::io::stdin().read_line(&mut input).expect("Unable to read input");
          println!("You entered >>>{input:?}<<<");
      }
    EOF

    click_on("Run")

    within(:output, :stdout) do
      expect(page).to have_content 'Enter some text'
      expect(page).to_not have_content 'You entered'
    end

    within(:stdin) do
      fill_in 'content', with: 'An automated test'
      click_on 'Send'
    end

    within(:output, :stdout) do
      expect(page).to have_content 'Enter some text'
      expect(page).to have_content 'You entered >>>"An automated test\n"<<<'
    end
  end

  scenario "input can be closed" do
    editor.set <<~EOF
      fn main() {
          let mut input = String::new();
          while std::io::stdin().read_line(&mut input).unwrap() != 0 {
              println!("You entered >>>{input:?}<<<");
              input.clear();
          }
          println!("All done");
      }
    EOF

    click_on("Run")

    within(:stdin) do
      click_on 'Execution control'
      click_on 'Close stdin'
    end

    within(:output, :stdout) do
      expect(page).to have_content 'All done'
    end
  end

  scenario "The process can be killed" do
    editor.set <<~EOF
      fn main() {
          loop {
              std::thread::sleep(std::time::Duration::from_secs(1));
          }
      }
    EOF

    click_on("Run")

    within(:stdin) do
      click_on 'Execution control'
      click_on 'Kill process'
    end

    within(:output, :error) do
      expect(page).to have_content 'SIGKILL'
    end
  end

  scenario "The process can be killed after stdin is closed" do
    editor.set <<~EOF
      fn main() {
          loop {
              std::thread::sleep(std::time::Duration::from_secs(1));
          }
      }
    EOF

    click_on("Run")

    within(:stdin) do
      click_on 'Execution control'
      click_on 'Close stdin'
      click_on 'Execution control'
      click_on 'Kill process'
    end

    within(:output, :error) do
      expect(page).to have_content 'SIGKILL'
    end
  end

  def editor
    Editor.new(page)
  end
end
