# coding: utf-8

module PlaygroundActions
  def in_build_menu(&block)
    in_menu("Select what to build", &block)
  end

  def in_mode_menu(&block)
    in_menu("Mode — Choose the optimization level", &block)
  end

  def in_channel_menu(&block)
    in_menu("Channel — Choose the Rust version", &block)
  end

  def in_advanced_options_menu(&block)
    in_menu("Advanced compilation flags", &block)
  end

  def in_tools_menu(&block)
    in_menu("Tools", &block)
  end

  def in_config_menu(&block)
    in_menu("Config", close: true, &block)
  end

  private

  def in_menu(button_locator, close: false)
    click_on(button_locator)
    yield
  ensure
    click_on(button_locator) if close
  end
end
