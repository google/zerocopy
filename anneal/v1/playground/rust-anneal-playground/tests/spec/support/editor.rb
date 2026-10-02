class Editor
  attr_reader :page
  def initialize(page)
    @page = page
  end

  def set(text)
    page.within('.ace_text-input', visible: :any) do
      page.execute_script <<~JS
        window.rustPlayground.setCode(#{text.to_json});
      JS
    end
  end

  def has_line?(text)
    page.has_css? '.ace_line', text: text
  end

  def has_highlighted_text?(text)
    page.within('.ace_text-input', visible: :any) do
      selected = page.evaluate_script <<~JS
        (() => {
          const editor = document.querySelector('.ace_editor').env.editor;
          return editor.getSelectedText();
        })()
      JS

      selected == text
    end
  end
end
