class Notifications
  attr_reader :page
  def initialize(page)
    @page = page
  end

  def close_all
    page.all(:notification).each do |notification|
      page.within(notification) do
        page.click_on('dismiss notification')
      end
    end
  end
end
