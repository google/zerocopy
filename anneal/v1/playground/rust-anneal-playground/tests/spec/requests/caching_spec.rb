require 'net/http'
require 'spec_helper'
require_relative './connection'

RSpec.feature "Caching headers are provided for assets ", type: :request do
  let(:index_uri) { URI(Capybara.app_host) }

  describe "the index page" do
    let(:one_day_s) { 24 * 60 * 60 }

    it "is cached for one day" do
      start_http(index_uri) do |http|
        request = Net::HTTP::Get.new(index_uri)
        response = http.request(request)

        expect(response['cache-control']).to match(/public.*max-age.*=.*#{one_day_s}/)
        expect(response['last-modified']).to_not be_nil
      end
    end
  end

  describe "an asset" do
    let(:index_body) { Net::HTTP.get(index_uri) }
    let(:index_page) { Capybara.string(index_body) }
    let(:asset_path) { index_page.first('head script', visible: false)[:src] }
    let(:asset_uri) { URI.join(index_uri, asset_path) }
    let(:one_year_s) { 365 * 24 * 60 * 60 }

    it 'is cached for one year' do
      start_http(asset_uri) do |http|
        request = Net::HTTP::Get.new(asset_uri)
        response = http.request(request)
        expect(response['cache-control']).to match(/public.*max-age.*=.*#{one_year_s}/)
        expect(response['last-modified']).to_not be_nil
      end
    end
  end
end
