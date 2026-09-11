require 'net/http'
require 'spec_helper'
require_relative './connection'

RSpec.feature "Cross-origin requests", :cors, type: :request do
  let(:evaluate_json_uri) { URI.join(Capybara.app_host, '/evaluate.json') }

  it "allows preflight requests for POSTing to evaluate.json" do
    start_http(evaluate_json_uri) do |http|
      request = Net::HTTP::Options.new(evaluate_json_uri)
      request['origin'] = 'https://rust-lang.org'
      request['access-control-request-headers'] = 'content-type'
      request['access-control-request-method'] = 'POST'

      response = http.request(request)

      expect(response['access-control-allow-headers']).to match(/content-type/i)
      expect(response['access-control-allow-methods'].split(',').map(&:strip)).to match_array([/GET/i, /POST/i])
      expect(response['access-control-allow-origin']).to eq('*').or eq('https://rust-lang.org')
      expect(response['access-control-max-age']).to eq('3600')
      expect(response['vary'].split(',').map(&:strip)).to match_array([/origin/i, /access-control-request-method/i, /access-control-request-headers/i])
    end
  end
end
