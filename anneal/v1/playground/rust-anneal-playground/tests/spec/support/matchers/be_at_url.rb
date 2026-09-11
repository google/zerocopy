class NotAtUrlError < StandardError; end

RSpec::Matchers.define :be_at_url do |path, query = {}|
  match do |page|
    page.document.synchronize(nil, errors: [NotAtUrlError] ) do
      uri = URI::parse(page.current_url)
      raise NotAtUrlError unless uri.path == path

      query = query.map { |k, v| [k.to_s, Array(v).map(&:to_s)] }.to_h
      query_hash = CGI::parse(uri.query || '')
      raise NotAtUrlError unless query <= query_hash

      true
    end
  rescue NotAtUrlError
    false
  end

  failure_message do |page|
    "expected that #{page.current_url} would be #{path} with the query parameters #{query}"
  end
end
