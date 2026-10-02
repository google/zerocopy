def start_http(uri, &block)
  http = Net::HTTP.new(uri.host, uri.port)
  http.use_ssl = uri.scheme == 'https'

  http.start(&block)
end
