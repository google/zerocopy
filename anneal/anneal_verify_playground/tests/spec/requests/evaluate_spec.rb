# coding: utf-8

require 'net/http'
require 'spec_helper'
require_relative './connection'

RSpec.feature "evaluate.json endpoint", type: :request do
  let(:evaluate_json_uri) { URI.join(Capybara.app_host, '/evaluate.json') }

  let(:code) {
    <<~EOF
    fn main() {
        let greetings = ["Hello", "Hola", "Bonjour",
                         "Ciao", "こんにちは", "안녕하세요",
                         "Cześć", "Olá", "Здравствуйте",
                         "Chào bạn", "您好", "Hallo",
                         "Hej", "Ahoj", "سلام","สวัสดี"];

        for (num, greeting) in greetings.iter().enumerate() {
            print!("{} : ", greeting);
            match num {
                0 =>  println!("This code is editable and runnable!"),
                1 =>  println!("¡Este código es editable y ejecutable!"),
                2 =>  println!("Ce code est modifiable et exécutable !"),
                3 =>  println!("Questo codice è modificabile ed eseguibile!"),
                4 =>  println!("このコードは編集して実行出来ます！"),
                5 =>  println!("여기에서 코드를 수정하고 실행할 수 있습니다!"),
                6 =>  println!("Ten kod można edytować oraz uruchomić!"),
                7 =>  println!("Este código é editável e executável!"),
                8 =>  println!("Этот код можно отредактировать и запустить!"),
                9 =>  println!("Bạn có thể edit và run code trực tiếp!"),
                10 => println!("这段代码是可以编辑并且能够运行的！"),
                11 => println!("Dieser Code kann bearbeitet und ausgeführt werden!"),
                12 => println!("Den här koden kan redigeras och köras!"),
                13 => println!("Tento kód můžete upravit a spustit"),
                14 => println!("این کد قابلیت ویرایش و اجرا دارد!"),
                15 => println!("โค้ดนี้สามารถแก้ไขได้และรันได้"),
                _ =>  {},
            }
        }
    }
    EOF
  }
  let(:request) {{ 'version': 'beta', 'optimize': '0', 'code': code } }
  let(:body) { JSON.generate(request) }

  it "allows evaluating compilation requests from the Rust home page" do
    start_http(evaluate_json_uri) do |http|
      request = Net::HTTP::Post.new(evaluate_json_uri)
      request.body = body
      request['Content-Type'] = 'application/json'

      response = http.request(request)

      body = response.body.force_encoding('UTF-8')
      expect(body).to match('Hello : This code is editable and runnable')
      expect(body).to match('こんにちは : このコードは編集して実行出来ます')
      expect(body).to match('สวัสดี : โค้ดนี้สามารถแก้ไขได้และรันได้')
    end
  end
end
