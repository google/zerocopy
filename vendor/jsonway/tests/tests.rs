extern crate jsonway;

#[derive(Debug)]
enum Side {
    Light,
    Dark
}

struct Jedi {
    name: String,
    side: Side
}

fn jedi_array() -> Vec<Jedi> {
    vec![
        Jedi { name: "Saes Rrogon".to_string(), side: Side::Dark },
        Jedi { name: "Qui-Gon Jinn".to_string(), side: Side::Light },
        Jedi { name: "Obi-Wan Kenobi".to_string(), side: Side::Light }
    ]
}

#[test]
fn simple_array_of_objects() {
    let jedi_array = jedi_array();

    let json = jsonway::array(|json| {
        json.objects(jedi_array.iter(), |jedi, json| {
            match jedi.side {
                Side::Light => {
                    json.set("name".to_string(), jedi.name.to_string());
                    json.set("side".to_string(), format!("{:?}", jedi.side));
                },
                Side::Dark => json.skip()
            }
        })
    }).unwrap();

    let array = json.as_array().unwrap();

    assert_eq!(array.len(), 2);
}

#[test]
fn simple_array_of_arrays() {
    let jedi_array = jedi_array();

    let json = jsonway::array(|json| {
        json.objects(jedi_array.iter(), |jedi, json| {
            match jedi.side {
                Side::Light => {
                    json.set("name".to_string(), jedi.name.to_string());
                    json.set("side".to_string(), format!("{:?}", jedi.side));
                },
                Side::Dark => json.skip()
            }
        })
    }).unwrap();

    let array = json.as_array().unwrap();
    assert_eq!(array.len(), 2);
}