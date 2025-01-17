#![crate_name = "weather_client"]

/*!
 * Weather update client
 * Connects SUB socket to tcp://localhost:5556
 * Collects weather updates and find avg temp in zipcode
 */

use std::env;

fn atoi(s: &str) -> i64 {
    s.parse().unwrap()
}

fn main() {
    println!("Collecting updates from weather server...");

    let context = zmq2::Context::new();
    let subscriber = context.socket(zmq2::SUB).unwrap();
    assert!(subscriber.connect("tcp://localhost:5556").is_ok());

    let args: Vec<String> = env::args().collect();
    let filter = if args.len() > 1 { &args[1] } else { "10001" };
    assert!(subscriber.set_subscribe(filter.as_bytes()).is_ok());

    let mut total_temp = 0;

    for _ in 0..100 {
        let string = subscriber.recv_string(0).unwrap().unwrap();
        let chks: Vec<i64> = string.split(' ').map(atoi).collect();
        let (_zipcode, temperature, _relhumidity) = (chks[0], chks[1], chks[2]);
        total_temp += temperature;
    }

    println!(
        "Average temperature for zipcode '{}' was {}F",
        filter,
        (total_temp / 100)
    );
}
