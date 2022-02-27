mod formula;
mod globals;
mod parse;

use clap::Parser;
use std::fs;

#[derive(Parser)]
struct Args {
    input: String,
}

fn main() {
    let args = Args::parse();
    let text = fs::read_to_string(args.input).expect("Could not read file");

    let (g,f) = parse::parse(&text).expect("Could not parse file");
    println!("{}", f.to_string(&g));
}
