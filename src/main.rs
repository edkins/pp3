mod formula;
mod globals;
mod parse;
mod script;

use clap::Parser;
use std::fs;

#[derive(Parser)]
struct Args {
    input: String,
}

fn main() {
    let args = Args::parse();
    let text = fs::read_to_string(args.input).expect("Could not read file");

    let (g, s) = parse::parse(&text).expect("Could not parse file");
    s.print(&g, 0);
}
