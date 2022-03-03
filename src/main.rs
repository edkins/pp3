mod axioms;
mod formula;
mod globals;
mod parse;
mod proof;
mod script;
mod tactics;

use crate::proof::ProofContext;
use clap::Parser;
use std::fs;

#[derive(Parser)]
struct Args {
    input: String,
}

fn main() {
    let args = Args::parse();
    let text = fs::read_to_string(args.input).expect("Could not read file");

    let (mut g, s) = parse::parse(&text).expect("Could not parse file");
    s.print(&g, 0);

    let mut proof_context = ProofContext::new(&g);
    proof_context.process(&mut g, &s).expect("Proof failed");
    proof_context.print(&g);
}
