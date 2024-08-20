use egg::*;
extern crate clap;
use clap::{App, Arg};
use egraphslib::rules;
use std::fs::File;
use std::io::{self,Write};
use std::path::Path;
fn main() {
    let matches = App::new("Rewriter")
        .arg(
            Arg::with_name("INPUT")
                .help("Sets the input file")
                .required(true)
                .index(1),
        )
        .arg(
            Arg::with_name("slot_count")
                .help("Sets the slot_count")
                .required(true)
                .index(2),
        )
        .arg(
            Arg::with_name("axiomatic")
                .help("If true use axiomatic rules otherwise use specific rules")
                .required(true)
                .index(3),
        )
        .get_matches();

    use std::{env, fs};
    let path = matches.value_of("INPUT").unwrap();

    let slot_count: usize = matches
        .value_of("slot_count")
        .unwrap()
        .parse()
        .expect("Number must be a valid usize");
    let axiomatic_int: usize = matches
        .value_of("axiomatic")
        .unwrap()
        .parse()
        .expect("axiomatic must be a valid usize");
    let axiomatic = axiomatic_int == 1;
    let timeout = env::var("TIMEOUT")
        .ok()
        .and_then(|t| t.parse::<u64>().ok())
        .unwrap_or(300);
    let prog_str = fs::read_to_string(path).expect("Failed to read the input file.");
    let lines: Vec<&str> = prog_str.lines().collect();
    /* for line in lines {
        expressions.push(line.parse().unwrap());
    } */
    //let prog = prog_str.parse().unwrap();
    // Run rewriter    
    /************* 
    for i in 1..=2 { // 1..=10 creates an inclusive range from 1 to 10
        if i==2 {
            enable_rotation = false ;
        }
        let (cost,prog) = rules::run(&prog, timeout, slot_count, axiomatic,enable_rotation);
        println!("cost of the solution : {}",cost);
    } **********/
    let mut enable_rotation : bool = true ;
    let solutions = rules::run(&lines, timeout, slot_count, axiomatic,enable_rotation);
    let path = Path::new("../simplified_expression.txt");
    let mut file = File::create(path);
    let mut info : String = String::from("");
    for (cost,prog) in solutions {
        println!("cost of the solution : {}",cost);
        let binding = prog.to_string();
        let best_str: &str = binding.as_ref();
        let processed_best = best_str.replace("(", "( ").replace(")", " )");
        info = info + &processed_best +"\n" ;  
    }
    file.expect("Problem in writing file").write_all(info.as_bytes());

}
