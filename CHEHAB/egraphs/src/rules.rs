use crate::{
    cost::CostFn,
    drawEgraph::*,
    extractor::{Extractor},
    lp_extractor::{LpExtractor},
    fhe_rules::*,
    fhelang::{ConstantFold, Egraph,FheLang},
};
use egg::*;
use std::fs::File;
use std::io::{self,Write};
use std::path::Path;


pub fn run(lines: &Vec<&str>,timeout: u64,slot_count: usize,axiomatic: bool,enable_rotation: bool) -> Vec<(f64,RecExpr<FheLang>)> 
{
    let rules = rules(slot_count, axiomatic,enable_rotation);
    let mut init_eg: Egraph = Egraph::new(ConstantFold);
    init_eg.add(FheLang::Constant(0));
    let mut runner = Runner::default().with_egraph(init_eg) ;
 
    for line in lines {
        let expr: RecExpr<FheLang> = line.parse().unwrap();
        runner = runner.with_expr(&expr)
    } 
    runner = runner.with_node_limit(400000)
        .with_time_limit(std::time::Duration::from_secs(60))
        .with_iter_limit(10000)
        .run(&rules);
    eprintln!("Stopped after {} iterations, reason: {:?}",runner.iterations.len(),runner.stop_reason);
    runner.print_report();
    ///***********************************************************
    let iterations = format!("{:#?}", runner.iterations);
    let path = Path::new("iterations.txt");
    let mut file = File::create(path);
    file.expect("Problem in writing iterations ").write_all(iterations.as_bytes());
    ////**********************************************************
    let (eg, root) = (runner.egraph, runner.roots[0]);
    /*************************************************************/
    //convert_egraph_svg(egg_to_serialized_egraph::<FheLang,ConstantFold>(&eg));
    let mut extractor = Extractor::new(&eg, CostFn { egraph: &eg });
    /*********************************************************
    let mut  extractor = LpExtractor::new(&eg, CostFn { egraph: &eg });
    extractor.solve(root)
    **************************************************************/
    let mut solutions : Vec<(f64,RecExpr<FheLang>)> = vec![];
    for root in runner.roots{
        // we have to apply a rewrite each expression to replace the SumVec oprand 
        // with simple operands 
        solutions.push(extractor.find_best(root));
    }
    solutions
}

/**************************************************************************************************/
/**************************************************************************************************/
pub fn rules(slot_count: usize, axiomatic: bool,enable_rotation : bool) -> Vec<Rewrite<FheLang, ConstantFold>> {
    let mut rules: Vec<Rewrite<FheLang, ConstantFold>> = vec![];

    if axiomatic {
        rules.extend(axiomatic_rules(slot_count));
        //rules.extend(specific_rules(slot_count));
    } else {
        rules.extend(specific_rules(slot_count));
        //rules.extend(axiomatic_rules(slot_count));
    }
    if enable_rotation {
        rules.extend(rotation_rules(slot_count));
    }

    rules
}
