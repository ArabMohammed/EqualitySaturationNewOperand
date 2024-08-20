use egg::*;
use std::{
    cmp::Ordering,
    collections::{HashMap, HashSet},
};
use coin_cbc::{Col, Model, Sense};
use crate::config::*;
use crate::cost;
use crate::fhelang ;




pub struct LpExtractor<'a, CF: cost::CostFunction<L>, L: Language, N: Analysis<L>> {
    cost_function: CF,
    costs: HashMap<Id, (f64, f64, f64, L)>,
    node_costs : HashMap<L, (f64, f64, f64)>,
    egraph: &'a egg::EGraph<L, N>,
    model: Model,
    vars: HashMap<Id, ClassVars>,
}
/*******************************************************************/
struct ClassVars {
    active: Col,
    order: Col,
    nodes: Vec<Col>,
}
/**************************************************************/

impl<'a, CF, L, N> LpExtractor<'a, CF, L, N>
where
    CF: cost::CostFunction<L>,
    L: Language,
    N: Analysis<L>,
{
    pub fn new(egraph: &'a EGraph<L, N>, cost_function: CF) -> Self {
        let costs = HashMap::default();
        let node_costs = HashMap::default();
        let mut model = Model::default();
        let vars = HashMap::default();
        let mut extractor = LpExtractor {
            costs,
            node_costs,
            egraph,
            cost_function,
            model,
            vars
        };
        extractor.find_costs();
        extractor.prepare_model();    
        extractor
    }

    /********************************************************************************************/
    /*******************************************************************************************/
    
    fn prepare_model(&mut self){
        let max_order = self.egraph.total_number_of_nodes() as f64 ;
        let mut model = Model::default();
        let vars: HashMap<Id, ClassVars> = self.egraph
            .classes()
            .map(|class| {
                let cvars = ClassVars {
                    active: model.add_binary(),
                    order: model.add_col(),
                    nodes: class.nodes.iter().map(|_| model.add_binary()).collect(),
                };
                // Sets the objective coefficient of the given variable.
                model.set_col_upper(cvars.order, max_order);
                (class.id, cvars)
            })
            .collect();
        let mut cycles: HashSet<(Id, usize)> = Default::default();
        find_cycles(self.egraph,|id, i| {
            cycles.insert((id, i));
        });
        for (&id, class) in &vars {
            // class active == some node active
            // sum(for node_active in class) == class_active
            let row = model.add_row();
            model.set_row_equal(row, 0.0);
            model.set_weight(row, class.active, -1.0);
            for &node_active in &class.nodes {
                model.set_weight(row, node_active, 1.0);
            }

            for (i, (node, &node_active)) in self.egraph[id].iter().zip(&class.nodes).enumerate() {
                if cycles.contains(&(id, i)) {
                    model.set_col_upper(node_active, 0.0);
                    model.set_col_lower(node_active, 0.0);
                    continue;
                }

                for child in node.children() {
                    let child_active = vars[child].active;
                    // node active implies child active, encoded as:
                    //   node_active <= child_active
                    //   node_active - child_active <= 0
                    let row = model.add_row();
                    model.set_row_upper(row, 0.0);
                    model.set_weight(row, node_active, 1.0);
                    model.set_weight(row, child_active, -1.0);
                }
            }
        }
        model.set_obj_sense(Sense::Minimize);
        for class in self.egraph.classes() {
            for (node, &node_active) in class.iter().zip(&vars[&class.id].nodes) {
                let cost = self.node_costs.get(&node) ;
                let mut value : f64 = 0.0 ;
                match cost {
                    Some(node_cost) => {value = ALPHA * node_cost.0 + BETA * node_cost.1 + GAMMA * node_cost.2},
                    None => (),
                }
                model.set_obj_coeff(node_active, value);
            }
        }
        self.model = model ;
        self.vars = vars;
    }
   
    /****************************************************************************************************/
    /****************************************************************************************************/

    fn node_total_cost(
        &mut self,
        node: &L,
        map: &mut HashMap<Id, HashSet<Id>>,
    ) -> Option<(f64, f64, f64)> {
        let eg = &self.egraph;

        // Check if all children have their costs calculated
        let has_cost = |&id| self.costs.contains_key(&eg.find(id));
        if node.children().iter().all(has_cost) {
            let costs = &self.costs;

            // Get the cost of a child e-class
            let depth_f = |id| costs[&eg.find(id)].0.clone();
            let mul_depth_f = |id| costs[&eg.find(id)].1.clone();
            let op_costs_f = |id| costs[&eg.find(id)].2.clone();

            // Calculate the initial cost of the node using the cost function
            let depth = self.cost_function.depth(&node, depth_f);
            let mul_depth = self.cost_function.mul_depth(&node, mul_depth_f);
            let mut op_costs = self.cost_function.op_costs(&node, op_costs_f);

            // Handle nodes with one child
            if node.children().len() == 1 {
                return Some((depth, mul_depth, op_costs));
            }

            // Handle nodes with two children
            if node.children().len() == 2 {
                // Get the operation of the current node
                let op = node.display_op().to_string();

                // Check if the operation is multiplication
                if op == "*" {
                    // Get the first and second child nodes
                    let child_0 = node.children().iter().nth(0).unwrap();
                    let child_1 = node.children().iter().nth(1).unwrap();

                    // Find the corresponding enodes for the children in the e-graph
                    let child_0_enode = costs[&eg.find(*child_0)].3.clone();
                    let child_1_enode = costs[&eg.find(*child_1)].3.clone();

                    // Get the operations of the child enodes
                    let op_child_0 = child_0_enode.display_op().to_string();
                    let op_child_1 = child_1_enode.display_op().to_string();

                    // Determine if the operation is constant
                    let is_constant_op = |op: &str| match op {
                        "+" | "<<" | "*" | "-" | "square" => false,
                        _ => true,
                    };

                    // Check if one of the children is constant
                    let is_constant = is_constant_op(&op_child_0) || is_constant_op(&op_child_1);

                    // Apply cost adjustment if one of the children is constant
                    if is_constant {
                        op_costs -= 99.0 * OP;
                    }
                }

                let child_0 = node.children().iter().nth(0).unwrap();
                let child_1 = node.children().iter().nth(1).unwrap();

                // If both children are the same, subtract the cost of one child
                if child_0 == child_1 {
                    return Some((depth, mul_depth, op_costs - costs[&eg.find(*child_1)].2));
                }

                let sub_classes_class_0 = map.get(&child_0).unwrap();
                let sub_classes_class_1 = map.get(&child_1).unwrap();

                // If one child e-class belongs to the hierarchy of the other, subtract the cost of the contained e-class
                if sub_classes_class_0.contains(child_1) {
                    return Some((depth, mul_depth, op_costs - costs[&eg.find(*child_1)].2));
                }
                if sub_classes_class_1.contains(child_0) {
                    return Some((depth, mul_depth, op_costs - costs[&eg.find(*child_0)].2));
                }

                // Calculate the intersection of both hierarchies and subtract the cost of the shared operations
                let shared_sub_classes = sub_classes_class_0
                    .intersection(sub_classes_class_1)
                    .cloned()
                    .collect::<HashSet<Id>>();
                // reduce the cost of shared e-classes from the op_costs 
                for id in shared_sub_classes {
                    let node = costs[&eg.find(id)].3.clone();

                    // Define costs for different operations

                    let op = node.display_op().to_string();
                    let op_cost: f64 = match op.as_str() {
                        "+" | "-" | "neg" => OP,
                        "<<" => OP * 50.0,
                        "square" => OP * 80.0,
                        "*" => OP * 100.0,
                        _ => LITERAL,
                    };

                    op_costs -= op_cost;
                }
                /*********************************************/
                self.node_costs.insert(node.clone(), (depth, mul_depth, op_costs));
                /********************************************/
                return Some((depth, mul_depth, op_costs));
            } else {
                // If the node has more than two children, return the calculated cost
                return Some((depth, mul_depth, op_costs));
            }
        }

        // Return None if the cost cannot be calculated
        None
    }

    /// Calculates the costs of all e-classes in an e-graph.
    ///
    /// This function iterates through all e-classes in the e-graph and calculates the cost for each one using
    ///  `make_pass` function. The cost calculation for each e-class considers the costs
    /// of its e-nodes. If the cost of an e-class is calculated for the first time, it is set along with the
    /// corresponding best e-node. The function continues iterating until no changes are detected, ensuring that
    /// all dependent e-classes have their costs updated appropriately.
    ///
    /// Steps:
    /// 1. Initialize a flag (`did_something`) to track if any costs were updated.
    /// 2. Initialize a map (`sub_classes`) to store sub-classes for each e-class.
    /// 3. Iterate over all e-classes and calculate their costs.
    /// 4. If the cost of an e-class is calculated for the first time, update the cost and set the flag to `true`.
    /// 5. If the cost of an e-class is already calculated, update it only if there is a change and set the flag accordingly.
    /// 6. Repeat until no more changes are detected.
    /// 7. Log an error message for any e-class that failed to compute a cost.
    ///
    /// Parameters:
    /// - `&mut self`: Mutable reference to the current instance.
    ///
    /// Returns:
    /// - None
    

    /**************************************************************************/
    /**************************************************************************/
    
    fn find_costs(&mut self) {
        let mut did_something = true;
        // store the eclass ids of the desecndants e-classes of an eclass
        let mut sub_classes: HashMap<Id, HashSet<Id>> = HashMap::new();
        // Iterate until no more changes are detected
        while did_something {
            did_something = false;

            for class in self.egraph.classes() {
                // calculate the cost of an eclass 
                let pass = self.make_pass(&mut sub_classes, class);
                match (self.costs.get(&class.id), pass) {
                    // If the cost is calculated for the first time
                    (None, Some(new)) => {
                        self.costs.insert(class.id, new);
                        did_something = true;
                    }
                    // If the cost is already calculated and there is a change
                    (Some(old), Some(new)) => {
                        if ALPHA * new.0 + BETA * new.1 + GAMMA * new.2
                            != ALPHA * old.0 + BETA * old.1 + GAMMA * old.2
                        {
                            did_something = true;
                        }
                        self.costs.insert(class.id, new);
                    }
                    _ => (),
                }
            }
        }

        // Log an error message for any e-class that failed to compute a cost
        for class in self.egraph.classes() {
            if !self.costs.contains_key(&class.id) {
                eprintln!(
                    "Failed to compute cost for eclass {}: {:?}",
                    class.id, class.nodes
                )
            }
        }
    }
    
    /**************************************************************************/
    /**************************************************************************/

    fn cmp(a: &Option<(f64, f64, f64)>, b: &Option<(f64, f64, f64)>) -> Ordering {
        match (a, b) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Greater,
            (Some(_), None) => Ordering::Less,
            (Some(a), Some(b)) => {
                let x = ALPHA * a.0 + BETA * a.1 + GAMMA * a.2;
                let y = ALPHA * b.0 + BETA * b.1 + GAMMA * b.2;
                x.partial_cmp(&y).unwrap()
            }
        }
    }
    
    /**************************************************************************/
    /**************************************************************************/

    fn make_pass(
        &mut self,
        sub_classes: &mut HashMap<Id, HashSet<Id>>,
        eclass: &EClass<L, N::Data>,
    ) -> Option<(f64, f64, f64, L)> {
        let mut node_sub_classes: HashSet<Id> = HashSet::new();
        let nodes = eclass.nodes.clone();

        // Find the e-node with the minimum cost
        let (cost, node) = nodes
            .iter()
            .map(|n| (self.node_total_cost(n, sub_classes), n))// claculate the cost of an enode
            .min_by(|a, b| Self::cmp(&a.0, &b.0))
            .unwrap_or_else(|| panic!("Can't extract, eclass is empty: {:#?}", eclass));

        match cost {
            // If no valid cost could be calculated, return None
            None => None,

            // If a valid cost is found
            Some(cost) => {
                // Update the hierarchy for the e-class based on the best e-node
                node.for_each(|id| {
                    node_sub_classes.insert(id);
                    node_sub_classes = node_sub_classes
                        .union(sub_classes.get(&id).unwrap())
                        .cloned()
                        .collect();
                });
                sub_classes.insert(eclass.id, node_sub_classes);

                Some((cost.0, cost.1, cost.2, node.clone()))
            }
        }
    }

    /************************************************************************************************/
    /************************************************************************************************/
    /***********************************Added Functions for Lpextarctor *****************************/
    
    /***************************************************************************************************/
    
    pub fn solve(&mut self, root: Id) -> (RecExpr<L>) {
        let (expr, ids) = self.solve_multiple(&[root]) ;
        let mut costs : Vec<f64> = Vec::new();
        for id in &ids{
            if let Some(c) = self.costs.get(id) {
                let result = ALPHA * c.0 + BETA * c.1 + GAMMA * c.2;
                costs.push(result);
            }
        }
        expr
    }
    /************************************************************************************************/
    /// Extract (potentially multiple) roots
    pub fn solve_multiple(&mut self, roots: &[Id]) -> (RecExpr<L>, Vec<Id>) {
        let egraph = self.egraph;

        for class in self.vars.values() {
            self.model.set_binary(class.active);
        }

        for root in roots {
            let root = &egraph.find(*root);
            self.model.set_col_lower(self.vars[root].active, 1.0);
        }

        let solution = self.model.solve();
        /* log::info!(
            "CBC status {:?}, {:?}",
            solution.raw().status(),
            solution.raw().secondary_status()
        ); */

        let mut todo: Vec<Id> = roots.iter().map(|id| self.egraph.find(*id)).collect();
        let mut expr = RecExpr::default();
        // converts e-class ids to e-node ids
        let mut ids: HashMap<Id, Id> = HashMap::default();

        while let Some(&id) = todo.last() {
            if ids.contains_key(&id) {
                todo.pop();
                continue;
            }
            let v = &self.vars[&id];
            assert!(solution.col(v.active) > 0.0);
            let node_idx = v.nodes.iter().position(|&n| solution.col(n) > 0.0).unwrap();
            let node = &self.egraph[id].nodes[node_idx];
            // Returns true if the predicate is true on all children.
            let mut result = true ; 
            for child in node.children() {
                // Check if the condition is met for the current child
                if !ids.contains_key(&child) {
                    result=false; // Condition not met, return false immediately
                    break ;
                }
            }
            if result {
                let new_id = expr.add(node.clone().map_children(|i| ids[&self.egraph.find(i)]));
                ids.insert(id, new_id);
                todo.pop();
            } else {
                todo.extend_from_slice(node.children())
            }
        }
        let root_idxs = roots.iter().map(|root| ids[root]).collect();
        /*****************
        let is_dag= true ;
        for (i, n) in expr.from().iter().enumerate() {
            for &child in n.children() {
                if usize::from(child) >= i {
                        is_dag=false;
                }
            }
        }
        assert!(is_dag, "LpExtract found a cyclic term!: {:?}", expr);
        *********************/
        (expr, root_idxs)
    }
}
/********************************************************/
fn find_cycles<L, N>(egraph: &EGraph<L, N>, mut f: impl FnMut(Id, usize))
where
    L: Language,
    N: Analysis<L>,
{
    enum Color {
        White,
        Gray,
        Black,
    }
    type Enter = bool;

    let mut color: HashMap<Id, Color> = egraph.classes().map(|c| (c.id, Color::White)).collect();
    let mut stack: Vec<(Enter, Id)> = egraph.classes().map(|c| (true, c.id)).collect();

    while let Some((enter, id)) = stack.pop() {
        if enter {
            *color.get_mut(&id).unwrap() = Color::Gray;
            stack.push((false, id));
            for (i, node) in egraph[id].iter().enumerate() {
                for child in node.children() {
                    match &color[child] {
                        Color::White => stack.push((true, *child)),
                        Color::Gray => f(id, i),
                        Color::Black => (),
                    }
                }
            }
        } else {
            *color.get_mut(&id).unwrap() = Color::Black;
        }
    }
}

