use std::fs;

fn main() {
    // Rust's Range upper bounds are exclusive.
    // Thus, we iterate from 4 up _until_, but not including, 16.
    for num_pigeons in 4..16 {
        let mut dimacs = String::new();

        let num_holes = num_pigeons - 1;

        print_header(&mut dimacs, num_pigeons, num_holes);
        place_pigeons_in_holes(&mut dimacs, num_pigeons, num_holes);
        enforce_no_hole_with_two_pigeons(&mut dimacs, num_pigeons, num_holes);

        fs::write(
            &format!("pigeonhole-{}p-{}h.cnf", num_pigeons, num_holes),
            dimacs,
        )
        .expect(&format!(
            "Unable to write file pigeonhole-{}p-{}h.cnf",
            num_pigeons, num_holes
        ));
    }
}

fn print_header(dimacs: &mut String, num_pigeons: i32, num_holes: i32) {
    let num_vars = num_pigeons * (num_pigeons - 1);

    // The total number of clauses can be derived as:
    // 1. n clauses to encode the first constraint (a pigeon is in a hole).
    // 2. For each hole, we generate (n - 1) clauses stating that pigeon i and pigeon j are not both in hole k.
    let num_clauses = num_pigeons + num_holes * num_holes * num_pigeons / 2;

    dimacs.push_str(&format!(
        "c Place {} pigeons in {} holes.\n",
        num_pigeons, num_holes
    ));
    dimacs.push_str(&format!("p cnf {} {}", num_vars, num_clauses))
}

fn place_pigeons_in_holes(dimacs: &mut String, num_pigeons: i32, num_holes: i32) {
    for pigeon in 1..num_pigeons + 1 {
        dimacs.push_str("\n");

        for hole in 1..num_holes + 1 {
            dimacs.push_str(&format!("{} ", num_holes * (pigeon - 1) + hole))
        }

        // Add the trailing 0 for each clause.
        dimacs.push_str("0");
    }
}

fn enforce_no_hole_with_two_pigeons(dimacs: &mut String, num_pigeons: i32, num_holes: i32) {
    for hole in 1..num_holes + 1 {
        for pigeon in 1..num_holes + 1 {
            for k in pigeon + 1..num_pigeons + 1 {
                dimacs.push_str("\n");
                dimacs.push_str(&format!(
                    "{} {} 0",
                    complement(num_holes * (pigeon - 1) + hole),
                    complement(num_holes * (k - 1) + hole)
                ))
            }
        }
    }
}

fn complement(literal: i32) -> i32 {
    literal * -1
}
