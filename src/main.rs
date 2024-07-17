use std::{env, fs::File, io::Read};

#[derive(Debug, Default)]
struct VarInfo {
    value: Option<bool>,
}

type Var = usize;

#[derive(Copy, Clone)]
struct Lit {
    var: Var,
    sign: bool,
}

#[derive(Default)]
struct Solver {
    vars: Vec<VarInfo>,
    clauses: Vec<Vec<Lit>>,
}

#[derive(Debug)]
struct Unsat;

impl Solver {
    pub fn add_var(&mut self) -> Var {
        let ret = self.vars.len();
        self.vars.push(VarInfo::default());
        ret
    }
    fn add_clause(&mut self, clause: impl IntoIterator<Item = Lit>) -> Result<(), Unsat> {
        let clause = clause
            .into_iter()
            .map(|x| {
                while x.var >= self.vars.len() {
                    self.add_var();
                }
                x
            })
            .collect();
        self.clauses.push(clause);
        Ok(())
    }
    fn val(&self, lit: Lit) -> Option<bool> {
        self.vars[lit.var].value.map(|x| x != lit.sign)
    }
    fn stupid_check(&self) -> Result<bool, Unsat> {
        let mut solved = true;
        for clause in &self.clauses {
            let mut maybe_true = false;
            let mut is_true = false;
            for val in clause.iter().copied().map(|x| self.val(x)) {
                if val != Some(false) {
                    maybe_true = true;
                }
                if val == Some(true) {
                    is_true = true;
                }
            }
            if !maybe_true {
                return Err(Unsat);
            }
            if !is_true {
                solved = false;
            }
        }
        Ok(solved)
    }
    fn solve(&mut self) -> Result<Vec<bool>, Unsat> {
        let mut unroll = Vec::new();
        loop {
            for (v, var) in self.vars.iter_mut().enumerate() {
                if var.value.is_none() {
                    var.value = Some(false);
                    unroll.push(v);
                    break;
                }
            }
            match self.stupid_check() {
                Ok(true) => {
                    return Ok(self.vars.iter().map(|x| x.value.unwrap_or(false)).collect())
                }
                Ok(false) => {}
                Err(_) => loop {
                    if let Some(x) = unroll.pop() {
                        if self.vars[x].value == Some(false) {
                            self.vars[x].value = Some(true);
                            unroll.push(x);
                            break;
                        } else {
                            self.vars[x].value = None;
                        }
                    } else {
                        return Err(Unsat);
                    }
                },
            }
        }
    }
}

fn main() {
    let mut parser = varisat_dimacs::DimacsParser::new();
    let mut file = File::open(env::args().nth(1).unwrap()).unwrap();
    let mut bytes = vec![0u8; 65536];
    let mut s = Solver::default();
    let mut header = None;
    loop {
        let len = file.read(&mut bytes).unwrap();
        if len == 0 {
            parser.eof().unwrap();
        } else {
            parser.parse_chunk(&bytes[..len]).unwrap();
        }
        if header.is_none() {
            header = parser.header();
            if let Some(header) = &header {
                while s.vars.len() < header.var_count {
                    s.add_var();
                }
            }
        }
        for x in parser.take_formula().iter().map(|x| x.to_vec()) {
            s.add_clause(x.iter().map(|x| Lit {
                var: x.var().index(),
                sign: x.is_negative(),
            }))
            .unwrap();
        }
        if len == 0 {
            break;
        }
    }
    println!("{:?}", s.solve());
}
