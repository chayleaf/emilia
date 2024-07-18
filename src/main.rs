use std::{collections::VecDeque, env, fmt, fs::File, io::Read, ops::Not};

#[derive(Debug, Default)]
struct VarInfo {
    value: Option<bool>,
    watchers: [Vec<usize>; 2],
}

type Var = usize;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Lit {
    var: Var,
    val: bool,
}

impl fmt::Debug for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            if self.val {
                self.var as isize
            } else {
                -(self.var as isize)
            }
        )
    }
}

impl Not for Lit {
    type Output = Self;
    fn not(mut self) -> Self::Output {
        self.val = !self.val;
        self
    }
}

#[derive(Default)]
struct Solver {
    vars: Vec<VarInfo>,
    clauses: Vec<Vec<Lit>>,
    prop_q: VecDeque<usize>,
    history: Vec<usize>,
    assumption_history: Vec<usize>,
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
        let mut clause: Vec<_> = clause
            .into_iter()
            .map(|x| {
                while x.var >= self.vars.len() {
                    self.add_var();
                }
                x
            })
            .collect();
        if clause.is_empty() {
            return Ok(());
        }
        clause.sort();
        if clause.len() == 1 {
            let lit = clause[0];
            return self.enqueue(lit);
        }
        for ab in clause.windows(2) {
            if ab[0] == !ab[1] {
                return Ok(());
            }
        }
        self.vars[clause[0].var].watchers[usize::from(!clause[0].val)].push(self.clauses.len());
        self.vars[clause[1].var].watchers[usize::from(!clause[1].val)].push(self.clauses.len());
        self.clauses.push(clause);
        Ok(())
    }
    fn val(&self, lit: Lit) -> Option<bool> {
        self.vars[lit.var].value.map(|x| x == lit.val)
    }
    fn visit(&mut self, clause: usize, from: Lit) -> Result<Option<Lit>, Unsat> {
        let val = |lit: Lit| self.vars[lit.var].value.map(|x| x == lit.val);
        let c = &mut self.clauses[clause];
        if !c[0] == from {
            c.swap(0, 1);
        }
        if val(c[0]) == Some(true) {
            return Ok(None);
        }
        for (i, lit) in c.iter().copied().enumerate().skip(2) {
            if val(lit) != Some(false) {
                c.swap(1, i);
                return Ok(Some(!lit));
            }
        }
        let lit = c[0];
        self.enqueue(lit).map(|_| None)
    }
    fn enqueue(&mut self, lit: Lit) -> Result<(), Unsat> {
        match self.val(lit) {
            Some(true) => Ok(()),
            Some(false) => Err(Unsat),
            None => {
                self.enqueue_unchecked(lit);
                Ok(())
            }
        }
    }
    fn enqueue_unchecked(&mut self, lit: Lit) {
        debug_assert!(self.val(lit).is_none());
        self.vars[lit.var].value = Some(lit.val);
        self.prop_q.push_back(lit.var);
        self.history.push(lit.var);
    }
    fn propagate(&mut self) -> Result<(), Unsat> {
        while let Some(var) = self.prop_q.pop_front() {
            let val = self.vars[var].value.unwrap();
            let mut watchers = Vec::new();
            std::mem::swap(
                &mut watchers,
                &mut self.vars[var].watchers[usize::from(val)],
            );
            let mut i = 0;
            while i < watchers.len() {
                if let Some(reassign) =
                    self.visit(watchers[i], Lit { var, val }).map_err(|err| {
                        self.prop_q.clear();
                        err
                    })?
                {
                    self.vars[reassign.var].watchers[usize::from(reassign.val)].push(watchers[i]);
                    watchers.swap_remove(i);
                } else {
                    i += 1;
                }
            }
            std::mem::swap(
                &mut watchers,
                &mut self.vars[var].watchers[usize::from(val)],
            );
        }
        Ok(())
    }
    fn undo_assumption(&mut self) -> Lit {
        let assumption = self.assumption_history.pop().unwrap();
        let mut ret;
        loop {
            let var = self.history.pop().unwrap();
            ret = self.vars[var].value.take();
            if var == assumption {
                return Lit {
                    var: assumption,
                    val: ret.unwrap(),
                };
            }
        }
    }
    fn solve(&mut self) -> Result<Vec<bool>, Unsat> {
        loop {
            if self.propagate().is_err() {
                loop {
                    if self.assumption_history.is_empty() {
                        return Err(Unsat);
                    }
                    let mut lit = self.undo_assumption();
                    if !lit.val {
                        lit.val = true;
                        self.enqueue_unchecked(lit);
                        break;
                    }
                }
            } else {
                let mut solved = true;
                for (v, var) in self.vars.iter_mut().enumerate() {
                    if var.value.is_none() {
                        self.enqueue_unchecked(Lit { var: v, val: false });
                        self.assumption_history.push(v);
                        solved = false;
                        break;
                    }
                }
                if solved {
                    return Ok(self.vars.iter().map(|x| x.value.unwrap_or(false)).collect());
                }
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
                val: x.is_positive(),
            }))
            .unwrap();
        }
        if len == 0 {
            break;
        }
    }
    println!("{:?}", s.solve().unwrap());
}
