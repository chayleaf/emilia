use std::{collections::BTreeSet, env, fmt, fs::File, io::Read, ops::Not};

#[derive(Debug, Default)]
struct VarInfo {
    // (value, clause, assumption)
    value: Option<(bool, Option<usize>, usize)>,
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
    base_clauses: usize,
    prop_q: usize,
    // history of vars
    history: Vec<usize>,
    // assumption history of vars
    assumption_history: Vec<usize>,
    solving: bool,
}

#[derive(Debug)]
struct Unsat {
    learnt: Vec<Lit>,
    max_assumption: usize,
}

impl Solver {
    pub fn add_var(&mut self) -> Var {
        let ret = self.vars.len();
        self.vars.push(VarInfo::default());
        ret
    }
    fn remove_clause(&mut self, i: usize) {
        let clause = self.clauses.swap_remove(i);
        for lit in [clause[0], clause[1]] {
            let watchers = &mut self.vars[lit.var].watchers[usize::from(!lit.val)];
            for (i, x) in watchers.iter().copied().enumerate() {
                if x == self.clauses.len() {
                    watchers.swap_remove(i);
                    break;
                }
            }
        }
        if i < self.base_clauses {
            self.base_clauses -= 1;
        }
    }
    fn add_clause(
        &mut self,
        clause: impl IntoIterator<Item = Lit>,
    ) -> Result<Option<usize>, Unsat> {
        let learned = self.solving;
        let mut clause: BTreeSet<_> = clause
            .into_iter()
            .map(|x| {
                while x.var >= self.vars.len() {
                    self.add_var();
                }
                x
            })
            .collect();
        if clause.is_empty() {
            return Ok(None);
        }
        if clause.len() == 1 {
            let lit = clause.pop_first().unwrap();
            self.enqueue(lit, None)?;
            return Ok(None);
        }
        let clause: Vec<_> = clause.into_iter().collect();
        for ab in clause.windows(2) {
            if ab[0] == !ab[1] {
                return Ok(None);
            }
        }
        self.vars[clause[0].var].watchers[usize::from(!clause[0].val)].push(self.clauses.len());
        self.vars[clause[1].var].watchers[usize::from(!clause[1].val)].push(self.clauses.len());
        self.clauses.push(clause);
        if !learned {
            self.base_clauses = self.clauses.len();
        } else {
            self.prune();
        }
        Ok(Some(self.clauses.len() - 1))
    }
    fn val(&self, lit: Lit) -> Option<bool> {
        self.vars[lit.var].value.map(|x| x.0 == lit.val)
    }
    fn visit(&mut self, clause: usize, from: Lit) -> Result<Option<Lit>, Unsat> {
        let val = |lit: Lit| self.vars[lit.var].value.map(|x| x.0 == lit.val);
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
        self.enqueue(lit, Some(clause)).map(|_| None)
    }
    fn prune(&mut self) {
        let prune_threshold = self.base_clauses;
        let prune_target = self.base_clauses / 2;
        if self.clauses.len() - self.base_clauses > prune_threshold {
            // this is stable sort, so preserve newer clauses i guess
            self.clauses[self.base_clauses..].reverse();
            self.clauses[self.base_clauses..].sort_by_key(|clause| clause.len());
            while self.clauses.len() - self.base_clauses > prune_target {
                self.remove_clause(self.base_clauses + prune_target);
            }
            self.clauses[self.base_clauses..].reverse();
        }
    }
    fn enqueue(&mut self, lit: Lit, cause: Option<usize>) -> Result<(), Unsat> {
        match self.val(lit) {
            Some(true) => Ok(()),
            Some(false) => {
                if let Some(mut cause) = cause {
                    let mut learnt = vec![Lit { var: 0, val: false }];
                    let mut seen = BTreeSet::new();
                    let mut max_assumption = 0;
                    let mut counter = 1i32;
                    let mut p = lit.var;
                    let mut first = true;
                    let mut hist = self.history.iter().copied().rev();
                    while counter > 0 {
                        let c = &self.clauses[cause];
                        for q in c.iter().skip(if first {
                            counter -= 1;
                            first = false;
                            0
                        } else {
                            1
                        }) {
                            if !seen.insert(q.var) {
                                continue;
                            }
                            let (_, _, assumption_index) = self.vars[q.var].value.unwrap();
                            {
                                if assumption_index == self.assumption_history.len() {
                                    counter += 1;
                                } else if assumption_index > 0 {
                                    learnt.push(*q);
                                    max_assumption = max_assumption.max(assumption_index);
                                }
                            }
                        }
                        p = hist.next().unwrap();
                        let mut cause1 = self.vars[p].value.unwrap().1;
                        // next literal to look at
                        while !seen.contains(&p) {
                            p = hist.next().unwrap();
                            cause1 = self.vars[p].value.unwrap().1;
                        }
                        counter -= 1;
                        if counter <= 0 {
                            break;
                        }
                        cause = cause1.unwrap();
                    }
                    learnt[0] = Lit {
                        var: p,
                        val: !self.vars[p].value.unwrap().0,
                    };

                    Err(Unsat {
                        learnt,
                        max_assumption,
                    })
                } else {
                    Err(Unsat {
                        learnt: vec![],
                        max_assumption: 0,
                    })
                }
            }
            None => {
                self.enqueue_unchecked(lit, cause);
                Ok(())
            }
        }
    }
    fn enqueue_unchecked(&mut self, lit: Lit, cause: Option<usize>) {
        println!(
            "pre vals {lit:?} {:?}",
            self.vars.iter().map(|x| x.value).collect::<Vec<_>>()
        );
        debug_assert!(self.val(lit).is_none());
        self.vars[lit.var].value = Some((lit.val, cause, self.assumption_history.len()));
        self.history.push(lit.var);
    }
    fn propagate(&mut self) -> Result<(), Unsat> {
        println!("q {:?}", self.prop_q);
        while self.prop_q < self.history.len() {
            println!("prop {:?}", self.prop_q);
            let var = self.history[self.prop_q];
            self.prop_q += 1;
            let val = self.vars[var].value.unwrap().0;
            let mut watchers = Vec::new();
            std::mem::swap(
                &mut watchers,
                &mut self.vars[var].watchers[usize::from(val)],
            );
            let mut i = 0;
            while i < watchers.len() {
                if let Some(reassign) =
                    self.visit(watchers[i], Lit { var, val }).map_err(|err| {
                        self.prop_q = self.history.len();
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
        loop {
            let var = self.history.pop().unwrap();
            let val = self.vars[var].value.take().map(|x| x.0);
            if var == assumption {
                self.prop_q = self.history.len();
                return Lit {
                    var: assumption,
                    val: val.unwrap(),
                };
            }
        }
    }
    fn solve(mut self) -> Result<Vec<bool>, Unsat> {
        self.solving = true;
        loop {
            if let Err(err) = self.propagate() {
                if err.learnt.is_empty() || self.assumption_history.is_empty() {
                    return Err(err);
                }
                while self.assumption_history.len() > err.max_assumption {
                    self.undo_assumption();
                }
                let clause = (err.learnt.len() > 1)
                    .then(|| self.add_clause(err.learnt.iter().copied()).unwrap())
                    .flatten();
                println!("adding {:?}", err.learnt);
                self.enqueue_unchecked(*err.learnt.first().unwrap(), clause);
            } else {
                let mut solved = true;
                for (v, var) in self.vars.iter_mut().enumerate() {
                    if var.value.is_none() {
                        self.assumption_history.push(v);
                        println!("q");
                        self.enqueue_unchecked(Lit { var: v, val: false }, None);
                        solved = false;
                        break;
                    }
                }
                if solved {
                    return Ok(self
                        .vars
                        .iter()
                        .map(|x| x.value.map(|x| x.0).unwrap_or(false))
                        .collect());
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
