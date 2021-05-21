use std::collections::{HashMap, HashSet};
use varisat::{CnfFormula, ExtendFormula};
use varisat::solver::Solver;
use varisat::{Var, Lit};
use bitintr::Popcnt;

type Field = Vec<Vec<usize>>;
type P = (usize, usize);
type Arc = (P, P);
type Sol = Vec<Arc>;

fn solve_numberlink(field: &Field) -> Option<Sol> {
    if field.len() == 0 || field[0].len() == 0 {
        return None;
    }

    let width = field[0].len();
    let height = field.len();

    let (s, t, b) = parse_field(&field).unwrap_or((vec![], vec![], vec![]));

    if s.len() == 0 || s.len() != t.len() || s.len()+t.len()+b.len() != width*height {
        return None;
    }

    let arcs: Vec<Arc> = gen_arcs(width, height);

    let mut formula = CnfFormula::new();

    let mut mp: HashMap<Arc, Var> = HashMap::new();

    /* "Solving Nubmerlink by a SAT-based Constraint Solver" (https://ipsj.ixsq.nii.ac.jp/ej/index.php?action=pages_view_main&active_action=repository_action_common_download&item_id=102780&item_no=1&attribute_id=1&file_no=1&page_id=13&block_id=8) */
    for (i, (u, v)) in arcs.clone().into_iter().enumerate() {
        let x = Var::from_index(i);
        let num_u = field[u.0][u.1];
        let num_v = field[v.0][v.1];
    
        mp.insert((u, v), x);
        
        // (12)
        // !(x and num_u != num_v)
        // !x or num_u == num_v
        if num_u != num_v {
            formula.add_clause(&[x.negative()]);
        }
    }

    for (u, v) in arcs {
        let adjs: &Vec<P> = &adj(u, width, height);

        let x = mp[&(u, v)];
        let y = mp[&(v, u)];

        // (2)
        formula.add_clause(&[x.negative(), y.negative()]);

        if s.contains(&u) {
            // (3)
            {
                let mut vars: Vec<Var> = vec![];    
                for v in adjs {
                    vars.push(mp[&(u, *v)]);
                }

                for lits in mk_clause_eq1(vars) {
                    formula.add_clause(lits.as_slice());
                }
            }    
            
            // (4)
            {
                for v in adjs {
                    formula.add_clause(&[mp[&(*v, u)].negative()]);
                }
            }
        }

        if t.contains(&u) {
            // (5)
            {
                for v in adjs {
                    formula.add_clause(&[mp[&(u, *v)].negative()]);
                }
            }
            
            // (6)
            {
                let mut vars: Vec<Var> = vec![];    
                for v in adjs {
                    vars.push(mp[&(*v, u)]);
                }

                for lits in mk_clause_eq1(vars) {
                    formula.add_clause(lits.as_slice());
                }
            }
        }

        if b.contains(&u) {
            // (8)
            {
                let mut vars: Vec<Var> = vec![];    
                for v in adjs {
                    vars.push(mp[&(u, *v)]);
                }
                
                for lits in mk_clause_less2(vars) {
                    formula.add_clause(lits.as_slice());
                }
            }    
            
            // (9)
            {
                let mut vars: Vec<Var> = vec![];    
                for v in adjs {
                    vars.push(mp[&(*v, u)]);
                }

                for lits in mk_clause_less2(vars) {
                    formula.add_clause(lits.as_slice());
                }
            }    
        }
    }

    println!("{:?}", formula);

    let mut solver = Solver::new();

    solver.add_formula(&formula);

    let solution = solver.solve().unwrap();

    println!("Solution: {}", solution);

    let model = solver.model();

    match model {
        Some(_) => {
            println!("{:?}", model);
        },
        None => {
            println!("No Solution");
        }
    }

    Some(vec![])
}

fn parse_field(field :&Field) -> Option<(Vec<P>, Vec<P>, Vec<P>)> {
    let mut cnt = vec![0; 17];
    let mut ends = vec![vec![]; 2];
    let mut b = vec![];
    
    for (i, line) in field.clone().into_iter().enumerate() {
        for (j, p) in line.clone().into_iter().enumerate() {
            if p > 0 {
                ends[cnt[p]].push((i, j));
                cnt[p] += 1;

                if cnt[p] > 2 {
                    return None;
                }
            } else {
                b.push((i, j));
            }
        }
    }

    Some((ends[0].clone(), ends[1].clone(), b))
}

fn mk_clause_eq1(vars: Vec<Var>) -> Vec<Vec<Lit>> {
    let mut res: Vec<Vec<Lit>> = vec![];
    let mut flgs: Vec<bool> = vec![];
    let n = vars.len();

    for bit in 0..(1<<n) {
        if ((bit as u32).popcnt()) as usize == n-1 {
            continue;
        }

        let mut lits: Vec<Lit> = vec![];

        for i in 0..n {
            lits.push(Lit::from_var(vars[i], (bit>>i&1) != 0));
        }

        res.push(lits);
    }

    res
}

fn mk_clause_less2(vars: Vec<Var>) -> Vec<Vec<Lit>> {
    let mut res: Vec<Vec<Lit>> = vec![];
    let mut flgs: Vec<bool> = vec![];
    let n = vars.len();

    for bit in 0..(1<<n) {
        if n < 2+((bit as u32).popcnt()) as usize {
            continue;
        }

        let mut lits: Vec<Lit> = vec![];

        for i in 0..n {
            lits.push(Lit::from_var(vars[i], (bit>>i&1) != 0));
        }

        res.push(lits);
    }

    res
}

fn adj(p: P, width: usize, height: usize) -> Vec<P> {
    let dx: Vec<i32> = vec![1, 0, -1, 0];
    let dy: Vec<i32> = vec![0, 1, 0, -1];

    let mut st = HashSet::new();
    let mut res = vec![];

    for d in 0..4 {
        let ni = (p.0 as i32 + dy[d]) as usize;
        let nj = (p.1 as i32 + dx[d]) as usize;

        if ni < width && nj < height && !st.contains(&(ni, nj)) {
            res.push((ni, nj));
            st.insert((ni, nj));
        }
    }

    res
}

fn gen_arcs(width: usize, height: usize) -> Vec<Arc> {
    let mut res: Vec<Arc> = vec![];

    for i in 0..width {
        for j in 0..height {
            let u = (i, j);
            let adjs = adj(u, width, height);

            for v in adjs {
                res.push((u, v));
            }
        }
    }

    res
}

fn parse_url(url: String) -> Option<Field> {
    let splitter = '/';
    let params: Vec<String> = url.split(splitter).map(|s| s.to_string()).collect();
    let length = params.len();

    if length < 3 {
        return None;
    }

    let width = params[length-3].parse().unwrap_or(0);
    let height = params[length-2].parse().unwrap_or(0);

    if width <= 0 || height <= 0 {
        return None;
    }

    let field_code = params[length-1].clone();

    if !is_valid_code(&field_code) {
        return None;
    }

    decode_field(width, height, field_code)
}

fn is_valid_code(code: &String) -> bool {
    return code.chars().all(char::is_alphanumeric);
}

fn decode_field(width: usize, height: usize, code: String) -> Option<Field> {
    let list: &Vec<char> = &code.chars().collect();
    let mut index: usize = 0;
    let mut i: usize = 0;
    let mut j: usize = 0;

    let mut res: Field = vec![vec![0; width as usize]; height as usize];

    while index < list.len() {
        while let Some(num) = get_num(index, list) {
            res[i as usize][j as usize] = num;

            index += 1;
            j += 1;

            if j >= width {
                j = 0;
                i += 1;
            }

            if index >= list.len() {
                break;
            }
        }

        consume(&mut index, &mut i, &mut j, width, list);
    }

    Some(res)
}

fn get_num(index: usize, list: &Vec<char>) -> Option<usize> {
    let ch = list[index as usize];

    if ch.is_digit(16) {
        return match ch.to_digit(16) {
            Some(num) => Some(num as usize),
            None => None,
        };
    } else {
        return None;
    }
}

fn consume(index: &mut usize, i: &mut usize, j: &mut usize, width: usize, list: &Vec<char>) {
    let length = list.len();

    while *index < length && !(list[*index as usize]).is_digit(16) {
        let ch = list[*index as usize];
        let value = (ch as i32) - ('f' as i32);

        if value <= 0 {
            return;
        }

        let value: usize = value as usize;

        *j += value;

        if *j >= width {
            *i += *j/width;
            *j %= width;
        }

        *index += 1;
    }    
}

fn main() {
    let opt_field = parse_url("http://pzv.jp/p.html?numlin/12/12/1p3h9g3j4i2j5t5l87g6l6j2g7jbgbjal8g1czg9uahcp4".to_string());
    
    println!("{:?}", opt_field);

    if let Some(field) = opt_field {
        solve_numberlink(&field);
    }
}