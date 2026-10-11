// harness: run
//! The Rust side of Chapter 2's comparisons: the Rust counterparts of the Lean
//! definitions in `code/lean/Book/Ch02/Basics.lean`, `Classes.lean` and
//! `Effects.lean`, so that the two can be read side by side.
//!
//! Run with: `cargo run --example ch02_rust_counterparts`

// ANCHOR: point
#[derive(Debug, Clone, Copy, PartialEq)]
struct Point {
    x: i64,
    y: i64,
}

impl Point {
    fn add(self, other: Point) -> Point {
        Point {
            x: self.x + other.x,
            y: self.y + other.y,
        }
    }
}
// ANCHOR_END: point

// ANCHOR: command
#[derive(Debug, Clone, PartialEq)]
enum Command {
    Ping,
    Get(String),
    Set(String, u64),
    Delete(String),
}

impl Command {
    fn describe(&self) -> String {
        match self {
            Command::Ping => "ping".to_string(),
            Command::Get(key) => format!("read {key}"),
            Command::Set(key, value) => format!("write {value} to {key}"),
            Command::Delete(key) => format!("remove {key}"),
        }
    }
}
// ANCHOR_END: command

// ANCHOR: tree
/// The recursive fields need a `Box`: without it, `Tree` would contain itself
/// and have infinite size.
#[derive(Debug)]
enum Tree {
    Leaf,
    Node(Box<Tree>, u64, Box<Tree>),
}

impl Tree {
    /// Consumes the tree and returns a new one, like the Lean version.
    fn insert(self, k: u64) -> Tree {
        match self {
            Tree::Leaf => Tree::Node(Box::new(Tree::Leaf), k, Box::new(Tree::Leaf)),
            Tree::Node(l, x, r) => {
                if k < x {
                    Tree::Node(Box::new(l.insert(k)), x, r)
                } else if x < k {
                    Tree::Node(l, x, Box::new(r.insert(k)))
                } else {
                    Tree::Node(l, x, r)
                }
            }
        }
    }

    fn to_vec(&self) -> Vec<u64> {
        match self {
            Tree::Leaf => Vec::new(),
            Tree::Node(l, x, r) => {
                let mut v = l.to_vec();
                v.push(*x);
                v.extend(r.to_vec());
                v
            }
        }
    }
}
// ANCHOR_END: tree

// ANCHOR: summary_trait
trait Summary {
    fn summary(&self) -> String;
    fn tag(&self) -> String {
        "item".to_string()
    }
}

struct Sensor {
    name: String,
    celsius: i64,
}

impl Summary for Sensor {
    fn summary(&self) -> String {
        format!("{}: {} °C", self.name, self.celsius)
    }
    fn tag(&self) -> String {
        "sensor".to_string()
    }
}

impl<T: Summary> Summary for Vec<T> {
    fn summary(&self) -> String {
        let parts: Vec<String> = self.iter().map(|x| x.summary()).collect();
        parts.join(", ")
    }
    fn tag(&self) -> String {
        "list".to_string()
    }
}

fn report<T: Summary>(x: &T) -> String {
    format!("[{}] {}", x.tag(), x.summary())
}
// ANCHOR_END: summary_trait

// ANCHOR: parse_nat
#[derive(Debug, PartialEq)]
enum ParseError {
    Empty,
    NotADigit(char),
}

fn parse_digit(c: char) -> Result<u64, ParseError> {
    c.to_digit(10)
        .map(u64::from)
        .ok_or(ParseError::NotADigit(c))
}

fn parse_nat(s: &str) -> Result<u64, ParseError> {
    if s.is_empty() {
        return Err(ParseError::Empty);
    }
    let mut n = 0;
    for c in s.chars() {
        let d = parse_digit(c)?;
        n = 10 * n + d;
    }
    Ok(n)
}
// ANCHOR_END: parse_nat

// ANCHOR: sum_squares
fn sum_squares(xs: &[u64]) -> u64 {
    let mut total = 0;
    for x in xs {
        total += x * x;
    }
    total
}
// ANCHOR_END: sum_squares

fn main() {
    let p = Point { x: 3, y: 4 };
    let moved = Point { y: 10, ..p };
    println!("{:?} {:?} {:?}", p, moved, p.add(p));

    let key = || "retries".to_string();
    let commands = [
        Command::Ping,
        Command::Get(key()),
        Command::Set(key(), 3),
        Command::Delete(key()),
    ];
    for c in &commands {
        println!("{}", c.describe());
    }

    let tree = [5, 3, 9, 1, 4, 3]
        .into_iter()
        .fold(Tree::Leaf, Tree::insert);
    println!("{:?}", tree.to_vec());

    let boiler = Sensor {
        name: "boiler".to_string(),
        celsius: 74,
    };
    println!("{}", report(&boiler));
    println!("{}", report(&vec![boiler]));

    println!("{:?} {:?}", parse_nat("2024"), parse_nat("2O24"));
    println!("{}", sum_squares(&[1, 2, 3]));
}
