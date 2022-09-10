// This is a verified reimplementation of the algorithm
// described in https://discuss.bbchallenge.org/t/decider-halting-segment/75.

// A bit is either 0 or 1.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Bit {
    B0 = 0,
    B1 = 1,
}
use std::{
    collections::{BTreeMap, HashMap, HashSet},
    io::{Read, Write},
    os::windows::prelude::FileExt,
};

use Bit::*;

// Because the word "state" would otherwise be overloaded, the 5 "states" for the
// TM are instead called "Colors": CA, CB, CC, CD, CE, with the "C" standing for "Color".
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Color {
    CA = 1,
    CB = 2,
    CC = 3,
    CD = 4,
    CE = 5,
}
use Color::*;

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Direction {
    L,
    R,
}
use Direction::*;

pub fn direction_int(d: Direction) -> i32 {
    if d == R {
        1
    } else {
        -1
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
pub struct Action {
    pub write: Bit,
    pub new_color: Color,
    pub move_in: Direction,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
pub struct Input {
    pub head: Bit,
    pub color: Color,
}

impl Input {
    fn as_index(self) -> usize {
        self.head as usize * 5 + (self.color as usize - 1)
    }
}

// pub type Program = HashMap<Input, Action>;

pub struct Program {
    actions: [Option<Action>; 10],
}

impl Program {
    fn contains_key(&self, input: &Input) -> bool {
        self.actions[input.as_index()].is_some()
    }
    fn keys(&self) -> impl Iterator<Item = Input> + '_ {
        [B0, B1].into_iter().flat_map(move |bit| {
            [CA, CB, CC, CD, CE]
                .into_iter()
                .map(move |color| Input { head: bit, color })
                .filter(|input| self.contains_key(input))
        })
    }
}
impl std::ops::Index<&Input> for Program {
    type Output = Action;
    fn index(&self, index: &Input) -> &Self::Output {
        self.actions[index.as_index()].as_ref().unwrap()
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////

pub fn color_from_char(s: char) -> Color {
    match s {
        'A' => CA,
        'B' => CB,
        'C' => CC,
        'D' => CD,
        'E' => CE,
        _ => panic!("nope"),
    }
}

pub fn bit_from_char(s: char) -> Bit {
    match s {
        '0' => B0,
        '1' => B1,
        _ => panic!("nope"),
    }
}

pub fn dir_from_char(s: char) -> Direction {
    match s {
        'R' => R,
        'L' => L,
        _ => panic!("nope"),
    }
}

pub fn from_string(desc: &str) -> Program {
    assert!(desc.len() == 34);
    let desc = desc.chars().collect::<Vec<_>>();
    let mut program: HashMap<Input, Action> = HashMap::new();
    let mut col: Color;
    let mut base;

    base = 0;
    col = CA;
    if desc[base] != '-' {
        program.insert(
            Input {
                head: B0,
                color: col,
            },
            Action {
                write: bit_from_char(desc[base]),
                new_color: color_from_char(desc[base + 2]),
                move_in: dir_from_char(desc[base + 1]),
            },
        );
    }
    if desc[base + 3] != '-' {
        program.insert(
            Input {
                head: B1,
                color: col,
            },
            Action {
                write: bit_from_char(desc[base + 3]),
                new_color: color_from_char(desc[base + 5]),
                move_in: dir_from_char(desc[base + 4]),
            },
        );
    }
    base = 7;
    col = CB;
    if desc[base] != '-' {
        program.insert(
            Input {
                head: B0,
                color: col,
            },
            Action {
                write: bit_from_char(desc[base]),
                new_color: color_from_char(desc[base + 2]),
                move_in: dir_from_char(desc[base + 1]),
            },
        );
    }
    if desc[base + 3] != '-' {
        program.insert(
            Input {
                head: B1,
                color: col,
            },
            Action {
                write: bit_from_char(desc[base + 3]),
                new_color: color_from_char(desc[base + 5]),
                move_in: dir_from_char(desc[base + 4]),
            },
        );
    }
    base = 14;
    col = CC;
    if desc[base] != '-' {
        program.insert(
            Input {
                head: B0,
                color: col,
            },
            Action {
                write: bit_from_char(desc[base]),
                new_color: color_from_char(desc[base + 2]),
                move_in: dir_from_char(desc[base + 1]),
            },
        );
    }
    if desc[base + 3] != '-' {
        program.insert(
            Input {
                head: B1,
                color: col,
            },
            Action {
                write: bit_from_char(desc[base + 3]),
                new_color: color_from_char(desc[base + 5]),
                move_in: dir_from_char(desc[base + 4]),
            },
        );
    }
    base = 21;
    col = CD;
    if desc[base] != '-' {
        program.insert(
            Input {
                head: B0,
                color: col,
            },
            Action {
                write: bit_from_char(desc[base]),
                new_color: color_from_char(desc[base + 2]),
                move_in: dir_from_char(desc[base + 1]),
            },
        );
    }
    if desc[base + 3] != '-' {
        program.insert(
            Input {
                head: B1,
                color: col,
            },
            Action {
                write: bit_from_char(desc[base + 3]),
                new_color: color_from_char(desc[base + 5]),
                move_in: dir_from_char(desc[base + 4]),
            },
        );
    }
    base = 28;
    col = CE;
    if desc[base] != '-' {
        program.insert(
            Input {
                head: B0,
                color: col,
            },
            Action {
                write: bit_from_char(desc[base]),
                new_color: color_from_char(desc[base + 2]),
                move_in: dir_from_char(desc[base + 1]),
            },
        );
    }
    if desc[base + 3] != '-' {
        program.insert(
            Input {
                head: B1,
                color: col,
            },
            Action {
                write: bit_from_char(desc[base + 3]),
                new_color: color_from_char(desc[base + 5]),
                move_in: dir_from_char(desc[base + 4]),
            },
        );
    }

    let mut res = Program {
        actions: [None; 10],
    };
    for (key, val) in program {
        res.actions[key.as_index()] = Some(val);
    }
    res
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
enum Pos {
    At { inside: i32 },
    Before { limit: i32 },
    After { limit: i32 },
}
use clap::Parser;
use Pos::*;

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
struct HaltingSegment {
    position: Pos,
    color: Color,
    pattern: BTreeMap<i32, Bit>,
}

fn can_match_initial(segment: &HaltingSegment) -> bool {
    segment.color == CA && segment.pattern.values().all(|val| val == &B0)
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
struct InputAction {
    input: Input,
    action: Action,
}

fn cover_input(
    radius: i32,
    program: &Program,
    config: &HaltingSegment,
    input: Input,
) -> HashSet<HaltingSegment> {
    let action = program[&input];
    if action.new_color != config.color {
        return HashSet::new();
    }

    match config.position {
        At { inside: index } => {
            let prev_index = index - direction_int(program[&input].move_in);
            if config.pattern.contains_key(&prev_index)
                && action.write != config.pattern[&prev_index]
            {
                // This behavior is inconsistent.
                return HashSet::new();
            }

            // Otherwise, we need a new config.
            let prev_config = HaltingSegment {
                color: input.color,
                position: At { inside: prev_index },
                pattern: {
                    // [prev_index := input.head]
                    let mut new_pattern = config.pattern.clone();
                    new_pattern.insert(prev_index, input.head);
                    new_pattern
                },
            };

            if 0 - radius <= prev_index && prev_index <= radius {
                return vec![prev_config].into_iter().collect();
            }

            // Here, we have a valid cover, but it's not "compact".
            assert!(prev_index == 1 + radius || prev_index == -1 - radius);

            if prev_index == -1 - radius {
                // far left
                vec![HaltingSegment {
                    color: input.color,
                    position: Before { limit: prev_index },
                    pattern: config.pattern.clone(),
                }]
                .into_iter()
                .collect()
            } else {
                // far right
                vec![HaltingSegment {
                    color: input.color,
                    position: After { limit: prev_index },
                    pattern: config.pattern.clone(),
                }]
                .into_iter()
                .collect()
            }
        }
        Before { limit: lim } => {
            if program[&input].move_in == R {
                // Still in Before(lim).
                let prev_config = HaltingSegment {
                    color: input.color,
                    position: Before { limit: lim },
                    pattern: config.pattern.clone(),
                };
                return vec![prev_config].into_iter().collect();
            }

            // There are two cases here:
            let still_before = HaltingSegment {
                color: input.color,
                position: Before { limit: lim },
                pattern: config.pattern.clone(),
            };
            let on_edge = HaltingSegment {
                color: input.color,
                position: At { inside: 0 - radius },
                pattern: {
                    let mut new_pattern = config.pattern.clone();
                    new_pattern.insert(0 - radius, input.head);
                    new_pattern
                    // config.pattern[0 - radius := input.head]
                },
            };

            if config.pattern.contains_key(&(0 - radius))
                && config.pattern[&(0 - radius)] != program[&input].write
            {
                vec![still_before].into_iter().collect()
            } else {
                vec![still_before, on_edge].into_iter().collect()
            }
        }
        After { limit: lim } => {
            if program[&input].move_in == L {
                // Still in Before(lim).
                let prev_config = HaltingSegment {
                    color: input.color,
                    position: After { limit: lim },
                    pattern: config.pattern.clone(),
                };
                return vec![prev_config].into_iter().collect();
            }

            // There are two cases here:
            let still_after = HaltingSegment {
                color: input.color,
                position: After { limit: lim },
                pattern: config.pattern.clone(),
            };
            let on_edge = HaltingSegment {
                color: input.color,
                position: At { inside: radius },
                pattern: {
                    let mut new_pattern = config.pattern.clone();
                    new_pattern.insert(radius, input.head);
                    new_pattern
                }, // config.pattern[radius := input.head]
            };

            if config.pattern.contains_key(&(radius))
                && config.pattern[&(radius)] != program[&input].write
            {
                vec![still_after].into_iter().collect()
            } else {
                vec![still_after, on_edge].into_iter().collect()
            }
        }
    }
}

fn cover_all_inputs(
    radius: i32,
    program: &Program,
    config: &HaltingSegment,
) -> HashSet<HaltingSegment> {
    let mut covers = HashSet::new();

    let todo = program.keys(); // set input: Input | input in program;
                               // let mut done: HashSet<Input> = HashSet::new();
    for input in todo {
        // :| input in todo;
        let input_covers = cover_input(radius, program, config, input);
        covers.extend(input_covers.into_iter());
        // covers := covers + input_covers;
        // todo := todo - {input};
        // done := done + {input};
    }
    covers
}

fn single_step_halting_covers(
    _radius: i32,
    program: &Program,
) -> impl Iterator<Item = HaltingSegment> + '_ {
    [B0, B1].into_iter().flat_map(|bit| {
        [CA, CB, CC, CD, CE]
            .into_iter()
            .map(move |color| Input { head: bit, color })
            .filter(|input| !program.contains_key(input))
            .map(|input| HaltingSegment {
                color: input.color,
                position: At { inside: 0 },
                pattern: vec![(0, input.head)].into_iter().collect(),
            })
    })
    /*
    covers := set bit: Bit, color: Color | Input(bit, color) !in program :: HaltingSegment(
      color := color,
      position := At(0),
      pattern := map[0 := bit]
    );
     */
}

fn decide_initial_segment_fixed_radius(radius: i32, program: &Program, gas: i64) -> (bool, i64) {
    if gas == 0 {
        return (false, 0);
    }
    let mut remaining_gas = gas - 1;
    let mut todo_covers: Vec<HaltingSegment> =
        single_step_halting_covers(radius, program).collect();
    let mut done_covers: HashSet<HaltingSegment> = HashSet::new();

    while remaining_gas > 0 && !todo_covers.is_empty() {
        remaining_gas -= 1;

        // Take arbitrary cover in todo_covers
        // var cover :| cover in todo_covers;
        let cover = todo_covers.pop().unwrap();
        // print_segment(radius, &cover);

        if can_match_initial(&cover) {
            return (false, remaining_gas);
        }

        if done_covers.contains(&cover) {
            continue; // In certain cases, duplicates can be added.
        }

        let new_covers = cover_all_inputs(radius, program, &cover);
        done_covers.insert(cover); // done_covers := done_covers + { cover };
        for new_cover in new_covers {
            if !done_covers.contains(&new_cover) {
                todo_covers.push(new_cover);
            }
        }
        // todo_covers := todo_covers + new_covers;
        // todo_covers := todo_covers - done_covers;
    }

    if !todo_covers.is_empty() {
        return (false, remaining_gas);
    }
    (true, remaining_gas)
}

pub fn decide_initial_segment(program: &Program, gas: i64) -> bool {
    let mut radius = 1;
    let mut remaining_gas = gas;
    while remaining_gas > 0 {
        // println!("radius {}", radius);
        let (does_loop, leftover_gas) =
            decide_initial_segment_fixed_radius(radius, program, remaining_gas);
        remaining_gas = leftover_gas;
        if does_loop {
            return true;
        }
        radius += 1;
    }
    false
}

/*






method Main() {
  var program := from_string("1RB1LB_1LC0RE_0LD0RA_1RA0LD_---0RC");

  var prove_it_halts := decide_initial_segment(program, 200_000);
  print "halts? ";
  print prove_it_halts;
  print "\n";


  /*
  // This is the current candidate for BB(5):
  // 1RB1LC_1RC1RB_1RD0LE_1LA1LD_---0LA
  // It runs for 47,176,870 steps and then halts.
  var busy_beaver_candidate := from_string("1RB1LC_1RC1RB_1RD0LE_1LA1LD_---0LA");
  // var busy_beaver_candidate: Program := map[program];
  print busy_beaver_candidate;
  print "\n";

  var step_count;
  var result;

  step_count := 47_176_869;
  print "Run for ";
  print step_count;
  print " steps...\n-> halt? ";
  result := machine_step_iterative(busy_beaver_candidate, INITIAL_STATE, step_count);
  print result.Halt?;
  print "\n";

  step_count := 47_176_870;
  print "Run for ";
  print step_count;
  print " steps...\n-> halt? ";
  result := machine_step_iterative(busy_beaver_candidate, INITIAL_STATE, step_count);
  print result.Halt?;
  print "\n";
  */
} */

fn print_segment(radius: i32, segment: &HaltingSegment) {
    print!("State: {:?} ;", segment.color);
    for x in -radius - 1..=radius + 1 {
        let focused = segment.position == At { inside: x }
            || x == -radius - 1 && segment.position == Before { limit: -radius - 1 }
            || x == radius + 1 && segment.position == After { limit: radius + 1 };
        print!("{}", if focused { "[" } else { " " });
        if segment.pattern.contains_key(&x) {
            let s = format!("{:?}", segment.pattern[&x]);
            print!("{}", &s[1..]);
        } else {
            print!("_");
        }
        print!("{}", if focused { "]" } else { " " });
    }
    println!();
}

#[derive(clap::Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Options {
    #[clap(long = "seed-file")]
    seed_file_path: String,

    #[clap(long = "unresolved-list-file")]
    unresolved_file_path: String,

    #[clap(long = "output-file")]
    output_file: String,

    #[clap(long = "step-limit", default_value_t = 1000)]
    step_limit: i64,
}

fn main() {
    let options = Options::parse();

    let seed_file = std::fs::File::open(&options.seed_file_path)
        .expect("The --seed-file must be an accessible file.");

    let mut unresolved_file = std::fs::File::open(&options.unresolved_file_path)
        .expect("The --unresolved-list-file must be an accessible file.");

    let total_unresolved_count = unresolved_file.metadata().unwrap().len() / 4;
    println!("Unresolved machines: {}", total_unresolved_count);

    if options.step_limit <= 0 {
        panic!("The step_limit must be positive.");
    }

    let mut count_proc = 0;
    let mut total_looping = 0;

    let limit = options.step_limit;

    let mut output = std::fs::File::create(&options.output_file).expect("new file");
    loop {
        let mut index: [u8; 4] = [0; 4];
        let count = unresolved_file.read(&mut index).expect("works");
        if count == 0 {
            break;
        }
        // Get the index.
        let raw_index = u32::from_be_bytes(index);
        let mut buf: [u8; 30] = [0; 30];
        // Scan to the place in the big file.
        let count_read = seed_file
            .seek_read(&mut buf, (raw_index as u64 + 1) * 30)
            .expect("works");
        assert!(count_read == 30);
        let program = byte_buffer_to_readable_program(&buf);

        let loopy = decide_initial_segment(&from_string(&program), limit);
        if loopy {
            let count = output.write(&index).expect("works");
            assert!(count == 4);
            total_looping += 1;
        }

        count_proc += 1;
        if count_proc % 1000 == 0 {
            println!(
                "{:8}/{:8} :: so far proved {:8}",
                count_proc, total_unresolved_count, total_looping
            );
        }
    }

    fn byte_buffer_to_readable_program(buffer: &[u8]) -> String {
        let mut output = String::new();
        for bi in (0..30).step_by(3) {
            if bi > 0 && bi % 6 == 0 {
                output += "_";
            }
            if buffer[bi + 2] == 0 {
                output += "---";
                continue;
            }
            if buffer[bi] == 0 {
                output += "0";
            } else if buffer[bi] == 1 {
                output += "1";
            } else {
                panic!();
            }
            if buffer[bi + 1] == 0 {
                output += "R";
            } else if buffer[bi + 1] == 1 {
                output += "L";
            } else {
                panic!();
            }
            if buffer[bi + 2] >= 1 && buffer[bi + 2] <= 5 {
                output += &format!("{}", (buffer[bi + 2] - 1 + b'A') as char);
            } else {
                panic!();
            }
        }
        output
    }
}
