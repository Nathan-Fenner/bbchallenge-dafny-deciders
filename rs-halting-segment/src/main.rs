// This is a verified reimplementation of the algorithm
// described in https://discuss.bbchallenge.org/t/decider-halting-segment/75.

// A bit is either 0 or 1.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Bit {
    B0,
    B1,
}
use std::collections::{BTreeMap, HashMap, HashSet};

use Bit::*;

// Because the word "state" would otherwise be overloaded, the 5 "states" for the
// TM are instead called "Colors": CA, CB, CC, CD, CE, with the "C" standing for "Color".
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Color {
    CA,
    CB,
    CC,
    CD,
    CE,
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

pub type Program = HashMap<Input, Action>;

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
    program
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
enum Pos {
    At { inside: i32 },
    Before { limit: i32 },
    After { limit: i32 },
}
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

    let todo = program.keys().copied(); // set input: Input | input in program;
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
        print_segment(radius, &cover);

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
        println!("radius {}", radius);
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

fn main() {
    let program = from_string("1RB1LB_1LC0RE_0LD0RA_1RA0LD_---0RC");
    println!("{:?}", program);
    let prove_it_halts = decide_initial_segment_fixed_radius(2, &program, 500_000);
    println!("halts? {:?}", prove_it_halts);
}
