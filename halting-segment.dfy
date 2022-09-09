// This is a verified reimplementation of the algorithm
// described in https://discuss.bbchallenge.org/t/decider-halting-segment/75.


// A bit is either 0 or 1.
datatype Bit = B0 | B1

// Because the word "state" would otherwise be overloaded, the 5 "states" for the
// TM are instead called "Colors": CA, CB, CC, CD, CE, with the "C" standing for "Color".
datatype Color = CA | CB | CC | CD | CE

datatype MachineState = MachineState(
  tape: set<int>, // The set of 1s
  position: int,
  color: Color
)

// The TM can move left or right at each step.
datatype Direction = L | R

function method direction_int(d: Direction): int {
  if d == R then 1 else -1
}

// An action describes what the machine might be told to do by a program:
// - write the given bit
// - switch to the given color
// - move one step in given direction
datatype Action = Action(write: Bit, new_color: Color, move: Direction)

// machine_step_action applies the given action to the machine state.
function method machine_step_action(m: MachineState, action: Action): MachineState {
  MachineState(
    tape := if action.write == B1 then m.tape + {m.position} else m.tape - {m.position},
    position := m.position + direction_int(action.move),
    color := action.new_color
  )
}

// All TMs are assumed to begin in the color CA, on a tape of all zeros.
const INITIAL_STATE: MachineState := MachineState(
  tape := {},
  position := 0,
  color := CA
)

// `Input` is a structure containing the information needed to find out what
// action should be applied next in a TM program.
datatype Input = Input(head: Bit, color: Color)

// A program is a (partial) mapping from inputs to actions, describing what the TM
// should do next in each situation.
//
// If a transition is absent, then it is assumed to be a halting transition.
type Program = map<Input, Action>

// A `MachineStep` either is either `Halt` if no transition for the current state
// exists, or it is NextMachine and holds that next state.
datatype MachineStep = NextMachine(next_state: MachineState) | Halt

// machine_step causes the provided state to step forward once according to the
// provided program. The output will either be the next state, or Halt if there
// is no configured transition.
function method machine_step(program: Program, m: MachineState): MachineStep {
  var input := Input(if m.position in m.tape then B1 else B0, m.color);
  if input in program
    then NextMachine(machine_step_action(m, program[input]))
    else Halt
}

// This function is a helper for moving 'n' steps forward in time.
// It is a `function` rather than `function method` because it will cause stack-overflow if run
// for more than a small number of iterations.
function machine_step_n(program: Program, m: MachineState, n: nat): MachineStep {
  if n == 0
    // If n is zero, then the output is the same as the initial program.
    then NextMachine(m)
    // Otherwise, run n-1 steps. If that machine has not yet halted, run it one
    // more step.
    else match machine_step_n(program, m, n-1) {
      case Halt => Halt
      case NextMachine(m2) => machine_step(program, m2)
    }
}

// This method computes the same value as `machine_step_n` (guaranteed by its ensures clause below).
// This version can be called at runtime because it will not overflow the stack.
method machine_step_iterative(program: Program, m: MachineState, n: nat)
returns (result: MachineStep)
ensures result == machine_step_n(program, m, n) {
  var i := 0;
  var current_state := NextMachine(m);

  while i < n
  invariant 0 <= i <= n
  invariant current_state == machine_step_n(program, m, i)
  {
    current_state := if current_state.Halt? then Halt else machine_step(program, current_state.next_state);
    i := i + 1;
  }
  return current_state;
}

// This function returns the nth TM state for a program, starting from the
// initial state.
function machine_iter_n(program: Program, n: nat): MachineStep {
  machine_step_n(program, INITIAL_STATE, n)
}

// By definition, a machine halts if there's a step such that at that point, it halts.
predicate program_eventually_halts(program: Program) {
  exists n :: n >= 0 && machine_iter_n(program, n).Halt?
}

// A program loops forever if it never halts.
predicate program_loops_forever(program: Program) {
  !program_eventually_halts(program)
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

function method color_from_char(s: char): Color {
  match s {
    case 'A' => CA
    case 'B' => CB
    case 'C' => CC
    case 'D' => CD
    case 'E' => CE
    case _ => CA // Avoid
  }
}

function method bit_from_char(s: char): Bit {
  match s {
    case '0' => B0
    case '1' => B1
    case _ => B0 // Avoid
  }
}

function method dir_from_char(s: char): Direction {
  match s {
    case 'R' => R
    case 'L' => L
    case _ => R // Avoid
  }
}

method from_string(desc: string) returns (program: Program)
requires |desc| == 34 {
  program := map[];
  var col: Color;
  var base: nat;
  
  base := 0;
  col := CA;
  if desc[base] != '-' {
    program := program[Input(B0, col) := Action(bit_from_char(desc[base]), color_from_char(desc[base+2]), dir_from_char(desc[base+1]))];
  }
  if desc[base+3] != '-' {
    program := program[Input(B1, col) := Action(bit_from_char(desc[base+3]), color_from_char(desc[base+5]), dir_from_char(desc[base+4]))];
  }
  base := 7;
  col := CB;
  if desc[base] != '-' {
    program := program[Input(B0, col) := Action(bit_from_char(desc[base]), color_from_char(desc[base+2]), dir_from_char(desc[base+1]))];
  }
  if desc[base+3] != '-' {
    program := program[Input(B1, col) := Action(bit_from_char(desc[base+3]), color_from_char(desc[base+5]), dir_from_char(desc[base+4]))];
  }
  base := 14;
  col := CC;
  if desc[base] != '-' {
    program := program[Input(B0, col) := Action(bit_from_char(desc[base]), color_from_char(desc[base+2]), dir_from_char(desc[base+1]))];
  }
  if desc[base+3] != '-' {
    program := program[Input(B1, col) := Action(bit_from_char(desc[base+3]), color_from_char(desc[base+5]), dir_from_char(desc[base+4]))];
  }
  base := 21;
  col := CD;
  if desc[base] != '-' {
    program := program[Input(B0, col) := Action(bit_from_char(desc[base]), color_from_char(desc[base+2]), dir_from_char(desc[base+1]))];
  }
  if desc[base+3] != '-' {
    program := program[Input(B1, col) := Action(bit_from_char(desc[base+3]), color_from_char(desc[base+5]), dir_from_char(desc[base+4]))];
  }
  base := 28;
  col := CE;
  if desc[base] != '-' {
    program := program[Input(B0, col) := Action(bit_from_char(desc[base]), color_from_char(desc[base+2]), dir_from_char(desc[base+1]))];
  }
  if desc[base+3] != '-' {
    program := program[Input(B1, col) := Action(bit_from_char(desc[base+3]), color_from_char(desc[base+5]), dir_from_char(desc[base+4]))];
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

datatype Pos = At(inside: int) | Before(limit: int) | After(limit: int)

predicate pos_matches(pos: Pos, index: int) {
  match pos {
    case At(x) => index == x
    case Before(lim_max) => index <= lim_max
    case After(lim_min) => index >= lim_min
  }
}

datatype HaltingSegment = HaltingSegment(
  position: Pos,
  color: Color,
  pattern: map<int, Bit>
)

// A segment matches a state if there's an appropriate translation such that the corresponding bits are set.
// Note that the "pattern" is treated as sparse, but the tape is not (missing on tape just means 0).
predicate config_matches_state(segment: HaltingSegment, state: MachineState) {
  segment.color == state.color && pos_matches(segment.position, state.position) && forall index | index in segment.pattern :: get_tape(state, index) == segment.pattern[index]
}

// We can check whether the initial state matches a segment.
// TODO: Will need to work with translated version, eventually.
function method can_match_initial(segment: HaltingSegment): (matches: bool)
ensures !matches ==> !config_matches_state(segment, INITIAL_STATE) {
  segment.color == CA && forall k | k in segment.pattern :: segment.pattern[k] == B0
}

function method get_input(state: MachineState): Input
{
  Input(if state.position in state.tape then B1 else B0, state.color)
}

function method get_tape(state: MachineState, index: int): Bit
{
  if index in state.tape then B1 else B0
}

datatype InputAction = InputAction(input: Input, action: Action)

predicate covers_previous(program: Program, config: HaltingSegment, covers: set<HaltingSegment>)
{
  forall prev: MachineState | !machine_step(program, prev).Halt? && config_matches_state(config, machine_step(program, prev).next_state) ::
    exists cover :: cover in covers && config_matches_state(cover, prev)
}

predicate config_set_covers(configs: set<HaltingSegment>, state: MachineState)
{
  exists cover | cover in configs :: config_matches_state(cover, state)
}

predicate single_steps_into(program: Program, prev: MachineState, config: HaltingSegment)
{
  get_input(prev) in program && !machine_step(program, prev).Halt? && config_matches_state(config, machine_step(program, prev).next_state)
}

predicate segment_radius(radius: nat, config: HaltingSegment)
requires radius >= 1
{
  (config.position.Before? ==> config.position == Before(-1 - radius))
  && (config.position.After? ==> config.position == After(1 + radius))
  && (config.position.At? ==> 0 - radius <= config.position.inside <= radius)
  && (forall k | k in config.pattern :: 0 - radius <= k <= radius)
}

method cover_input(radius: nat, program: Program, config: HaltingSegment, input: Input)
returns (covers: set<HaltingSegment>)
requires radius >= 1
requires segment_radius(radius, config)
requires input in program
ensures forall prev | single_steps_into(program, prev, config) && get_input(prev) == input :: config_set_covers(covers, prev)
ensures forall cover | cover in covers :: segment_radius(radius, cover)
{
  var action := program[input];
  if action.new_color != config.color {
    forall prev | get_input(prev) == input && !machine_step(program, prev).Halt? && config_matches_state(config, machine_step(program, prev).next_state)
    ensures exists cover | cover in covers :: config_matches_state(cover, prev)
    {
      assert machine_step(program, prev).next_state.color == action.new_color;
      assert machine_step(program, prev).next_state.color == config.color;
    }
    return {};
  }
  
  match config.position {
    case At(index) => {
      var prev_index := index - direction_int(program[input].move);
      assert forall prev | single_steps_into(program, prev, config) && get_input(prev) == input :: prev.position == prev_index;
      if prev_index in config.pattern && action.write != config.pattern[prev_index] {
        // This behavior is inconsistent.
        covers := {};
        forall prev | single_steps_into(program, prev, config) && get_input(prev) == input
        ensures config_set_covers(covers, prev)
        {
        }
        return {};
      }

      // Otherwise, we need a new config.
      var prev_config := HaltingSegment(
        color := input.color,
        position := At(prev_index),
        pattern := config.pattern[prev_index := input.head]
      );

      if 0 - radius <= prev_index <= radius {
        return { prev_config };
      }

      // Here, we have a valid cover, but it's not "compact".
      assert prev_index == 1 + radius || prev_index == -1 - radius;

      if prev_index == -1 - radius {
        // far left
        return {
          HaltingSegment(
            color := input.color,
            position := Before(prev_index),
            pattern := config.pattern
          )
        };
      } else {
        // far right
        return {
          HaltingSegment(
            color := input.color,
            position := After(prev_index),
            pattern := config.pattern
          )
        };
      }
    }
    case Before(lim) => {
      var prev_index_pattern := Before(lim - direction_int(program[input].move));
      assert forall prev | single_steps_into(program, prev, config) && get_input(prev) == input :: pos_matches(prev_index_pattern, prev.position);

      if program[input].move == R {
        // Still in Before(lim).
        var prev_config := HaltingSegment(
          color := input.color,
          position := Before(lim),
          pattern := config.pattern
        );
        covers := { prev_config };
        return covers;
      }

      // There are two cases here:
      var still_before := HaltingSegment(
        color := input.color,
        position := Before(lim),
        pattern := config.pattern
      );
      var on_edge := HaltingSegment(
        color := input.color,
        position := At(0 - radius),
        pattern := config.pattern[0 - radius := input.head]
      );

      forall prev | single_steps_into(program, prev, config) && get_input(prev) == input
      ensures config_matches_state(still_before, prev) || config_matches_state(on_edge, prev)
      {
        // ...
      }

      return { still_before, on_edge };
    }
    case After(lim) => {
      var prev_index_pattern := After(lim - direction_int(program[input].move));
      assert forall prev | single_steps_into(program, prev, config) && get_input(prev) == input :: pos_matches(prev_index_pattern, prev.position);

      if program[input].move == L {
        // Still in Before(lim).
        var prev_config := HaltingSegment(
          color := input.color,
          position := After(lim),
          pattern := config.pattern
        );
        covers := { prev_config };
        return covers;
      }

      // There are two cases here:
      var still_before := HaltingSegment(
        color := input.color,
        position := After(lim),
        pattern := config.pattern
      );
      var on_edge := HaltingSegment(
        color := input.color,
        position := At(radius),
        pattern := config.pattern[radius := input.head]
      );

      forall prev | single_steps_into(program, prev, config) && get_input(prev) == input
      ensures config_matches_state(still_before, prev) || config_matches_state(on_edge, prev)
      {
      }

      return { still_before, on_edge };
    }
  }
}

method cover_all_inputs(radius: nat, program: Program, config: HaltingSegment)
returns (covers: set<HaltingSegment>)
requires radius >= 1
requires segment_radius(radius, config)
ensures forall prev | single_steps_into(program, prev, config) :: config_set_covers(covers, prev)
ensures forall cover | cover in covers :: segment_radius(radius, cover)
ensures covers_previous(program, config, covers)
{
  covers := {};

  var todo := set input: Input | input in program;
  var done := {};

  while |todo| != 0
  invariant forall cover | cover in covers :: segment_radius(radius, cover)
  invariant forall input: Input | input in todo :: input in program
  invariant forall input: Input | input in program :: input in todo + done
  invariant forall input: Input | input in done :: forall prev | single_steps_into(program, prev, config) && get_input(prev) == input :: config_set_covers(covers, prev)
  {
    var input :| input in todo;
    var input_covers := cover_input(radius, program, config, input);
    covers := covers + input_covers;
    todo := todo - {input};
    done := done + {input};
  }

  forall prev: MachineState | !machine_step(program, prev).Halt? && config_matches_state(config, machine_step(program, prev).next_state)
  ensures exists cover :: cover in covers && config_matches_state(cover, prev)
  {
    assert get_input(prev) in program;
  }

  return covers;
}

method single_step_halting_covers(radius: nat, program: Program)
returns (covers: set<HaltingSegment>)
requires radius >= 1
ensures forall cover | cover in covers :: segment_radius(radius, cover)
ensures forall state: MachineState | state.position == 0 && machine_step(program, state).Halt? :: config_set_covers(covers, state)
{

  covers := set bit: Bit, color: Color | Input(bit, color) !in program :: HaltingSegment(
    color := color,
    position := At(0),
    pattern := map[0 := bit]
  );

  forall state: MachineState | state.position == 0 && machine_step(program, state).Halt? 
  ensures config_set_covers(covers, state)
  {
    var input := get_input(state);
    assert input !in program;
    var my_cover := HaltingSegment(
      color := input.color,
      position := At(0),
      pattern := map[0 := input.head]
    );
    assert config_matches_state(my_cover, state);
  }

  return covers;
}

method decide_initial_segment_fixed_radius(radius: nat, program: Program, gas: nat)
returns (loops_forever: bool, remaining_gas: nat)
requires radius >= 1
ensures loops_forever ==> !program_eventually_halts(program)
ensures remaining_gas < gas || gas == 0
{
  if gas == 0 {
    return false, 0;
  }
  remaining_gas := gas - 1;
  var todo_covers := single_step_halting_covers(radius, program);
  var done_covers := {};

  while remaining_gas > 0 && |todo_covers| != 0
  invariant forall cover | cover in done_covers + todo_covers :: segment_radius(radius, cover)
  invariant forall state: MachineState | state.position == 0 && machine_step(program, state).Halt? :: config_set_covers(todo_covers + done_covers, state)
  invariant forall cover | cover in done_covers :: covers_previous(program, cover, done_covers + todo_covers)
  invariant forall cover | cover in done_covers :: !can_match_initial(cover)
  {
    remaining_gas := remaining_gas - 1;

    var cover :| cover in todo_covers;

    if can_match_initial(cover) {
      return false, remaining_gas;
    }

    done_covers := done_covers + { cover };
    var new_covers := cover_all_inputs(radius, program, cover);
    todo_covers := todo_covers + new_covers;

    todo_covers := todo_covers - done_covers;

    forall each_cover | each_cover in done_covers
    ensures covers_previous(program, each_cover, done_covers + todo_covers)
    {
      if each_cover == cover {
        assert covers_previous(program, each_cover, new_covers);
      } else {
        assert covers_previous(program, each_cover, done_covers + todo_covers);
      }
    }
  }

  if |todo_covers| != 0 {
    return false, remaining_gas;
  }

  // We now need a complex lemma to prove that this works.
  // It's a bit tricky.

  assert forall cover | cover in done_covers :: segment_radius(radius, cover);
  assert forall state: MachineState | state.position == 0 && machine_step(program, state).Halt? :: config_set_covers(done_covers, state);
  assert forall cover | cover in done_covers :: covers_previous(program, cover, done_covers);
  assert forall cover | cover in done_covers :: !can_match_initial(cover);

  prove_no_terminate(program, done_covers);

  return true, remaining_gas;
}




lemma nonterm_makes_initial_covered_n_shift(program: Program, done_covers: set<HaltingSegment>, n: nat, shift: int)
requires forall state: MachineState | state.position == 0 && machine_step(program, state).Halt? :: config_set_covers(done_covers, state);
requires forall cover | cover in done_covers :: covers_previous(program, cover, done_covers);
ensures config_set_covers(done_covers, translate_state(INITIAL_STATE, shift))
requires !machine_iter_n(program, n).Halt?
requires config_set_covers(done_covers, translate_state(machine_iter_n(program, n).next_state, shift))
{
  if n == 0 {
    return;
  }

  // We must go backwards and forwards.
  assert config_set_covers(done_covers, translate_state(machine_iter_n(program, n).next_state, shift));
  var done_cover_for_translated :| done_cover_for_translated in done_covers && config_matches_state(done_cover_for_translated, translate_state(machine_iter_n(program, n).next_state, shift));

  assert !machine_iter_n(program, n-1).Halt?;
  assert !machine_step(program, translate_state(machine_iter_n(program, n-1).next_state, shift)).Halt?;

  assert translate_state(machine_step(program, machine_iter_n(program, n-1).next_state).next_state, shift) == translate_state(machine_iter_n(program, n).next_state, shift);
  step_or_translate_commute(program, machine_iter_n(program, n-1).next_state, shift);
  assert machine_step(program, translate_state(machine_iter_n(program, n-1).next_state, shift)).next_state == translate_state(machine_iter_n(program, n).next_state, shift);

  nonterm_makes_initial_covered_n_shift(program, done_covers, n-1, shift);
}

lemma step_or_translate_commute(program: Program, state: MachineState, amount: int)
requires !machine_step(program, state).Halt?
ensures !machine_step(program, translate_state(state, amount)).Halt?
ensures machine_step(program, translate_state(state, amount)).next_state == translate_state(machine_step(program, state).next_state, amount)
{
  var state_tr := translate_state(state, amount);
  var state_ev := machine_step(program, state).next_state;

  var state_tr_ev := machine_step(program, state_tr).next_state;
  var state_ev_tr := translate_state(state_ev, amount);

  assert state_tr_ev.color == state_ev_tr.color;
  assert state_tr_ev.position == state_ev_tr.position;
  assert forall k: int :: k in state_ev_tr.tape <==> k-amount in state_ev.tape ;
  assert state_tr_ev.tape == state_ev_tr.tape;
  assert state_tr_ev == state_ev_tr;
}

lemma nonterm_makes_initial_covered_n(program: Program, done_covers: set<HaltingSegment>, n: nat)
requires forall state: MachineState | state.position == 0 && machine_step(program, state).Halt? :: config_set_covers(done_covers, state);
requires forall cover | cover in done_covers :: covers_previous(program, cover, done_covers);
ensures exists shift: int :: config_set_covers(done_covers, translate_state(INITIAL_STATE, shift))
requires machine_iter_n(program, n).Halt?
{
  assert n >= 1;
  if machine_iter_n(program, n-1).Halt? {
    // Need to find the first halting state.
    nonterm_makes_initial_covered_n(program, done_covers, n-1);
    return;
  }

  var last := machine_iter_n(program, n-1).next_state;
  var last_fixed := translate_state(last, -last.position);
  assert config_set_covers(done_covers, last_fixed);

  // Claim: we can follow this backward to the beginning.

  nonterm_makes_initial_covered_n_shift(program, done_covers, n-1, -last.position);
}

lemma nonterm_makes_initial_covered(program: Program, done_covers: set<HaltingSegment>)
requires forall state: MachineState | state.position == 0 && machine_step(program, state).Halt? :: config_set_covers(done_covers, state);
requires forall cover | cover in done_covers :: covers_previous(program, cover, done_covers);
ensures exists shift: int :: config_set_covers(done_covers, translate_state(INITIAL_STATE, shift))
requires program_eventually_halts(program)
{
  var n :| machine_iter_n(program, n).Halt?;
  nonterm_makes_initial_covered_n(program, done_covers, n);
}


lemma prove_no_terminate(program: Program, done_covers: set<HaltingSegment>)
// requires forall cover | cover in done_covers :: segment_radius(radius, cover);
requires forall state: MachineState | state.position == 0 && machine_step(program, state).Halt? :: config_set_covers(done_covers, state);
requires forall cover | cover in done_covers :: covers_previous(program, cover, done_covers);
requires forall cover | cover in done_covers :: !can_match_initial(cover);
ensures !program_eventually_halts(program)
{
  if program_eventually_halts(program) {
    nonterm_makes_initial_covered(program, done_covers);
  }
}

function method translate_state(state: MachineState, amount: int): MachineState
{
  MachineState(
    tape := set k | k in state.tape :: k + amount,
    position := state.position + amount,
    color := state.color
  )
}


function translate_map_keys(m: map<int, Bit>, amount: int): map<int, Bit>
{
  if |m| == 0 then m
  else var k :| k in m; translate_map_keys(map k2 | k2 in m && k2 != k :: m[k2], amount)[k + amount := m[k]]
}
lemma translate_map_key(m: map<int, Bit>, amount: int, original_key: int)
requires original_key + amount in translate_map_keys(m, amount);
ensures (original_key in m <==> original_key + amount in translate_map_keys(m, amount))
ensures (original_key in m ==> m[original_key] == translate_map_keys(m, amount)[original_key + amount])
ensures (original_key + amount in translate_map_keys(m, amount) ==> m[original_key] == translate_map_keys(m, amount)[original_key + amount])
{ 

}


function translate_segment(config: HaltingSegment, amount: int): HaltingSegment
{
  HaltingSegment(
    position := match config.position {
      case At(x) => At(x + amount)
      case Before(x) => Before(x + amount)
      case After(x) => After(x + amount)
    },
    color := config.color,
    pattern := translate_map_keys(config.pattern, amount)
  )
}

lemma prove_state_translate_get_tape(state: MachineState, amount: int)
ensures forall index :: get_tape(translate_state(state, amount), index + amount) == get_tape(state, index)
{

}

lemma translation_undo_state(state: MachineState, amount: int)
ensures translate_state(translate_state(state, amount), -amount) == state
{
  var forward := translate_state(state, amount);
  var backward := translate_state(forward, -amount);
  assert backward.position == state.position;
  assert backward.color == state.color;

  forall k
  ensures k in state.tape <==> k in backward.tape {
    assert k in backward.tape <==> k + amount in forward.tape;
  }
  assert backward.tape == state.tape;
  assert backward == state;
}

lemma translation_preserves_matching(config: HaltingSegment, state: MachineState, amount: int,
// For explicitness, you must pass these in:
then_config: HaltingSegment,
then_state: MachineState
)
requires config_matches_state(config, state);
ensures config_matches_state(translate_segment(config, amount), translate_state(state, amount))

requires then_config == translate_segment(config, amount)
requires then_state == translate_state(state, amount)
{
  var translated_config := translate_segment(config, amount);
  var translated_state := translate_state(state, amount);
  assert translated_config.color == translated_state.color;
  assert pos_matches(translated_config.position, translated_state.position);
  prove_state_translate_get_tape(state, amount);
  forall index | index in translated_config.pattern
  ensures get_tape(translated_state, index) == translated_config.pattern[index]
  {
    var old_index := index - amount;
    assert get_tape(translated_state, index) == get_tape(state, index - amount);
    translate_map_key(config.pattern, amount, old_index);
    assert translated_config.pattern[old_index + amount] == config.pattern[old_index];
  }
}


method decide_initial_segment(program: Program, gas: nat)
returns (loops_forever: bool)
ensures loops_forever ==> !program_eventually_halts(program)
{
  var radius := 1;
  var remaining_gas := gas;
  while remaining_gas > 0 {
    var does_loop, leftover_gas := decide_initial_segment_fixed_radius(radius, program, remaining_gas);
    assert leftover_gas < remaining_gas;
    remaining_gas := leftover_gas;
    if does_loop {
      return true;
    }
    radius := radius + 1;
  }
  return false;
}