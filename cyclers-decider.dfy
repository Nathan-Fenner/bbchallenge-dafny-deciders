// A bit is either 0 or 1.
datatype Bit = B0 | B1
// A tape is a cons-list of bits. InfiniteZeros conceptually represents an infinite sequence of 0s.
// Hence, it is a "half-infinite" tape of bits, describing "one side" of the Turing machine
// configuration.
// We use the name 'RawTape' here since these are not normalized; we want to avoid
// having tapes like "010..." since there is no difference between "010..." and "01...".
datatype RawTape = InfiniteZeros | Cons(head: Bit, tail: RawTape)

// A tape is "good" if it doesn't end in a B0 bit.
// Therefore, it must be empty, or if its head is B0, the next one is not empty.
// Additionally, its tail must be "good".
predicate good_tape(r: RawTape) {
  r == InfiniteZeros || (good_tape(r.tail) && (r.head == B0 ==> r.tail != InfiniteZeros))
}

// A `Tape` is any `RawTape` which does not end in a B0.
// This ensures that each Tape represents a genuinely different state.
type Tape = t: RawTape | good_tape(t) witness InfiniteZeros

// 'cons' adds a bit to the beginning of the provided tape.
// If the tape was InfiniteZeros then this has no effect.
// Otherwise, it just uses the `Cons` constructor.
function method cons(b: Bit, t: Tape): Tape {
  if b == B0 && t == InfiniteZeros then InfiniteZeros else Cons(b, t)
}

// Bits is just a convenient wrapper for the `uncons` function's return type.
datatype Bits = Bits(head: Bit, tail: Tape)
// uncons removes a bit from the tape, returning both the bit and the remainder
// of the tape.
function method uncons(t: Tape): Bits {
  if t == InfiniteZeros then Bits(B0, InfiniteZeros) else Bits(t.head, t.tail)
}

// This lemma verifies that cons and uncons are "opposites", so that adding
// and then removing a bit leaves the tape in its initial state,
// and that removing and then adding back a bit leaves the tape in its
// initial state.
//
// This lemma is not actually used below, since Dafny can prove it automatically.
lemma cons_uncons(tape: Tape)
ensures uncons(cons(B0, tape)).tail == tape
ensures uncons(cons(B1, tape)).tail == tape
ensures cons(uncons(tape).head, uncons(tape).tail) == tape {
}

// Because the word "state" would otherwise be overloaded, the 5 "states" for the
// TM are instead called "Colors": CA, CB, CC, CD, CE, with the "C" standing for "Color".
datatype Color = CA | CB | CC | CD | CE

// A machine state describes the machine's color and the tape that it finds itself in.
// Conceptually, the machine head is over the "head_symbol" bit and about to process that
// bit. The `left` and `right` fields describe the half-infinite tape to the left of the
// head and to the right.
//
// Note that this representation avoids explicitly representing the TM's location in space.
// This simplifies the logic and presentation below.
datatype MachineState = MachineState(color: Color, head_symbol: Bit, left: Tape, right: Tape)

// The TM can move left or right at each step.
datatype Direction = L | R

// An action describes what the machine might be told to do by a program:
// - write the given bit
// - switch to the given color
// - move one step in given direction
datatype Action = Action(write: Bit, new_color: Color, move: Direction)

// machine_step_action applies the given action to the machine state.
function method machine_step_action(m: MachineState, action: Action): MachineState {
  match action.move {
    case L => MachineState(
      // The new color comes from the action.
      color := action.new_color,
      // The next symbol to be read comes from the first symbol in the left tape.
      head_symbol := uncons(m.left).head,
      // We remove one symbol from the left tape.
      left := uncons(m.left).tail,
      // The written bit ends up at the beginning of the right tape.
      right := cons(action.write, m.right)
    )
    // This case is identical to the case above, but with left/right reversed.
    case R => MachineState(
      // The new color comes from the action.
      color := action.new_color,
      // The next symbol to be read comes from the first symbol in the right tape.
      head_symbol := uncons(m.right).head,
      // We remove one symbol from the right tape.
      right := uncons(m.right).tail,
      // The written bit ends up at the beginning of the left tape.
      left := cons(action.write, m.left)
    )
  }
}

// All TMs are assumed to begin in the color CA, on a tape of all zeros.
const initial: MachineState := MachineState(Color.CA, Bit.B0, InfiniteZeros, InfiniteZeros)

// `ProgramStepInput` is a structure containing the information needed to find out what
// action should be applied next in a TM program.
datatype ProgramStepInput = ProgramStepInput(head: Bit, color: Color)

// A program is a (partial) mapping from inputs to actions, describing what the TM
// should do next in each situation.
//
// If a transition is absent, then it is assumed to be a halting transition.
type Program = map<ProgramStepInput, Action>

// A `MachineStep` either is either `Halt` if no transition for the current state
// exists, or it is NextMachine and holds that next state.
datatype MachineStep = NextMachine(next_state: MachineState) | Halt

// machine_step causes the provided state to step forward once according to the
// provided program. The output will either be the next state, or Halt if there
// is no configured transition.
function method machine_step(program: Program, m: MachineState): MachineStep {
  if ProgramStepInput(m.head_symbol, m.color) in program
    then NextMachine(machine_step_action(m, program[ProgramStepInput(m.head_symbol, m.color)]))
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
  machine_step_n(program, initial, n)
}

// By definition, a machine halts if there's a step such that at that point, it halts.
predicate program_eventually_halts(program: Program) {
  exists n :: n >= 0 && machine_iter_n(program, n).Halt?
}

predicate program_loops_forever(program: Program) {
  !program_eventually_halts(program)
}

//
//
//
// Everything below this point is for the algorithm.
//
//
//

// This is a verified implementation of the Cyclers decider.
// If this function returns true, then it has detected that the TM contains a cycle.
// If it returns false, then no cycle has been detected yet. Either the time_limit
// needs to be raised, or it cannot accurately classify the provided program.
method cyclers_decider(program: Program, time_limit: nat)
returns (finds_loop: bool)
ensures finds_loop ==> program_loops_forever(program) {
  // Dafny requires verification that this method terminates. We use this 'gas'
  // to track how many iterations remain.
  var gas := time_limit;
  // This method maintains a set of visited states, with an 
  var visited: set<MachineState> := {};

  // We track the current state of the machine in this variable.
  var current_state := initial;

  while gas > 0 && current_state !in visited
  // The initial configuration must either be visited or is our current state, at all times.
  invariant initial in visited || current_state == initial
  // Each state in the visited set must not halt in one step...
  invariant forall m :: m in visited ==> !machine_step(program, m).Halt?
  // and the successor must either also be in the visited set, or is the current state.
  invariant forall m :: m in visited ==> machine_step(program, m).next_state in visited || machine_step(program, m).next_state == current_state {
    // Decrease the amount of gas we have left (ensures that this decider terminates).
    gas := gas - 1;
    // Try to step the current state forward:
    match machine_step(program, current_state) {
      case Halt => {
        // If it halted, then we know that this program actually halts.
        // So verification of cycling immediately fails.
        return false;
      }
      case NextMachine(follow) => {
        // We have a following state.
        // It is now possible to add the current state to the visited set,
        // and update the current state.
        visited := visited + {current_state};
        current_state := follow;
      }
    }
  }
  if gas == 0 {
    // If we ran out of gas, then analysis is not done.
    // We have not yet found a cycle, so we return false.
    return false;
  }


  // These are slightly stronger versions of the loop invariant.
  // We no longer need to reference current_state.
  assert forall m :: m in visited ==> !machine_step(program, m).Halt?;
  // and the successor must either also be in the visited set, or is the current state.
  assert forall m :: m in visited ==> machine_step(program, m).next_state in visited;

  // At this point, we can now prove that the program never halts.
  // We take an arbitrary natural number, and prove that the corresponding
  // state doesn't halt in one step. This means that no reachable state ever
  // halts.
  forall n: nat
  ensures !machine_iter_n(program, n).Halt?
  {
    // To prove this, we just have to use this lemma, which applies
    // induction to each n.
    visited_set_includes_each_iter(program, visited, n);
  }
}



// visited_set_includes_each_iter proves that `machine_iter_n(program, n)` has a successor.
// It does this via induction, relying on the 'visited' set being complete.
lemma visited_set_includes_each_iter(program: Program, visited: set<MachineState>, n: nat)
// We need for the visited set to include the initial state.
requires initial in visited
// We need for each machine in the visited set to have a successor.
requires forall m :: m in visited ==> !machine_step(program, m).Halt?
// We need for each successor of a visited machine to also be visited.
requires forall m :: m in visited ==> machine_step(program, m).next_state in visited
// And if we have all of the above, we can prove that the current machine n doesn't halt.
ensures !machine_iter_n(program, n).Halt?
// We also need the following, for induction: that the successor of the current state is
// also visited.
ensures machine_iter_n(program, n).next_state in visited
{
  if n == 0 {
    // The initial state is visited, so we are done.
    assert !machine_iter_n(program, n).Halt?;
  } else {
    // First, apply induction, by recursively calling this lemma on n-1.
    visited_set_includes_each_iter(program, visited, n-1);
    // Now, the conclusion follows immediately from the induction hypothesis
    // and the lemma's requirements.
    assert !machine_iter_n(program, n).Halt?;
  }
}

method Main() {
  // This is the current candidate for BB(5):
  // 1RB1LC_1RC1RB_1RD0LE_1LA1LD_---0LA
  // It runs for 47,176,870 steps and then halts.
  var busy_beaver_candidate: Program := map[
    ProgramStepInput(B0, CA) := Action(B1, CB, R),
    ProgramStepInput(B1, CA) := Action(B1, CC, L),
    
    ProgramStepInput(B0, CB) := Action(B1, CC, R),
    ProgramStepInput(B1, CB) := Action(B1, CB, R),
    
    ProgramStepInput(B0, CC) := Action(B1, CD, R),
    ProgramStepInput(B1, CC) := Action(B0, CE, L),
    
    ProgramStepInput(B0, CD) := Action(B1, CA, L),
    ProgramStepInput(B1, CD) := Action(B1, CD, L),
    
    // ProgramStepInput(B0, CE) := Action(B1, CZ, R), // Halt
    ProgramStepInput(B1, CE) := Action(B0, CA, L)
  ];

  print busy_beaver_candidate;
  print "\n";

  var step_count;
  var result;
  
  step_count := 47_176_869;
  print "Run for ";
  print step_count;
  print " steps...\n-> halt? ";
  result := machine_step_iterative(busy_beaver_candidate, initial, step_count);
  print result.Halt?;
  print "\n";

  step_count := 47_176_870;
  print "Run for ";
  print step_count;
  print " steps...\n-> halt? ";
  result := machine_step_iterative(busy_beaver_candidate, initial, step_count);
  print result.Halt?;
  print "\n";
}