# rs-halting-segment

This is a Rust re-implementation of the Dafny file `halting-segment.dfy`, which is itself a reimplementation of the [Halting Segment decider](https://discuss.bbchallenge.org/t/decider-halting-segment/75) ([repo](https://github.com/Iijil1/Iijils-bb-challenge/blob/main/halting-segment/main.go)).

The Dafny implementation is fully verified, culminating in the specification:

```
method decide_initial_segment(program: Program, gas: nat)
returns (loops_forever: bool)
ensures loops_forever ==> !program_eventually_halts(program)
{
  ...
}
```

so that if the `decide_initial_segment` function is computed and returns `true`, the TM corresponding to `program` must really never halt.

The Dafny code works, but is very slow. Therefore, I manually translated this code to this Rust implementation in a line-by-line fashion.
Afterwards, I made a few optimizations to run even faster (for example, replacing the `Input` with a contiguous array instead of a hashmap).
