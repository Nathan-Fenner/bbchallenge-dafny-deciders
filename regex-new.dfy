datatype Bit = B0 | B1
datatype Reg = Cat(items: seq<Reg>) | Lit(Bit)| Plus(rep: Reg) | Alt(first: Reg, second: Reg) | Never | Any

function method cat(a: Reg, b: Reg): Reg {
  match (a, b) {
    case (Cat(alist), Cat(blist)) => Cat(alist + blist)
    case (a, Cat(blist)) => Cat([a] + blist)
    case (Cat(alist), b) => Cat(alist + [b])
    case (Never, b) => Never
    case (a, Never) => Never
    case (Any, Any) => Any
    case _ => Cat([a, b])
  }
}

lemma catenating_matches_single(t: seq<Bit>, r: Reg)
requires matches(t, r)
ensures matches(t, Cat([r]))
{
  var n := |t|;
  assert t == t[..n];
  assert matches(t[..n], r);
  assert matches(t[n..], Cat([]));
}

lemma catenating_matches_single_rev(t: seq<Bit>, r: Reg)
requires matches(t, Cat([r]))
ensures matches(t, r)
{
  var n := |t|;
  assert t == t[..n];
  assert matches(t[..n], r);
  assert matches(t[n..], Cat([]));
}

lemma cat2_split(tape: seq<Bit>, a: Reg, b: Reg)
requires matches(tape, Cat([a, b]))
ensures exists n :: 0 <= n <= |tape| && matches(tape[..n], a) && matches(tape[n..], b)
{
  var n1 :| 0 <= n1 <= |tape| && matches(tape[..n1], a) && matches(tape[n1..], Cat([b]));
  var rest := tape[n1..];
  assert matches(rest, Cat([b]));
  var n2 :| 0 <= n2 <= |rest| && matches(rest[..n2], b) && matches(rest[n2..], Cat([]));
  assert rest[n2..] == [];
  assert rest[..n2] == rest;
  assert matches(rest, b);
  assert matches(rest[n2..], Cat([]));
  assert matches(tape[n1..], b);
}

lemma cat_cat_cat_induction(tape: seq<Bit>, alist: seq<Reg>, blist: seq<Reg>)
decreases |alist|
requires matches(tape, Cat([Cat(alist), Cat(blist)]))
ensures matches(tape, Cat(alist + blist))
{
  cat2_split(tape, Cat(alist), Cat(blist));
  var n :| 0 <= n <= |tape| && matches(tape[..n], Cat(alist)) && matches(tape[n..], Cat(blist));
  if |alist| == 0 {
    assert alist + blist == blist;
    assert matches(tape, Cat(alist + blist));
    return;
  }

  var tape_a := tape[..n];
  assert matches(tape_a, Cat(alist));
  var n_a :| 0 <= n_a <= |tape_a| && matches(tape_a[..n_a], alist[0]) && matches(tape_a[n_a..], Cat(alist[1..]));

  catenating_matches_cat(tape_a[n_a..], tape[n..], Cat(alist[1..]), Cat(blist));
  assert matches(tape_a[n_a..] + tape[n..], Cat([Cat(alist[1..]), Cat(blist)]));
  cat_cat_cat_induction(tape_a[n_a..] + tape[n..], alist[1..], blist);
  assert matches(tape_a[n_a..] + tape[n..], Cat(alist[1..] + blist));

  catenating_matches_cat(tape_a[..n_a], tape_a[n_a..] + tape[n..], alist[0], Cat(alist[1..] + blist));
  assert matches(tape_a[..n_a] + (tape_a[n_a..] + tape[n..]), Cat([alist[0], Cat(alist[1..] + blist)]));
  assert tape_a[..n_a] + (tape_a[n_a..] + tape[n..]) == tape;
  assert matches(tape, Cat([alist[0], Cat(alist[1..] + blist)]));
  cat2_split(tape, alist[0], Cat(alist[1..] + blist));
  var nf :| 0 <= nf <= |tape| && matches(tape[..nf], alist[0]) && matches(tape[nf..], Cat(alist[1..] + blist));
  assert matches(tape, Cat([alist[0]] + (alist[1..] + blist)));
  assert [alist[0]] + (alist[1..] + blist) == alist + blist;
  assert matches(tape, Cat(alist + blist));
}

lemma cat_r_cat_induction(tape: seq<Bit>, a: Reg, blist: seq<Reg>)
requires matches(tape, Cat([a, Cat(blist)]))
ensures matches(tape, Cat([a] + blist))
{
  cat2_split(tape, a, Cat(blist));
  var n :| 0 <= n <= |tape| && matches(tape[..n], a) && matches(tape[n..], Cat(blist));
}

lemma cat_cat_r_induction(tape: seq<Bit>, alist: seq<Reg>, b: Reg)
requires matches(tape, Cat([Cat(alist), b]))
ensures matches(tape, Cat(alist + [b]))
{
  cat2_split(tape, Cat(alist), b);
  var n :| 0 <= n <= |tape| && matches(tape[..n], Cat(alist)) && matches(tape[n..], b);
  catenating_matches_single(tape[n..], b);
  assert matches(tape[n..], Cat([b]));
  catenating_matches_cat(tape[..n], tape[n..], Cat(alist), Cat([b]));
  assert tape[..n] + tape[n..] == tape;
  assert matches(tape, Cat([Cat(alist), Cat([b])]));
  cat_cat_cat_induction(tape, alist, [b]);
}

lemma cat_works(a: Reg, b: Reg)
ensures forall tape: seq<Bit> | matches(tape, Cat([a, b])) :: matches(tape, cat(a, b))
{
  match (a, b) {
    case (Cat(alist), Cat(blist)) => {
      forall tape: seq<Bit> | matches(tape, Cat([a, b]))
      ensures matches(tape, cat(a, b))
      {
        cat_cat_cat_induction(tape, alist, blist);
        assert matches(tape, Cat(alist + blist));
      }
    }
    case (a, Cat(blist)) => {
      forall tape: seq<Bit> | matches(tape, Cat([a, b]))
      ensures matches(tape, cat(a, b))
      {
        cat_r_cat_induction(tape, a, blist);
      }
    }
    case (Cat(alist), b) => {
      forall tape: seq<Bit> | matches(tape, Cat([a, b]))
      ensures matches(tape, cat(a, b))
      {
        cat_cat_r_induction(tape, alist, b);
      }
    }
    case (Never, b) => {
    }
    case (a, Never) => {
      forall tape: seq<Bit> | matches(tape, Cat([a, b]))
      ensures matches(tape, cat(a, b))
      {
        var r := Cat([a, b]);
        assert a == r.items[0];
        assert Cat([b]) == Cat(r.items[1..]);
        var n :| 0 <= n <= |tape| && matches(tape[..n], a) && matches(tape[n..], Cat([b]));
        assert matches(tape[n..], Cat([b]));
        catenating_matches_single(tape[n..], b);
      }
    }
    case (Any, Any) => {
      // ...
    }
    case _ => {
      assert cat(a, b) == Cat([a, b]);
    }
  }
}

function method alt(a: Reg, b: Reg): Reg {
  if a == b then a else
  if a == Plus(b) then a else
  if b == Plus(a) then b else
  match (a, b) {
    case (Any, _) => Any
    case (_, Any) => Any
    case (Never, b) => b
    case (a, Never) => a
    case _ => Alt(a, b)
  }
}

lemma alt_works(a: Reg, b: Reg)
ensures forall t: seq<Bit> :: matches(t, Alt(a, b)) ==> matches(t, alt(a, b))
{
}

function reg_sum_size(rs: seq<Reg>): nat {
  if rs == [] then 1 else reg_size(rs[0]) + 1 + reg_sum_size(rs[1..])
}

function reg_size(r: Reg): nat {
  match r {
  case Never => 1
  case Cat(list) => reg_sum_size(list)
  case Alt(a, b) => 1 + reg_size(a) + reg_size(b)
  case Lit(_) => 1
  case Plus(r) => 1 + reg_size(r)
  case Any => 1
  }
}

predicate matches(s: seq<Bit>, r: Reg)
decreases reg_size(r), |s|
{
  match r {
  case Never => false
  case Cat(list) => if list == []
    then s == []
    else
      assert reg_size(list[0]) < reg_size(r);
      assert reg_size(Cat(list[1..])) < reg_size(r);
      exists n :: 0 <= n <= |s| && matches(s[..n], list[0]) && matches(s[n..], Cat(list[1..]))
  case Alt(a, b) => matches(s, a) || matches(s, b)
  case Lit(b) => s == [b]
  case Plus(r) => matches(s, r) || exists n :: 1 <= n <= |s| && matches(s[..n], r) && matches(s[n..], Plus(r))
  case Any => true
  }
}



lemma catenating_matches_cat(ta: seq<Bit>, tb: seq<Bit>, a: Reg, b: Reg)
requires matches(ta, a)
requires matches(tb, b)
ensures matches(ta + tb, Cat([a, b]))
{
  var t := ta + tb;
  var n := |ta|;
  assert matches(t[..n], a);
  var trail := t[n..];
  assert matches(trail, b);
  catenating_matches_single(trail, b);
  assert matches(trail, Cat([b]));
  assert matches(ta + tb, Cat([a, b]));
}

datatype Deriv = Deriv(can_be_empty: bool, after_0: Reg, after_1: Reg)

method deriv_of(r: Reg) returns (result: Deriv)
decreases reg_size(r)
ensures matches([], r) <==> result.can_be_empty
ensures forall t: seq<Bit> | t != [] && t[0] == B0 && matches(t, r) :: matches(t[1..], result.after_0)
ensures forall t: seq<Bit> | t != [] && t[0] == B1 && matches(t, r) :: matches(t[1..], result.after_1)
{
  match r {
    case Never => {
      return Deriv(can_be_empty := false, after_0 := Never, after_1 := Never);
    }
    case Any => {
      return Deriv(
        can_be_empty := true,
        after_0 := Any,
        after_1 := Any
      );
    }
    case Lit(b) => {
      return Deriv(can_be_empty := false, after_0 := if b == B0 then Cat([]) else Never, after_1 := if b == B1 then Cat([]) else Never);
    }
    case Plus(rep) => {
      assert reg_size(rep) < reg_size(r);
      var drep := deriv_of(rep);
      result := Deriv(
        can_be_empty := drep.can_be_empty,
        after_0 := Alt(drep.after_0, cat(drep.after_0, Plus(rep))),
        after_1 := Alt(drep.after_1, cat(drep.after_1, Plus(rep)))
      );
      cat_works(drep.after_0, Plus(rep));
      cat_works(drep.after_1, Plus(rep));
      assert matches([], r) <==> result.can_be_empty;
      forall t: seq<Bit> | t != [] && t[0] == B0 && matches(t, r)
      ensures matches(t[1..], result.after_0)
      {
        if matches(t, rep) {
          // Easy case.
          assert matches(t[1..], result.after_0);
        } else {
          var n :| 1 <= n <= |t| && matches(t[..n], rep) && matches(t[n..], Plus(rep));
          var t_left := t[..n];
          var t_right := t[n..];
          assert matches(t_left[1..], drep.after_0);
          assert matches(t_right, Plus(rep));
          catenating_matches_cat(t_left[1..], t_right, drep.after_0, Plus(rep));
          assert matches(t_left[1..] + t_right, Cat([drep.after_0, Plus(rep)]));
          assert t_left[1..] + t_right == t[1..];
          assert matches(t[1..], result.after_0);
        }
      }
      forall t: seq<Bit> | t != [] && t[0] == B1 && matches(t, r)
      ensures matches(t[1..], result.after_1)
      {
        if matches(t, rep) {
          // Easy case.
          assert matches(t[1..], result.after_1);
        } else {
          var n :| 1 <= n <= |t| && matches(t[..n], rep) && matches(t[n..], Plus(rep));
          var t_left := t[..n];
          var t_right := t[n..];
          assert matches(t_left[1..], drep.after_1);
          assert matches(t_right, Plus(rep));
          catenating_matches_cat(t_left[1..], t_right, drep.after_1, Plus(rep));
          assert matches(t_left[1..] + t_right, Cat([drep.after_1, Plus(rep)]));
          assert t_left[1..] + t_right == t[1..];
          assert matches(t[1..], result.after_1);
        }
      }
      return result;
    }
    case Alt(a, b) => {
      var da := deriv_of(a);
      var db := deriv_of(b);
      return Deriv(
        can_be_empty := da.can_be_empty || db.can_be_empty,
        after_0 := Alt(da.after_0, db.after_0),
        after_1 := Alt(da.after_1, db.after_1)
      );
    }
    case Cat(list) => {
      if list == [] {
        return Deriv(
          can_be_empty := true,
          after_0 := Never,
          after_1 := Never
        );
      }

      var a := list[0];
      var b := Cat(list[1..]);
      assert reg_size(a) < reg_size(r);
      var da := deriv_of(a);
      assert reg_size(b) < reg_size(r);
      var db := deriv_of(b);
      if da.can_be_empty {
        result := Deriv(
          can_be_empty := db.can_be_empty,
          after_0 := alt(db.after_0, cat(da.after_0, b)),
          after_1 := alt(db.after_1, cat(da.after_1, b))
        );

        cat_works(da.after_0, b);
        cat_works(da.after_1, b);

        if result.can_be_empty {
          assert matches([], a);
          assert matches([], b);
          // Very silly, but needed to expand:
          var t: seq<Bit> := [];
          var n := 0;
          assert 0 <= n <= |t| && matches(t[..n], a) && matches(t[n..], b);
          assert matches([], r);
        } else {
          assert !matches([], r);
        }

        forall t: seq<Bit> | t != [] && t[0] == B0 && matches(t, r)
        ensures matches(t[1..], result.after_0) {
          var n :| 0 <= n <= |t| && matches(t[..n], a) && matches(t[n..], b);
          if n == 0 {
            // Automatic.
            assert matches(t[1..], result.after_0);
          } else {
            assert n >= 1;
            var t_tail := t[1..];
            assert t_tail[..n-1] == t[1..n];
            assert t_tail[n-1..] == t[n..];
            assert matches(t_tail[..n-1], da.after_0);
            assert matches(t_tail[n-1..], b);
            cat_works(da.after_0, b);
            catenating_matches_cat(t_tail[..n-1], t_tail[n-1..], da.after_0, b);
            assert t_tail[..n-1] + t_tail[n-1..] == t_tail;
            assert matches(t[1..], cat(da.after_0, b));
            assert matches(t[1..], result.after_0);
          }
        }
        forall t: seq<Bit> | t != [] && t[0] == B1 && matches(t, r)
        ensures matches(t[1..], result.after_1) {
          var n :| 0 <= n <= |t| && matches(t[..n], a) && matches(t[n..], b);
          if n == 0 {
            // Automatic.
            assert matches(t[1..], result.after_1);
          } else {
            assert n >= 1;
            var t_tail := t[1..];
            assert t_tail[..n-1] == t[1..n];
            assert t_tail[n-1..] == t[n..];
            assert matches(t_tail[..n-1], da.after_1);
            assert matches(t_tail[n-1..], b);
            cat_works(da.after_1, b);
            catenating_matches_cat(t_tail[..n-1], t_tail[n-1..], da.after_1, b);
            assert t_tail[..n-1] + t_tail[n-1..] == t_tail;
            assert matches(t[1..], cat(da.after_1, b));
            assert matches(t[1..], result.after_1);
          }
        }
        return result;
      } else {
        result := Deriv(
          can_be_empty := false,
          after_0 := cat(da.after_0, b),
          after_1 := cat(da.after_1, b)
        );
        cat_works(da.after_0, b);
        cat_works(da.after_1, b);
        forall t: seq<Bit> | t != [] && t[0] == B0 && matches(t, r)
        ensures matches(t[1..], result.after_0) {
          var n :| 0 <= n <= |t| && matches(t[..n], a) && matches(t[n..], b);
          assert n >= 1;
          var t_tail := t[1..];
          assert t_tail[..n-1] == t[1..n];
          assert t_tail[n-1..] == t[n..];
          assert matches(t_tail[..n-1], da.after_0);
          assert matches(t_tail[n-1..], b);
          assert t_tail[..n-1] + t_tail[n-1..] == t_tail;
          catenating_matches_cat(t_tail[..n-1], t_tail[n-1..], da.after_0, b);
          assert matches(t[1..], result.after_0);
        }
        forall t: seq<Bit> | t != [] && t[0] == B1 && matches(t, r)
        ensures matches(t[1..], result.after_1) {
          var n :| 0 <= n <= |t| && matches(t[..n], a) && matches(t[n..], b);
          assert n >= 1;
          var t_tail := t[1..];
          assert t_tail[..n-1] == t[1..n];
          assert t_tail[n-1..] == t[n..];
          assert matches(t_tail[..n-1], da.after_1);
          assert t_tail[..n-1] + t_tail[n-1..] == t_tail;
          catenating_matches_cat(t_tail[..n-1], t_tail[n-1..], da.after_1, b);
          assert matches(t_tail[n-1..], b);
        }
        return result;
      }
    }
  }
}




datatype RawHalfTape = HalfTape(initial: seq<Bit>)
type HalfTape = x: RawHalfTape | x.initial == [] || x.initial[|x.initial|-1] == B1
  witness HalfTape([])


function make_zeros(n: nat): seq<Bit>
{
  if n == 0 then [] else [B0] + make_zeros(n-1)
}

lemma make_zeros_works(n: nat)
ensures |make_zeros(n)| == n
ensures forall i :: 0 <= i < n ==> make_zeros(n)[i] == B0
{}

function take_from_tape(tape: HalfTape, n: nat): seq<Bit>
{
  if n <= |tape.initial| then tape.initial[..n]
  else tape.initial + make_zeros(n - |tape.initial|)
}

function drop_from_tape(tape: HalfTape, n: nat): HalfTape {
  if n <= |tape.initial| then HalfTape(initial := tape.initial[n..])
  else HalfTape(initial := [])
}

predicate half_tape_matches(tape: HalfTape, r: Reg)
{
  exists n: nat :: drop_from_tape(tape, n) == HalfTape([]) && matches(take_from_tape(tape, n), r)
}

// This function allows us to move beyond just listing neighborhoods as finite strings.
method generalize_cover(r: Reg) returns (covers: set<Reg>)
ensures forall tape: HalfTape :: half_tape_matches(tape, r) ==> exists cover :: cover in covers && half_tape_matches(tape, cover)
{
  return { r };
}