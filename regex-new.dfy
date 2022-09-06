datatype Bit = B0 | B1
datatype Reg = Cat(first: Reg, second: Reg) | Lit(Bit) | OnlyEmpty | Plus(rep: Reg) | Alt(first: Reg, second: Reg) | Never | Any

function method cat(a: Reg, b: Reg): Reg {
  match (a, b) {
    case (Never, b) => Never
    case (a, Never) => Never
    case (OnlyEmpty, b) => b
    case (a, OnlyEmpty) => a
    case (Any, Any) => Any
    case _ => Cat(a, b)
  }
}

lemma cat_works(a: Reg, b: Reg)
ensures forall tape: seq<Bit> | matches(tape, Cat(a, b)) :: matches(tape, cat(a, b))
{
  match (a, b) {
    case (Never, b) => {
      //
    }
    case (a, Never) => {
      //
    }
    case (OnlyEmpty, b) => {
      //
    }
    case (Any, Any) => {
      // ...
    }
    case (a, OnlyEmpty) => {
      forall tape: seq<Bit> | matches(tape, Cat(a, b)) ensures matches(tape, cat(a, b)) {
        var n :| 0 <= n <= |tape| && matches(tape[..n], a) && matches(tape[n..], b);
        assert n == |tape|;
        assert tape[..n] == tape;
        assert matches(tape, a);
      }
    }
    case _ => {
      assert cat(a, b) == Cat(a, b);
    }
  }
}

function alt(a: Reg, b: Reg): Reg {
  if a == b then a else
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

function reg_size(r: Reg): nat {
  match r {
  case Never => 1
  case Cat(a, b) => 1 + reg_size(a) + reg_size(b)
  case Alt(a, b) => 1 + reg_size(a) + reg_size(b)
  case Lit(_) => 1
  case OnlyEmpty => 1
  case Plus(r) => 1 + reg_size(r)
  case Any => 1
  }
}

predicate matches(s: seq<Bit>, r: Reg)
decreases reg_size(r), |s|
{
  match r {
  case Never => false
  case Cat(a, b) => exists n :: 0 <= n <= |s| && matches(s[..n], a) && matches(s[n..], b)
  case Alt(a, b) => matches(s, a) || matches(s, b)
  case OnlyEmpty => s == []
  case Lit(b) => s == [b]
  case Plus(r) => matches(s, r) || exists n :: 1 <= n <= |s| && matches(s[..n], r) && matches(s[n..], Plus(r))
  case Any => true
  }
}

lemma catenating_matches_cat(ta: seq<Bit>, tb: seq<Bit>, a: Reg, b: Reg)
requires matches(ta, a)
requires matches(tb, b)
ensures matches(ta + tb, Cat(a, b))
{
  var t := ta + tb;
  var n := |ta|;
  assert matches(t[..n], a);
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
    case OnlyEmpty => {
      return Deriv(can_be_empty := true, after_0 := Never, after_1 := Never);
    }
    case Lit(b) => {
      return Deriv(can_be_empty := false, after_0 := if b == B0 then OnlyEmpty else Never, after_1 := if b == B1 then OnlyEmpty else Never);
    }
    case Plus(rep) => {
      assert reg_size(rep) < reg_size(r);
      var drep := deriv_of(rep);
      result := Deriv(
        can_be_empty := drep.can_be_empty,
        after_0 := Alt(drep.after_0, Cat(drep.after_0, Plus(rep))),
        after_1 := Alt(drep.after_1, Cat(drep.after_1, Plus(rep)))
      );
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
          assert matches(t_left[1..] + t_right, Cat(drep.after_0, Plus(rep)));
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
          assert matches(t_left[1..] + t_right, Cat(drep.after_1, Plus(rep)));
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
    case Cat(a, b) => {
      var da := deriv_of(a);
      var db := deriv_of(b);
      if da.can_be_empty {
        result := Deriv(
          can_be_empty := db.can_be_empty,
          after_0 := Alt(db.after_0, Cat(da.after_0, b)),
          after_1 := Alt(db.after_1, Cat(da.after_1, b))
        );

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
          } else {
            assert n >= 1;
            var t_tail := t[1..];
            assert t_tail[..n-1] == t[1..n];
            assert t_tail[n-1..] == t[n..];
            assert matches(t_tail[..n-1], da.after_0);
            assert matches(t_tail[n-1..], b);
          }
        }
        forall t: seq<Bit> | t != [] && t[0] == B1 && matches(t, r)
        ensures matches(t[1..], result.after_1) {
          var n :| 0 <= n <= |t| && matches(t[..n], a) && matches(t[n..], b);
          if n == 0 {
            // Automatic.
          } else {
            assert n >= 1;
            var t_tail := t[1..];
            assert t_tail[..n-1] == t[1..n];
            assert t_tail[n-1..] == t[n..];
            assert matches(t_tail[..n-1], da.after_1);
            assert matches(t_tail[n-1..], b);
          }
        }
        return result;
      } else {
        result := Deriv(
          can_be_empty := false,
          after_0 := Cat(da.after_0, b),
          after_1 := Cat(da.after_1, b)
        );
        forall t: seq<Bit> | t != [] && t[0] == B0 && matches(t, r)
        ensures matches(t[1..], result.after_0) {
          var n :| 0 <= n <= |t| && matches(t[..n], a) && matches(t[n..], b);
          assert n >= 1;
          var t_tail := t[1..];
          assert t_tail[..n-1] == t[1..n];
          assert t_tail[n-1..] == t[n..];
          assert matches(t_tail[..n-1], da.after_0);
          assert matches(t_tail[n-1..], b);
        }
        forall t: seq<Bit> | t != [] && t[0] == B1 && matches(t, r)
        ensures matches(t[1..], result.after_1) {
          var n :| 0 <= n <= |t| && matches(t[..n], a) && matches(t[n..], b);
          assert n >= 1;
          var t_tail := t[1..];
          assert t_tail[..n-1] == t[1..n];
          assert t_tail[n-1..] == t[n..];
          assert matches(t_tail[..n-1], da.after_1);
          assert matches(t_tail[n-1..], b);
        }
        return result;
      }
    }
  }
}
