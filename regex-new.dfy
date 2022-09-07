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

lemma cat_n_split(tape: seq<Bit>, items: seq<Reg>, n: nat)
requires matches(tape, Cat(items))
requires 0 <= n <= |items|
ensures exists split: nat :: 0 <= split <= |tape| && matches(tape[..split], Cat(items[..n])) && matches(tape[split..], Cat(items[n..]))
{
  if n == 0 {
    var split := 0;
    assert split <= |tape|;
    assert matches(tape[..split], Cat(items[..n]));
    assert matches(tape[split..], Cat(items[n..]));
    assert exists split: nat :: 0 <= split <= |tape| && matches(tape[..split], Cat(items[..n])) && matches(tape[split..], Cat(items[n..]));
    return;
  }
  var split_first :| 0 <= split_first <= |tape| && matches(tape[..split_first], items[0]) && matches(tape[split_first..], Cat(items[1..]));
  cat_n_split(tape[split_first..], items[1..], n-1);
  var split_rest :| 0 <= split_rest <= |tape[split_first..]|
    && matches(tape[split_first..][..split_rest], Cat(items[1..][..n-1]))
    && matches(tape[split_first..][split_rest..], Cat(items[1..][n-1..]))
  ;
  assert tape[..split_first] + tape[split_first..][..split_rest] == tape[..split_first + split_rest];
  catenating_matches_cat(tape[..split_first], tape[split_first..][..split_rest], items[0], Cat(items[1..][..n-1]));
  assert matches(tape[..split_first + split_rest], Cat([items[0], Cat(items[1..][..n-1])]));
  assert items[1..][..n-1] == items[1..n];
  assert matches(tape[..split_first + split_rest], Cat([items[0], Cat(items[1..n])]));
  cat_r_cat_induction(tape[..split_first + split_rest], items[0], items[1..n]);
  assert matches(tape[..split_first + split_rest], Cat([items[0]] + items[1..n]));
  assert [items[0]] + items[1..n] == items[..n];
  assert matches(tape[..split_first + split_rest], Cat(items[..n]));
  assert exists split: nat :: 0 <= split <= |tape| && matches(tape[..split], Cat(items[..n])) && matches(tape[split..], Cat(items[n..]));
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

lemma catenating_seqs_matches_cat(ta: seq<Bit>, tb: seq<Bit>, a: seq<Reg>, b: seq<Reg>)
requires matches(ta, Cat(a))
requires matches(tb, Cat(b))
ensures matches(ta + tb, Cat(a + b))
{
  catenating_matches_cat(ta, tb, Cat(a), Cat(b));
  assert matches(ta + tb, Cat([Cat(a), Cat(b)]));
  cat_cat_cat_induction(ta + tb, a, b);
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

// These params affect how generalization occurs.
datatype GeneralizeParams = GeneralizeParams(
  // The maximum number of items allowed to appear in the outermost Cat.
  // If set to 0, no effect.
  // If not zero and more than `max_length` items appear, everything after `max_length-1` is replaced by `Any`.
  max_length: nat
)

// This lemma proves that if you replace some middle section of a Cat with a different regex,
// as long as the replaced part covers the original, the whole regex covers the original.
lemma cat_replace(whole: seq<Reg>, lo: nat, hi: nat, new_range: seq<Reg>)
requires 0 <= lo <= hi <= |whole|
requires forall tape: seq<Bit> | matches(tape, Cat(whole[lo..hi])) :: matches(tape, Cat(new_range))
ensures forall tape: seq<Bit> | matches(tape, Cat(whole)) :: matches(tape, Cat(whole[..lo] + new_range + whole[hi..]))
{
  forall tape: seq<Bit> | matches(tape, Cat(whole))
  ensures matches(tape, Cat(whole[..lo] + new_range + whole[hi..]))
  {
    cat_n_split(tape, whole, lo);
    var n1 :| 0 <= n1 <= |tape| && matches(tape[..n1], Cat(whole[..lo])) && matches(tape[n1..], Cat(whole[lo..]));
    cat_n_split(tape[n1..], whole[lo..], hi - lo);
    assert whole[lo..hi] == whole[lo..][..hi - lo];
    var n2 :| 0 <= n2 <= |tape[n1..]| && matches(tape[n1..][..n2], Cat(whole[lo..hi])) && matches(tape[n1..][n2..], Cat(whole[hi..]));
    assert tape[n1..][..n2] == tape[n1..n1+n2];
    assert matches(tape[n1..n1+n2], Cat(whole[lo..hi]));
    assert matches(tape[n1..n1+n2], Cat(new_range));
    catenating_seqs_matches_cat(tape[..n1], tape[n1..n1+n2], whole[..lo], new_range);
    assert tape[..n1] + tape[n1..n1+n2] == tape[..n1+n2];
    assert matches(tape[..n1+n2], Cat(whole[..lo] + new_range));
    assert tape[..n1+n2] + tape[n1..][n2..] == tape;
    catenating_seqs_matches_cat(tape[..n1+n2], tape[n1+n2..], whole[..lo] + new_range, whole[hi..]);
  }
}

// This function allows us to move beyond just listing neighborhoods as finite strings.
// Specifically, we want to convert long finite regexes into short "classy" ones.
method generalize_cover(r: Reg, params: GeneralizeParams) returns (covers: set<Reg>)
ensures forall tape: HalfTape :: half_tape_matches(tape, r) ==> exists cover :: cover in covers && half_tape_matches(tape, cover)
{
  if r.Alt? {
    // Alternations are automatically split, to reduce the size of regex and exchange them for smaller ones.
    var cover_first := generalize_cover(r.first, params);
    var cover_second := generalize_cover(r.second, params);
    covers := cover_first + cover_second;
    forall tape | half_tape_matches(tape, r)
    ensures exists cover :: cover in covers && half_tape_matches(tape, cover) {
      assert half_tape_matches(tape, r.first) || half_tape_matches(tape, r.second);
    }
    return covers;
  }

  if r.Cat? {
    // Most optimizations happen here.
    if params.max_length != 0 && |r.items| > params.max_length {
      // If the regex is too large, assume that far-away portions are unimportant, and
      // remove them entirely, replacing with 'Any'.
      var items_keep := r.items[..params.max_length-1];
      var items_discard := r.items[params.max_length-1..];
      assert r.items == items_keep + items_discard;
      var any_cover := Cat(items_keep + [Any]);
      covers := { any_cover };
      forall tape | half_tape_matches(tape, r)
      ensures exists cover :: cover in covers && half_tape_matches(tape, cover) {
        var n :| drop_from_tape(tape, n) == HalfTape([]) && matches(take_from_tape(tape, n), r);
        var t := take_from_tape(tape, n);
        assert matches(t, r);
        cat_n_split(t, r.items, |items_keep|);
        var n_initial :| 0 <= n_initial <= |t| && matches(t[..n_initial], Cat(items_keep)) && matches(t[n_initial..], Cat(items_discard));
        catenating_matches_cat(t[..n_initial], t[n_initial..], Cat(items_keep), Cat(items_discard));
        assert t == t[..n_initial] + t[n_initial..];
        assert matches(t, Cat([Cat(items_keep), Cat(items_discard)]));
        cat2_split(t, Cat(items_keep), Cat(items_discard));
        var n_split :| 0 <= n_split <= |t| && matches(t[..n_split], Cat(items_keep)) && matches(t[n_split..], Cat(items_discard));
        assert matches(t[n_split..], Any);
        catenating_matches_cat(t[..n_split], t[n_split..], Cat(items_keep), Any);
        assert t[..n_split] + t[n_split..] == t;
        assert matches(t, Cat([Cat(items_keep), Any]));
        cat_cat_r_induction(t, items_keep, Any);
        assert matches(t, any_cover);
        assert half_tape_matches(tape, any_cover);
      }
      return covers;
    }

    var i := 0;
    var min_repeat := 4;
    while i < |r.items| {
      var group_size := 1;
      while i + group_size * min_repeat <= |r.items| {
        // If there are min_repeat duplicates, starting from i,
        // then replace the last with a Plus.

        var all_same := true;
        var j := 0;
        while j < min_repeat && all_same {
          if r.items[i + j*group_size..i + (j+1)*group_size] != r.items[i..i+group_size] {
            all_same := false;
          }
          j := j + 1;
        }

        if all_same {
          var remove_start := i;
          var remove_end := i + group_size;

          var new_plus := Plus(Cat(r.items[remove_start..remove_end]));
          forall tape | matches(tape, Cat(r.items[remove_start..remove_end]))
          ensures matches(tape, Cat([new_plus]))
          {
            catenating_matches_single(tape, new_plus);
          }
          cat_replace(r.items, remove_start, remove_end, [new_plus]);
          // Add in a plus at the beginning.
          // TODO: If there is a plus right before this, should we also remove that one?
          // Or will that just not happen?
          return {
            Cat(r.items[..remove_start] + [new_plus] + r.items[remove_end..])
          };
        }
        group_size := group_size + 1;
      }
      i := i + 1;
    }


  }

  return { r };
}

/// The TM step goes here

// 'cons' adds a bit to the beginning of the provided tape.
// Adding zero to the beginning of an empty tape does nothing.
function method cons(b: Bit, t: HalfTape): HalfTape {
  if b == B0 && t == HalfTape([])
    then HalfTape([])
    else
      var result := [b] + t.initial;
      assert result[|result|-1] != B0;
      HalfTape(result)
}

function method tail(t: HalfTape): HalfTape {
  if t == HalfTape([]) then HalfTape([]) else HalfTape(t.initial[1..])
}

function method head(t: HalfTape): Bit {
  if t == HalfTape([]) then B0 else t.initial[0]
}

// This lemma verifies that cons and uncons are "opposites", so that adding
// and then removing a bit leaves the tape in its initial state,
// and that removing and then adding back a bit leaves the tape in its
// initial state.
//
// This lemma is not actually used below, since Dafny can prove it automatically.
lemma cons_uncons(tape: HalfTape)
ensures tail(cons(B0, tape)) == tape
ensures tail(cons(B1, tape)) == tape
ensures cons(head(tape), tail(tape)) == tape {
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
datatype MachineState = MachineState(color: Color, head_symbol: Bit, left: HalfTape, right: HalfTape)

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
      head_symbol := head(m.left),
      // We remove one symbol from the left tape.
      left := tail(m.left),
      // The written bit ends up at the beginning of the right tape.
      right := cons(action.write, m.right)
    )
    // This case is identical to the case above, but with left/right reversed.
    case R => MachineState(
      // The new color comes from the action.
      color := action.new_color,
      // The next symbol to be read comes from the first symbol in the right tape.
      head_symbol := head(m.right),
      // We remove one symbol from the right tape.
      right := tail(m.right),
      // The written bit ends up at the beginning of the left tape.
      left := cons(action.write, m.left)
    )
  }
}

// All TMs are assumed to begin in the color CA, on a tape of all zeros.
const initial: MachineState := MachineState(Color.CA, Bit.B0, HalfTape([]), HalfTape([]))

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

// Now, more proof and implementation.

datatype RegexState = RegexState(color: Color, head_symbol: Bit, left: Reg, right: Reg)

predicate state_matches(state: MachineState, r: RegexState) {
  state.color == r.color && state.head_symbol == r.head_symbol && half_tape_matches(state.left, r.left) && half_tape_matches(state.right, r.right)
}

method initial_cover() returns (cover: RegexState)
ensures state_matches(initial, cover)
{
  cover := RegexState(color := CA, head_symbol := B0, left := Cat([]), right := Cat([]));
  var n := 0;
  assert drop_from_tape(HalfTape([]), n) == HalfTape([]);
  assert take_from_tape(HalfTape([]), n) == [];
  assert half_tape_matches(HalfTape([]), Cat([]));
  assert half_tape_matches(initial.left, cover.left);
  assert half_tape_matches(initial.right, cover.right);
  return cover;
}

lemma cons_one_works(tape: HalfTape, r: Reg, b: Bit)
requires half_tape_matches(tape, r)
ensures half_tape_matches(cons(b, tape), cat(Lit(b), r))
{
  var n: nat :| drop_from_tape(tape, n) == HalfTape([]) && matches(take_from_tape(tape, n), r);
  var bit_tape := cons(b, tape);
  assert take_from_tape(bit_tape, n+1) == [b] + take_from_tape(tape, n);
  catenating_matches_cat([b], take_from_tape(tape, n), Lit(b), r);
  assert half_tape_matches(cons(b, tape), Cat([Lit(b), r]));
  assert half_tape_matches(cons(b, tape), cat(Lit(b), r));
}

method regex_step_cover(program: Program, current: RegexState) returns (valid: bool, next_cover: set<RegexState>)
ensures valid ==> forall state: MachineState | state_matches(state, current) :: !machine_step(program, state).Halt?
ensures valid ==> forall state: MachineState | state_matches(state, current) :: exists cover: RegexState :: cover in next_cover && state_matches(machine_step(program, state).next_state, cover)
{

  var current_input := ProgramStepInput(current.head_symbol, current.color);
  if current_input !in program {
    // We reached a cover for at least one halting state. We cannot make progress.
    return false, {};
  }
  var current_action := program[current_input];
  forall state: MachineState | state_matches(state, current)
  ensures !machine_step(program, state).Halt?
  {
    // Trivial!
  }
  match current_action.move {
    case L => {
      var peel_left := deriv_half_tape(current.left);

      next_cover := {};
      var cover0 := RegexState(
        color := current_action.new_color,
        head_symbol := B0,
        left := peel_left.after_0,
        right := cat(Lit(current_action.write), current.right)
      );
      var cover1 := RegexState(
        color := current_action.new_color,
        head_symbol := B1,
        left := peel_left.after_1,
        right := cat(Lit(current_action.write), current.right)
      );
      if peel_left.after_0 != Never {
        next_cover := next_cover + {cover0};
      }
      if peel_left.after_1 != Never {
        next_cover := next_cover + {cover1};
      }
      
      forall state: MachineState | state_matches(state, current) && !machine_step(program, state).Halt?
      ensures exists new_cover :: new_cover in next_cover && state_matches(machine_step(program, state).next_state, new_cover)
      {
        var next_state := MachineState(
          color := current_action.new_color,
          head_symbol := head(state.left),
          left := tail(state.left),
          right := cons(current_action.write, state.right)
        );
        assert machine_step(program, state).next_state == next_state;
        if next_state.head_symbol == B0 {
          assert half_tape_matches(next_state.left, peel_left.after_0);
          assert peel_left.after_0 != Never;
          assert half_tape_matches(state.right, current.right);
          cons_one_works(state.right, current.right, current_action.write);
          assert half_tape_matches(next_state.right, cat(Lit(current_action.write), current.right));
          assert state_matches(next_state, cover0);
        } else {
          assert half_tape_matches(next_state.left, peel_left.after_1);
          assert peel_left.after_1 != Never;
          assert half_tape_matches(state.right, current.right);
          cons_one_works(state.right, current.right, current_action.write);
          assert half_tape_matches(next_state.right, cat(Lit(current_action.write), current.right));
          assert state_matches(next_state, cover1);
        }
      }

      return true, next_cover;
    }
    case R => {
      var peel_right := deriv_half_tape(current.right);

      next_cover := {};
      var cover0 := RegexState(
        color := current_action.new_color,
        head_symbol := B0,
        right := peel_right.after_0,
        left := cat(Lit(current_action.write), current.left)
      );
      var cover1 := RegexState(
        color := current_action.new_color,
        head_symbol := B1,
        right := peel_right.after_1,
        left := cat(Lit(current_action.write), current.left)
      );
      if peel_right.after_0 != Never {
        next_cover := next_cover + {cover0};
      }
      if peel_right.after_1 != Never {
        next_cover := next_cover + {cover1};
      }
      
      forall state: MachineState | state_matches(state, current) && !machine_step(program, state).Halt?
      ensures exists new_cover :: new_cover in next_cover && state_matches(machine_step(program, state).next_state, new_cover)
      {
        var next_state := MachineState(
          color := current_action.new_color,
          head_symbol := head(state.right),
          right := tail(state.right),
          left := cons(current_action.write, state.left)
        );
        assert machine_step(program, state).next_state == next_state;
        if next_state.head_symbol == B0 {
          assert half_tape_matches(next_state.right, peel_right.after_0);
          assert peel_right.after_0 != Never;
          assert half_tape_matches(state.left, current.left);
          cons_one_works(state.left, current.left, current_action.write);
          assert half_tape_matches(next_state.left, cat(Lit(current_action.write), current.left));
          assert state_matches(next_state, cover0);
        } else {
          assert half_tape_matches(next_state.right, peel_right.after_1);
          assert peel_right.after_1 != Never;
          assert half_tape_matches(state.left, current.left);
          cons_one_works(state.left, current.left, current_action.write);
          assert half_tape_matches(next_state.left, cat(Lit(current_action.write), current.left));
          assert state_matches(next_state, cover1);
        }
      }

      return true, next_cover;
    }
  }
}

function TriggerDoneCoverNext(state: MachineState): nat {
  0
}

method regex_cycler_decider(program: Program, time_limit: nat) returns (result: bool)
ensures result ==> program_loops_forever(program)
{
  var first_cover := initial_cover();
  var todo_pile: set<RegexState> := {first_cover};
  var done_pile: set<RegexState> := {};
  

  assert first_cover in todo_pile + done_pile;
  var gas := 0;
  while gas < time_limit && todo_pile != {}
  // The initial state must be represented, so that our induction can conclude.
  invariant exists cover :: cover in todo_pile+done_pile && state_matches(initial, cover)
  // Each state covered by a "done" regex must not halt in one step...
  invariant forall done_cover {:trigger done_cover in done_pile} | done_cover in done_pile :: forall state | state_matches(state, done_cover) :: !machine_step(program, state).Halt?
  // and that next step needs to be covered by a regex that's either todo or already done.
  invariant forall done_cover {:trigger done_cover in done_pile} | done_cover in done_pile :: forall state {:trigger TriggerDoneCoverNext(state)} | state_matches(state, done_cover) ::
    exists todo_cover :: todo_cover in todo_pile+done_pile && state_matches(machine_step(program, state).next_state, todo_cover)
  {
    gas := gas + 1;

    var current: RegexState :| current in todo_pile;
    todo_pile := todo_pile - {current};
    done_pile := done_pile + {current};


    var still_ok, new_covers := regex_step_cover(program, current);
    if !still_ok {
      // Failed to move forward.
      return false;
    }
    todo_pile := todo_pile + new_covers;

    forall done_cover | done_cover in done_pile ensures forall state | state_matches(state, done_cover) ::
    exists todo_cover :: todo_cover in todo_pile+done_pile && state_matches(machine_step(program, state).next_state, todo_cover) {
      assert done_cover in done_pile;
      forall state | state_matches(state, done_cover) ensures
        exists todo_cover :: todo_cover in todo_pile+done_pile && state_matches(machine_step(program, state).next_state, todo_cover)
      {
        assert TriggerDoneCoverNext(state) == 0;
        // TODO
      }
    }
  }

  if todo_pile != {} {
    return false;
  }
  
  forall done_cover: RegexState | done_cover in done_pile ensures forall covered_state :: state_matches(covered_state, done_cover) ==> (!machine_step(program, covered_state).Halt? && 
    exists todo_cover :: todo_cover in done_pile && state_matches(machine_step(program, covered_state).next_state, todo_cover))
  {
    assert TriggerCoverNext(done_cover) == 0;
    forall covered_state: MachineState ensures state_matches(covered_state, done_cover) ==> (!machine_step(program, covered_state).Halt? && 
    exists todo_cover :: todo_cover in done_pile && state_matches(machine_step(program, covered_state).next_state, todo_cover))
    {
      assert TriggerDoneCoverNext(covered_state) == 0;
    }
  }
  assert complete_pile(program, done_pile);
  all_machines_loop(program, done_pile);

  return true;
}


function TriggerCoverNext(done_cover: RegexState): nat {
  0
}

predicate complete_pile(program: Program, fin_pile: set<RegexState>) {
  (exists cover :: cover in fin_pile && state_matches(initial, cover)) &&
  (forall done_cover: RegexState {:trigger TriggerCoverNext(done_cover)} :: done_cover in fin_pile ==> forall covered_state :: state_matches(covered_state, done_cover) ==> (!machine_step(program, covered_state).Halt? && 
    exists todo_cover :: todo_cover in fin_pile && state_matches(machine_step(program, covered_state).next_state, todo_cover)))
}

lemma all_machines_loop_induct(program: Program, fin_pile: set<RegexState>, n: nat)
requires complete_pile(program, fin_pile)
ensures !machine_iter_n(program, n).Halt? && exists next_cover :: next_cover in fin_pile && state_matches(machine_iter_n(program, n).next_state, next_cover)
{
  if n == 0 {
    assert machine_iter_n(program, 0).next_state == initial;
    var init_cover :| init_cover in fin_pile && state_matches(initial, init_cover);
    assert !machine_iter_n(program, n).Halt?;
    assert exists next_cover :: next_cover in fin_pile && state_matches(machine_iter_n(program, n).next_state, next_cover);
    return;
  }
  all_machines_loop_induct(program, fin_pile, n-1);
  var my_cover: RegexState :| my_cover in fin_pile && state_matches(machine_iter_n(program, n-1).next_state, my_cover);
  assert TriggerCoverNext(my_cover) == 0;
  assert !machine_iter_n(program, n).Halt?;
  assert exists next_cover :: next_cover in fin_pile && state_matches(machine_iter_n(program, n).next_state, next_cover);
}

lemma all_machines_loop(program: Program, fin_pile: set<RegexState>)
requires complete_pile(program, fin_pile)
ensures forall each_n: nat :: !machine_iter_n(program, each_n).Halt?
{
  forall n: nat
  ensures !machine_iter_n(program, n).Halt?
  {
    all_machines_loop_induct(program, fin_pile, n);
  }
}


datatype HalfTapeDeriv = HalfTapeDeriv(after_0: Reg, after_1: Reg)

method deriv_half_tape(r: Reg) returns (result: HalfTapeDeriv)
ensures forall t: HalfTape | half_tape_matches(t, r) && head(t) == B0 :: half_tape_matches(tail(t), result.after_0)
ensures forall t: HalfTape | half_tape_matches(t, r) && head(t) == B1 :: half_tape_matches(tail(t), result.after_1)
{
  var d := deriv_of(r);
  result := HalfTapeDeriv(
    after_0 := if d.can_be_empty then alt(Cat([]), d.after_0) else d.after_0,
    after_1 := d.after_1
  );
  forall t: HalfTape | half_tape_matches(t, r) && head(t) == B1
  ensures half_tape_matches(tail(t), result.after_1) {
    var n: nat :| drop_from_tape(t, n) == HalfTape([]) && matches(take_from_tape(t, n), r);
    var lead := take_from_tape(t, n);
    assert t.initial[0] == B1;
    assert tail(t) == HalfTape(t.initial[1..]);
    if lead == [] {
      assert d.can_be_empty;
      assert half_tape_matches(tail(t), Cat([]));
      assert half_tape_matches(tail(t), result.after_1);
    } else {
      assert lead[0] == B1;
      assert matches(lead, r);
      assert matches(lead[1..], d.after_1);
      assert take_from_tape(tail(t), n-1) == lead[1..];
      assert drop_from_tape(tail(t), n-1) == HalfTape([]);
      assert half_tape_matches(tail(t), d.after_1);
      assert half_tape_matches(tail(t), result.after_1);
    }
  }
  forall t: HalfTape | half_tape_matches(t, r) && head(t) == B0
  ensures half_tape_matches(tail(t), result.after_0) {
    var n: nat :| drop_from_tape(t, n) == HalfTape([]) && matches(take_from_tape(t, n), r);
    var lead := take_from_tape(t, n);
    assert t.initial == [] || t.initial[0] == B0;
    assert tail(t) == HalfTape([]) || tail(t) == HalfTape(t.initial[1..]);
    if lead == [] {
      assert d.can_be_empty;
      assert half_tape_matches(tail(t), Cat([]));
      assert half_tape_matches(tail(t), result.after_0);
    } else {
      assert lead[0] == B0;
      assert matches(lead, r);
      assert matches(lead[1..], d.after_0);
      assert take_from_tape(tail(t), n-1) == lead[1..];
      assert drop_from_tape(tail(t), n-1) == HalfTape([]);
      assert half_tape_matches(tail(t), d.after_0);
      assert half_tape_matches(tail(t), result.after_0);
    }
  }
}

