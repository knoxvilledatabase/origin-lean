/-
Extracted from Algebra/ContinuedFractions/Computation/Basic.lean
Genuine: 8 | Conflates: 0 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core
import Mathlib.Algebra.Order.Floor
import Mathlib.Algebra.ContinuedFractions.Basic

/-!
# Computable Continued Fractions

## Summary

We formalise the standard computation of (regular) continued fractions for linear ordered floor
fields. The algorithm is rather simple. Here is an outline of the procedure adapted from Wikipedia:

Take a value `v`. We call `⌊v⌋` the *integer part* of `v` and `v - ⌊v⌋` the *fractional part* of
`v`.  A continued fraction representation of `v` can then be given by `[⌊v⌋; b₀, b₁, b₂,...]`, where
`[b₀; b₁, b₂,...]` recursively is the continued fraction representation of `1 / (v - ⌊v⌋)`.  This
process stops when the fractional part hits 0.

In other words: to calculate a continued fraction representation of a number `v`, write down the
integer part (i.e. the floor) of `v`. Subtract this integer part from `v`. If the difference is 0,
stop; otherwise find the reciprocal of the difference and repeat. The procedure will terminate if
and only if `v` is rational.

For an example, refer to `IntFractPair.stream`.

## Main definitions

- `GenContFract.IntFractPair.stream`: computes the stream of integer and fractional parts of a given
  value as described in the summary.
- `GenContFract.of`: computes the generalised continued fraction of a value `v`.
  In fact, it computes a regular continued fraction that terminates if and only if `v` is rational.

## Implementation Notes

There is an intermediate definition `GenContFract.IntFractPair.seq1` between
`GenContFract.IntFractPair.stream` and `GenContFract.of` to wire up things. Users should not
(need to) directly interact with it.

The computation of the integer and fractional pairs of a value can elegantly be
captured by a recursive computation of a stream of option pairs. This is done in
`IntFractPair.stream`. However, the type then does not guarantee the first pair to always be
`some` value, as expected by a continued fraction.

To separate concerns, we first compute a single head term that always exists in
`GenContFract.IntFractPair.seq1` followed by the remaining stream of option pairs. This sequence
with a head term (`seq1`) is then transformed to a generalized continued fraction in
`GenContFract.of` by extracting the wanted integer parts of the head term and the stream.

## References

- https://en.wikipedia.org/wiki/Continued_fraction

## Tags

numerics, number theory, approximations, fractions
-/

namespace GenContFract

variable (K : Type*)

structure IntFractPair where
  b : ℤ
  fr : K

variable {K}

/-! Interlude: define some expected coercions and instances. -/

namespace IntFractPair

instance [Repr K] : Repr (IntFractPair K) :=
  ⟨fun p _ => "(b : " ++ repr p.b ++ ", fract : " ++ repr p.fr ++ ")"⟩

instance inhabited [Inhabited K] : Inhabited (IntFractPair K) :=
  ⟨⟨0, default⟩⟩

def mapFr {β : Type*} (f : K → β) (gp : IntFractPair K) : IntFractPair β :=
  ⟨gp.b, f gp.fr⟩

section coe

/-! Interlude: define some expected coercions. -/

variable {β : Type*} [Coe K β]

@[coe]
def coeFn : IntFractPair K → IntFractPair β := mapFr (↑)

instance coe : Coe (IntFractPair K) (IntFractPair β) where
  coe := coeFn

@[simp, norm_cast]
theorem coe_to_intFractPair {b : ℤ} {fr : K} :
    (↑(IntFractPair.mk b fr) : IntFractPair β) = IntFractPair.mk b (↑fr : β) :=
  rfl

end coe

variable [LinearOrderedField K] [FloorRing K]

protected def of (v : K) : IntFractPair K :=
  ⟨⌊v⌋, Int.fract v⟩

protected def stream (v : K) : Stream' <| Option (IntFractPair K)
  | 0 => some (IntFractPair.of v)
  | n + 1 =>
    (IntFractPair.stream v n).bind fun ap_n =>
      if ap_n.fr = 0 then none else some (IntFractPair.of ap_n.fr⁻¹)

theorem stream_isSeq (v : K) : (IntFractPair.stream v).IsSeq := by
  intro _ hyp
  simp [IntFractPair.stream, hyp]

protected def seq1 (v : K) : Stream'.Seq1 <| IntFractPair K :=
  ⟨IntFractPair.of v, -- the head
    -- take the tail of `IntFractPair.stream` since the first element is already in the head
    Stream'.Seq.tail
      -- create a sequence from `IntFractPair.stream`
      ⟨IntFractPair.stream v, -- the underlying stream
        @stream_isSeq _ _ _ v⟩⟩ -- the proof that the stream is a sequence

end IntFractPair

protected def of [LinearOrderedField K] [FloorRing K] (v : K) : GenContFract K :=
  let ⟨h, s⟩ := IntFractPair.seq1 v -- get the sequence of integer and fractional parts.
  ⟨h.b, -- the head is just the first integer part
    s.map fun p => ⟨1, p.b⟩⟩ -- the sequence consists of the remaining integer parts as the partial
                            -- denominators; all partial numerators are simply 1

end GenContFract
