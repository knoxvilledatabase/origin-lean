/-
Extracted from Algebra/ContinuedFractions/Basic.lean
Genuine: 26 | Conflates: 0 | Dissolved: 0 | Infrastructure: 12
-/
import Origin.Core
import Mathlib.Data.Seq.Seq
import Mathlib.Algebra.Field.Defs

noncomputable section

/-!
# Basic Definitions/Theorems for Continued Fractions

## Summary

We define generalised, simple, and regular continued fractions and functions to evaluate their
convergents. We follow the naming conventions from Wikipedia and [wall2018analytic], Chapter 1.

## Main definitions

1. Generalised continued fractions (gcfs)
2. Simple continued fractions (scfs)
3. (Regular) continued fractions ((r)cfs)
4. Computation of convergents using the recurrence relation in `convs`.
5. Computation of convergents by directly evaluating the fraction described by the gcf in `convs'`.

## Implementation notes

1. The most commonly used kind of continued fractions in the literature are regular continued
fractions. We hence just call them `ContFract` in the library.
2. We use sequences from `Data.Seq` to encode potentially infinite sequences.

## References

- <https://en.wikipedia.org/wiki/Generalized_continued_fraction>
- [Wall, H.S., *Analytic Theory of Continued Fractions*][wall2018analytic]

## Tags

numerics, number theory, approximations, fractions
-/

variable (α : Type*)

/-!### Definitions -/

structure GenContFract.Pair where
  /-- Partial numerator -/
  a : α
  /-- Partial denominator -/
  b : α
  deriving Inhabited

open GenContFract

/-! Interlude: define some expected coercions and instances. -/

namespace GenContFract.Pair

variable {α}

instance [Repr α] : Repr (Pair α) :=
  ⟨fun p _ ↦ "(a : " ++ repr p.a ++ ", b : " ++ repr p.b ++ ")"⟩

def map {β : Type*} (f : α → β) (gp : Pair α) : Pair β :=
  ⟨f gp.a, f gp.b⟩

section coe

variable {β : Type*} [Coe α β]

@[coe]
def coeFn : Pair α → Pair β := map (↑)

instance : Coe (Pair α) (Pair β) :=
  ⟨coeFn⟩

@[simp, norm_cast]
theorem coe_toPair {a b : α} : (↑(Pair.mk a b) : Pair β) = Pair.mk (a : β) (b : β) := rfl

end coe

end GenContFract.Pair

@[ext]
structure GenContFract where
  /-- Head term -/
  h : α
  /-- Sequence of partial numerator and denominator pairs. -/
  s : Stream'.Seq <| Pair α

variable {α}

namespace GenContFract

def ofInteger (a : α) : GenContFract α :=
  ⟨a, Stream'.Seq.nil⟩

instance [Inhabited α] : Inhabited (GenContFract α) :=
  ⟨ofInteger default⟩

def partNums (g : GenContFract α) : Stream'.Seq α :=
  g.s.map Pair.a

def partDens (g : GenContFract α) : Stream'.Seq α :=
  g.s.map Pair.b

def TerminatedAt (g : GenContFract α) (n : ℕ) : Prop :=
  g.s.TerminatedAt n

instance terminatedAtDecidable (g : GenContFract α) (n : ℕ) :
    Decidable (g.TerminatedAt n) := by
  unfold TerminatedAt
  infer_instance

def Terminates (g : GenContFract α) : Prop :=
  g.s.Terminates

section coe

/-! Interlude: define some expected coercions. -/

variable {β : Type*} [Coe α β]

@[coe]
def coeFn : GenContFract α → GenContFract β :=
  fun g ↦ ⟨(g.h : β), (g.s.map (↑) : Stream'.Seq <| Pair β)⟩

instance : Coe (GenContFract α) (GenContFract β) :=
  ⟨coeFn⟩

@[simp, norm_cast]
theorem coe_toGenContFract {g : GenContFract α} :
    (g : GenContFract β) =
      ⟨(g.h : β), (g.s.map (↑) : Stream'.Seq <| Pair β)⟩ := rfl

end coe

end GenContFract

def GenContFract.IsSimpContFract (g : GenContFract α)
    [One α] : Prop :=
  ∀ (n : ℕ) (aₙ : α), g.partNums.get? n = some aₙ → aₙ = 1

variable (α)

def SimpContFract [One α] :=
  { g : GenContFract α // g.IsSimpContFract }

variable {α}

namespace SimpContFract

variable [One α]

def ofInteger (a : α) : SimpContFract α :=
  ⟨GenContFract.ofInteger a, fun n aₙ h ↦ by cases h⟩

instance : Inhabited (SimpContFract α) :=
  ⟨ofInteger 1⟩

instance : Coe (SimpContFract α) (GenContFract α) :=
  -- Porting note: originally `by unfold SimpContFract; infer_instance`
  ⟨Subtype.val⟩

end SimpContFract

def SimpContFract.IsContFract [One α] [Zero α] [LT α]
    (s : SimpContFract α) : Prop :=
  ∀ (n : ℕ) (bₙ : α),
    (↑s : GenContFract α).partDens.get? n = some bₙ → 0 < bₙ

variable (α)

def ContFract [One α] [Zero α] [LT α] :=
  { s : SimpContFract α // s.IsContFract }

variable {α}

/-! Interlude: define some expected coercions. -/

namespace ContFract

variable [One α] [Zero α] [LT α]

def ofInteger (a : α) : ContFract α :=
  ⟨SimpContFract.ofInteger a, fun n bₙ h ↦ by cases h⟩

instance : Inhabited (ContFract α) :=
  ⟨ofInteger 0⟩

instance : Coe (ContFract α) (SimpContFract α) :=
  -- Porting note: originally `by unfold ContFract; infer_instance`
  ⟨Subtype.val⟩

instance : Coe (ContFract α) (GenContFract α) :=
  ⟨fun c ↦ c.val⟩
  -- Porting note: was `fun c ↦ ↑(↑c : SimpContFract α)`

end ContFract

namespace GenContFract

/-!
### Computation of Convergents

We now define how to compute the convergents of a gcf. There are two standard ways to do this:
directly evaluating the (infinite) fraction described by the gcf or using a recurrence relation.
For (r)cfs, these computations are equivalent as shown in
`Algebra.ContinuedFractions.ConvergentsEquiv`.
-/

variable {K : Type*} [DivisionRing K]

/-!
We start with the definition of the recurrence relation. Given a gcf `g`, for all `n ≥ 1`, we define
- `A₋₁ = 1,  A₀ = h,  Aₙ = bₙ₋₁ * Aₙ₋₁ + aₙ₋₁ * Aₙ₋₂`, and
- `B₋₁ = 0,  B₀ = 1,  Bₙ = bₙ₋₁ * Bₙ₋₁ + aₙ₋₁ * Bₙ₋₂`.

`Aₙ, Bₙ` are called the *nth continuants*, `Aₙ` the *nth numerator*, and `Bₙ` the
*nth denominator* of `g`. The *nth convergent* of `g` is given by `Aₙ / Bₙ`.
-/

def nextNum (a b ppredA predA : K) : K :=
  b * predA + a * ppredA

def nextDen (aₙ bₙ ppredB predB : K) : K :=
  bₙ * predB + aₙ * ppredB

def nextConts (a b : K) (ppred pred : Pair K) : Pair K :=
  ⟨nextNum a b ppred.a pred.a, nextDen a b ppred.b pred.b⟩

def contsAux (g : GenContFract K) : Stream' (Pair K)
  | 0 => ⟨1, 0⟩
  | 1 => ⟨g.h, 1⟩
  | n + 2 =>
    match g.s.get? n with
    | none => contsAux g (n + 1)
    | some gp => nextConts gp.a gp.b (contsAux g n) (contsAux g (n + 1))

def conts (g : GenContFract K) : Stream' (Pair K) :=
  g.contsAux.tail

def nums (g : GenContFract K) : Stream' K :=
  g.conts.map Pair.a

def dens (g : GenContFract K) : Stream' K :=
  g.conts.map Pair.b

def convs (g : GenContFract K) : Stream' K :=
  fun n : ℕ ↦ g.nums n / g.dens n

def convs'Aux : Stream'.Seq (Pair K) → ℕ → K
  | _, 0 => 0
  | s, n + 1 =>
    match s.head with
    | none => 0
    | some gp => gp.a / (gp.b + convs'Aux s.tail n)

def convs' (g : GenContFract K) (n : ℕ) : K :=
  g.h + convs'Aux g.s n

end GenContFract
