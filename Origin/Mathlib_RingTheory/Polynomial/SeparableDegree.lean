/-
Extracted from RingTheory/Polynomial/SeparableDegree.lean
Genuine: 9 of 9 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Separable degree

This file contains basics about the separable degree of a polynomial.

## Main results

- `IsSeparableContraction`: is the condition that, for `g` a separable polynomial, we have that
  `g(x^(q^m)) = f(x)` for some `m : ℕ`.
- `HasSeparableContraction`: the condition of having a separable contraction
- `HasSeparableContraction.degree`: the separable degree, defined as the degree of some
  separable contraction
- `Irreducible.hasSeparableContraction`: any irreducible polynomial can be contracted
  to a separable polynomial
- `HasSeparableContraction.dvd_degree'`: the degree of a separable contraction divides the degree,
  in function of the exponential characteristic of the field
- `HasSeparableContraction.dvd_degree` and `HasSeparableContraction.eq_degree` specialize the
  statement of `separable_degree_dvd_degree`
- `IsSeparableContraction.degree_eq`: the separable degree is well-defined, implemented as the
  statement that the degree of any separable contraction equals `HasSeparableContraction.degree`

## Tags

separable degree, degree, polynomial
-/

noncomputable section

namespace Polynomial

open Polynomial

section CommSemiring

variable {F : Type*} [CommSemiring F] (q : ℕ)

def IsSeparableContraction (f : F[X]) (g : F[X]) : Prop :=
  g.Separable ∧ ∃ m : ℕ, expand F (q ^ m) g = f

def HasSeparableContraction (f : F[X]) : Prop :=
  ∃ g : F[X], IsSeparableContraction q f g

variable {q} {f : F[X]} (hf : HasSeparableContraction q f)

def HasSeparableContraction.contraction : F[X] :=
  Classical.choose hf

def HasSeparableContraction.degree : ℕ :=
  hf.contraction.natDegree

theorem HasSeparableContraction.isSeparableContraction :
    IsSeparableContraction q f hf.contraction := Classical.choose_spec hf

theorem IsSeparableContraction.dvd_degree' {g} (hf : IsSeparableContraction q f g) :
    ∃ m : ℕ, g.natDegree * q ^ m = f.natDegree := by
  obtain ⟨m, rfl⟩ := hf.2
  use m
  rw [natDegree_expand]

theorem HasSeparableContraction.dvd_degree' : ∃ m : ℕ, hf.degree * q ^ m = f.natDegree :=
  (Classical.choose_spec hf).dvd_degree'

theorem HasSeparableContraction.dvd_degree : hf.degree ∣ f.natDegree :=
  let ⟨a, ha⟩ := hf.dvd_degree'
  Dvd.intro (q ^ a) ha

theorem HasSeparableContraction.eq_degree {f : F[X]} (hf : HasSeparableContraction 1 f) :
    hf.degree = f.natDegree := by
  let ⟨a, ha⟩ := hf.dvd_degree'
  rw [← ha, one_pow a, mul_one]

end CommSemiring

section Field

variable {F : Type*} [Field F]

variable (q : ℕ) {f : F[X]} (hf : HasSeparableContraction q f)
