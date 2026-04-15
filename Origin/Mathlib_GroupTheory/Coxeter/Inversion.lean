/-
Extracted from GroupTheory/Coxeter/Inversion.lean
Genuine: 10 of 10 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Reflections, inversions, and inversion sequences

Throughout this file, `B` is a type and `M : CoxeterMatrix B` is a Coxeter matrix.
`cs : CoxeterSystem M W` is a Coxeter system; that is, `W` is a group, and `cs` holds the data
of a group isomorphism `W ≃* M.group`, where `M.group` refers to the quotient of the free group on
`B` by the Coxeter relations given by the matrix `M`. See `Mathlib/GroupTheory/Coxeter/Basic.lean`
for more details.

We define a *reflection* (`CoxeterSystem.IsReflection`) to be an element of the form
$t = u s_i u^{-1}$, where $u \in W$ and $s_i$ is a simple reflection. We say that a reflection $t$
is a *left inversion* (`CoxeterSystem.IsLeftInversion`) of an element $w \in W$ if
$\ell(t w) < \ell(w)$, and we say it is a *right inversion* (`CoxeterSystem.IsRightInversion`) of
$w$ if $\ell(w t) > \ell(w)$. Here $\ell$ is the length function
(see `Mathlib/GroupTheory/Coxeter/Length.lean`).

Given a word, we define its *left inversion sequence* (`CoxeterSystem.leftInvSeq`) and its
*right inversion sequence* (`CoxeterSystem.rightInvSeq`). We prove that if a word is reduced, then
both of its inversion sequences contain no duplicates. In fact, the right (respectively, left)
inversion sequence of a reduced word for $w$ consists of all of the right (respectively, left)
inversions of $w$ in some order, but we do not prove that in this file.

## Main definitions

* `CoxeterSystem.IsReflection`
* `CoxeterSystem.IsLeftInversion`
* `CoxeterSystem.IsRightInversion`
* `CoxeterSystem.leftInvSeq`
* `CoxeterSystem.rightInvSeq`

## References

* [A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*](bjorner2005)

-/

assert_not_exists TwoSidedIdeal

namespace CoxeterSystem

open List Matrix Function

variable {B : Type*}

variable {W : Type*} [Group W]

variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple

local prefix:100 "π " => cs.wordProd

local prefix:100 "ℓ " => cs.length

def IsReflection (t : W) : Prop := ∃ w i, t = w * s i * w⁻¹

theorem isReflection_simple (i : B) : cs.IsReflection (s i) := by use 1, i; simp

namespace IsReflection

variable {cs}

variable {t : W} (ht : cs.IsReflection t)

include ht

theorem pow_two : t ^ 2 = 1 := by
  rcases ht with ⟨w, i, rfl⟩
  simp

theorem mul_self : t * t = 1 := by
  rcases ht with ⟨w, i, rfl⟩
  simp

theorem inv : t⁻¹ = t := by
  rcases ht with ⟨w, i, rfl⟩
  simp [mul_assoc]

theorem isReflection_inv : cs.IsReflection t⁻¹ := by rwa [ht.inv]

theorem odd_length : Odd (ℓ t) := by
  suffices cs.lengthParity t = Multiplicative.ofAdd 1 by
    simpa [lengthParity_eq_ofAdd_length, ZMod.natCast_eq_one_iff_odd]
  rcases ht with ⟨w, i, rfl⟩
  simp [lengthParity_simple]

theorem length_mul_left_ne (w : W) : ℓ (w * t) ≠ ℓ w := by
  suffices cs.lengthParity (w * t) ≠ cs.lengthParity w by
    contrapose this
    simp only [lengthParity_eq_ofAdd_length, this]
  rcases ht with ⟨w, i, rfl⟩
  simp [lengthParity_simple]

theorem length_mul_right_ne (w : W) : ℓ (t * w) ≠ ℓ w := by
  suffices cs.lengthParity (t * w) ≠ cs.lengthParity w by
    contrapose this
    simp only [lengthParity_eq_ofAdd_length, this]
  rcases ht with ⟨w, i, rfl⟩
  simp [lengthParity_simple]

theorem conj (w : W) : cs.IsReflection (w * t * w⁻¹) := by
  obtain ⟨u, i, rfl⟩ := ht
  use w * u, i
  group

end IsReflection
