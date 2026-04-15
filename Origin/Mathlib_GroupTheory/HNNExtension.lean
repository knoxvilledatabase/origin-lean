/-
Extracted from GroupTheory/HNNExtension.lean
Genuine: 11 of 12 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

## HNN Extensions of Groups

This file defines the HNN extension of a group `G`, `HNNExtension G A B φ`. Given a group `G`,
subgroups `A` and `B` and an isomorphism `φ` of `A` and `B`, we adjoin a letter `t` to `G`, such
that for any `a ∈ A`, the conjugate of `of a` by `t` is `of (φ a)`, where `of` is the canonical map
from `G` into the `HNNExtension`. This construction is named after Graham Higman, Bernhard Neumann
and Hanna Neumann.

## Main definitions

- `HNNExtension G A B φ` : The HNN Extension of a group `G`, where `A` and `B` are subgroups and `φ`
  is an isomorphism between `A` and `B`.
- `HNNExtension.of` : The canonical embedding of `G` into `HNNExtension G A B φ`.
- `HNNExtension.t` : The stable letter of the HNN extension.
- `HNNExtension.lift` : Define a function `HNNExtension G A B φ →* H`, by defining it on `G` and `t`
- `HNNExtension.of_injective` : The canonical embedding `G →* HNNExtension G A B φ` is injective.
- `HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range` : Britton's Lemma. If an element of
  `G` is represented by a reduced word, then this reduced word does not contain `t`.

-/

assert_not_exists Field

open Monoid Coprod Multiplicative Subgroup Function

def HNNExtension.con (G : Type*) [Group G] (A B : Subgroup G) (φ : A ≃* B) :
    Con (G ∗ Multiplicative ℤ) :=
  conGen (fun x y => ∃ (a : A),
    x = inr (ofAdd 1) * inl (a : G) ∧
    y = inl (φ a : G) * inr (ofAdd 1))

def HNNExtension (G : Type*) [Group G] (A B : Subgroup G) (φ : A ≃* B) : Type _ :=
  (HNNExtension.con G A B φ).Quotient

variable {G : Type*} [Group G] {A B : Subgroup G} {φ : A ≃* B} {H : Type*}
  [Group H] {M : Type*} [Monoid M]

-- INSTANCE (free from Core): :

namespace HNNExtension

def of : G →* HNNExtension G A B φ :=
  (HNNExtension.con G A B φ).mk'.comp inl

def t : HNNExtension G A B φ :=
  (HNNExtension.con G A B φ).mk'.comp inr (ofAdd 1)

theorem t_mul_of (a : A) :
    t * (of (a : G) : HNNExtension G A B φ) = of (φ a : G) * t :=
  (Con.eq _).2 <| ConGen.Rel.of _ _ <| ⟨a, by simp⟩

theorem of_mul_t (b : B) :
    (of (b : G) : HNNExtension G A B φ) * t = t * of (φ.symm b : G) := by
  rw [t_mul_of]; simp

theorem equiv_eq_conj (a : A) :
    (of (φ a : G) : HNNExtension G A B φ) = t * of (a : G) * t⁻¹ := by
  rw [t_mul_of]; simp

theorem equiv_symm_eq_conj (b : B) :
    (of (φ.symm b : G) : HNNExtension G A B φ) = t⁻¹ * of (b : G) * t := by
  rw [mul_assoc, of_mul_t]; simp

theorem inv_t_mul_of (b : B) :
    t⁻¹ * (of (b : G) : HNNExtension G A B φ) = of (φ.symm b : G) * t⁻¹ := by
  rw [equiv_symm_eq_conj]; simp

theorem of_mul_inv_t (a : A) :
    (of (a : G) : HNNExtension G A B φ) * t⁻¹ = t⁻¹ * of (φ a : G) := by
  rw [equiv_eq_conj]; simp [mul_assoc]

def lift (f : G →* H) (x : H) (hx : ∀ a : A, x * f ↑a = f (φ a : G) * x) :
    HNNExtension G A B φ →* H :=
  Con.lift _ (Coprod.lift f (zpowersHom H x)) (Con.conGen_le <| by
    rintro _ _ ⟨a, rfl, rfl⟩
    simp [hx])

set_option backward.isDefEq.respectTransparency false in
