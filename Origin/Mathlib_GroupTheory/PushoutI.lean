/-
Extracted from GroupTheory/PushoutI.lean
Genuine: 7 of 10 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!

## Pushouts of Monoids and Groups

This file defines wide pushouts of monoids and groups and proves some properties
of the amalgamated product of groups (i.e. the special case where all the maps
in the diagram are injective).

## Main definitions

- `Monoid.PushoutI`: the pushout of a diagram of monoids indexed by a type `ι`
- `Monoid.PushoutI.base`: the map from the amalgamating monoid to the pushout
- `Monoid.PushoutI.of`: the map from each Monoid in the family to the pushout
- `Monoid.PushoutI.lift`: the universal property used to define homomorphisms out of the pushout.

- `Monoid.PushoutI.NormalWord`: a normal form for words in the pushout
- `Monoid.PushoutI.of_injective`: if all the maps in the diagram are injective in a pushout of
  groups then so is `of`
- `Monoid.PushoutI.Reduced.eq_empty_of_mem_range`: For any word `w` in the coproduct,
  if `w` is reduced (i.e none its letters are in the image of the base monoid), and nonempty, then
  `w` itself is not in the image of the base monoid.

## References

* The normal form theorem follows these [notes](https://webspace.maths.qmul.ac.uk/i.m.chiswell/ggt/lecture_notes/lecture2.pdf)
  from Queen Mary University

## Tags

amalgamated product, pushout, group

-/

namespace Monoid

open CoprodI Subgroup Coprod Function List

variable {ι : Type*} {G : ι → Type*} {H : Type*} {K : Type*} [Monoid K]

def PushoutI.con [∀ i, Monoid (G i)] [Monoid H] (φ : ∀ i, H →* G i) :
    Con (Coprod (CoprodI G) H) :=
  conGen (fun x y : Coprod (CoprodI G) H =>
    ∃ i x', x = inl (of (φ i x')) ∧ y = inr x')

def PushoutI [∀ i, Monoid (G i)] [Monoid H] (φ : ∀ i, H →* G i) : Type _ :=
  (PushoutI.con φ).Quotient

namespace PushoutI

section Monoid

variable [∀ i, Monoid (G i)] [Monoid H] {φ : ∀ i, H →* G i}

-- INSTANCE (free from Core): mul

-- INSTANCE (free from Core): one

-- INSTANCE (free from Core): monoid

def of (i : ι) : G i →* PushoutI φ :=
  (Con.mk' _).comp <| inl.comp CoprodI.of

variable (φ) in

def base : H →* PushoutI φ :=
  (Con.mk' _).comp inr

theorem of_comp_eq_base (i : ι) : (of i).comp (φ i) = (base φ) := by
  ext x
  apply (Con.eq _).2
  refine ConGen.Rel.of _ _ ?_
  simp only [MonoidHom.comp_apply]
  exact ⟨_, _, rfl, rfl⟩

variable (φ) in

theorem of_apply_eq_base (i : ι) (x : H) : of i (φ i x) = base φ x := by
  rw [← MonoidHom.comp_apply, of_comp_eq_base]

def lift (f : ∀ i, G i →* K) (k : H →* K)
    (hf : ∀ i, (f i).comp (φ i) = k) :
    PushoutI φ →* K :=
  Con.lift _ (Coprod.lift (CoprodI.lift f) k) <| by
    apply Con.conGen_le fun x y => ?_
    rintro ⟨i, x', rfl, rfl⟩
    simp only [DFunLike.ext_iff, MonoidHom.coe_comp, comp_apply] at hf
    simp [hf]

set_option backward.isDefEq.respectTransparency false in
