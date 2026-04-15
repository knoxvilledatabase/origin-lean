/-
Extracted from Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean
Genuine: 23 | Conflates: 0 | Dissolved: 8 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Algebra.DirectSum.AddChar
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Pontryagin duality for finite abelian groups

This file proves the Pontryagin duality in case of finite abelian groups. This states that any
finite abelian group is canonically isomorphic to its double dual (the space of complex-valued
characters of its space of complex-valued characters).

We first prove it for `ZMod n` and then extend to all finite abelian groups using the
Structure Theorem.

## TODO

Reuse the work done in `Mathlib.GroupTheory.FiniteAbelian.Duality`. This requires to write some more
glue.
-/

noncomputable section

open Circle Finset Function Multiplicative

open Fintype (card)

open Real hiding exp

open scoped BigOperators DirectSum

variable {α : Type*} [AddCommGroup α] {n : ℕ} {a b : α}

namespace AddChar

variable (n : ℕ) [NeZero n]

def zmod (x : ZMod n) : AddChar (ZMod n) Circle :=
  AddChar.compAddMonoidHom ⟨AddCircle.toCircle, AddCircle.toCircle_zero, AddCircle.toCircle_add⟩ <|
    ZMod.toAddCircle.comp <| .mulLeft x

@[simp] lemma zmod_intCast (x y : ℤ) : zmod n x y = exp (2 * π * (x * y / n)) := by
  simp [zmod, ← Int.cast_mul x y, -Int.cast_mul, ZMod.toAddCircle_intCast,
    AddCircle.toCircle_apply_mk]

@[simp] lemma zmod_zero : zmod n 0 = 1 :=
  DFunLike.ext _ _ <| by simp [ZMod.intCast_surjective.forall, zmod]

variable {n}

@[simp] lemma zmod_add : ∀ x y : ZMod n, zmod n (x + y) = zmod n x * zmod n y := by
  simp [DFunLike.ext_iff, ← Int.cast_add, zmod, add_mul, add_div, map_add_eq_mul]

lemma zmod_injective : Injective (zmod n) := by
  simp_rw [Injective, ZMod.intCast_surjective.forall]
  rintro x y h
  have hn : (n : ℝ) ≠ 0 := NeZero.ne _
  simpa [pi_ne_zero, exp_inj, hn, CharP.intCast_eq_intCast (ZMod n) n] using
    (zmod_intCast ..).symm.trans <| (DFunLike.congr_fun h ((1 : ℤ) : ZMod n)).trans <|
      zmod_intCast ..

@[simp] lemma zmod_inj {x y : ZMod n} : zmod n x = zmod n y ↔ x = y := zmod_injective.eq_iff

def zmodHom : AddChar (ZMod n) (AddChar (ZMod n) Circle) where
  toFun := zmod n
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by simp

-- DISSOLVED: mkZModAux

-- DISSOLVED: mkZModAux_injective

def circleEquivComplex [Finite α] : AddChar α Circle ≃+ AddChar α ℂ where
  toFun ψ := toMonoidHomEquiv.symm <| coeHom.comp ψ.toMonoidHom
  invFun ψ :=
    { toFun := fun a ↦ (⟨ψ a, mem_sphere_zero_iff_norm.2 <| ψ.norm_apply _⟩ : Circle)
      map_zero_eq_one' := by simp [Circle]
      map_add_eq_mul' := fun a b ↦ by ext : 1; simp [map_add_eq_mul] }
  left_inv ψ := by ext : 1; simp
  right_inv ψ := by ext : 1; simp
  map_add' ψ χ := rfl

@[simp] lemma card_eq [Fintype α] : card (AddChar α ℂ) = card α := by
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' α
  classical
  have hn' i : NeZero (n i) := by have := hn i; exact ⟨by positivity⟩
  let f : α → AddChar α ℂ := fun a ↦ coeHom.compAddChar ((mkZModAux n <| e a).compAddMonoidHom e)
  have hf : Injective f := circleEquivComplex.injective.comp
    ((compAddMonoidHom_injective_left _ e.surjective).comp <| mkZModAux_injective.comp <|
      DFunLike.coe_injective.comp <| e.injective.comp Additive.ofMul.injective)
  exact (card_addChar_le _ _).antisymm (Fintype.card_le_of_injective _ hf)

def zmodAddEquiv : ZMod n ≃+ AddChar (ZMod n) ℂ := by
  refine AddEquiv.ofBijective
    (circleEquivComplex.toAddMonoidHom.comp <| AddChar.toAddMonoidHom zmodHom) ?_
  rw [Fintype.bijective_iff_injective_and_card, card_eq]
  exact ⟨circleEquivComplex.injective.comp zmod_injective, rfl⟩

@[simp] lemma zmodAddEquiv_apply (x : ZMod n) :
    zmodAddEquiv x = circleEquivComplex (zmod n x) := rfl

section Finite

variable (α) [Finite α]

def complexBasis : Basis (AddChar α ℂ) ℂ (α → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank (AddChar.linearIndependent _ _) <| by
    cases nonempty_fintype α; rw [card_eq, Module.finrank_fintype_fun_eq_card]

@[simp, norm_cast]
lemma coe_complexBasis : ⇑(complexBasis α) = ((⇑) : AddChar α ℂ → α → ℂ) := by
  rw [complexBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

variable {α}

@[simp]
lemma complexBasis_apply (ψ : AddChar α ℂ) : complexBasis α ψ = ψ := by rw [coe_complexBasis]

-- DISSOLVED: exists_apply_ne_zero

lemma forall_apply_eq_zero : (∀ ψ : AddChar α ℂ, ψ a = 1) ↔ a = 0 := by
  simpa using exists_apply_ne_zero.not

lemma doubleDualEmb_injective : Injective (doubleDualEmb : α → AddChar (AddChar α ℂ) ℂ) :=
  doubleDualEmb.ker_eq_bot_iff.1 <| eq_bot_iff.2 fun a ha ↦
    forall_apply_eq_zero.1 fun ψ ↦ by simpa using DFunLike.congr_fun ha (Additive.ofMul ψ)

lemma doubleDualEmb_bijective : Bijective (doubleDualEmb : α → AddChar (AddChar α ℂ) ℂ) := by
  cases nonempty_fintype α
  exact (Fintype.bijective_iff_injective_and_card _).2
    ⟨doubleDualEmb_injective, card_eq.symm.trans card_eq.symm⟩

@[simp]
lemma doubleDualEmb_inj : (doubleDualEmb a : AddChar (AddChar α ℂ) ℂ) = doubleDualEmb b ↔ a = b :=
  doubleDualEmb_injective.eq_iff

@[simp] lemma doubleDualEmb_eq_zero : (doubleDualEmb a : AddChar (AddChar α ℂ) ℂ) = 0 ↔ a = 0 := by
  rw [← map_zero doubleDualEmb, doubleDualEmb_inj]

-- DISSOLVED: doubleDualEmb_ne_zero

def doubleDualEquiv : α ≃+ AddChar (AddChar α ℂ) ℂ := .ofBijective _ doubleDualEmb_bijective

@[simp]
lemma coe_doubleDualEquiv : ⇑(doubleDualEquiv : α ≃+ AddChar (AddChar α ℂ) ℂ) = doubleDualEmb := rfl

@[simp] lemma doubleDualEmb_doubleDualEquiv_symm_apply (a : AddChar (AddChar α ℂ) ℂ) :
    doubleDualEmb (doubleDualEquiv.symm a) = a :=
  doubleDualEquiv.apply_symm_apply _

@[simp] lemma doubleDualEquiv_symm_doubleDualEmb_apply (a : AddChar (AddChar α ℂ) ℂ) :
    doubleDualEquiv.symm (doubleDualEmb a) = a := doubleDualEquiv.symm_apply_apply _

end Finite

lemma sum_apply_eq_ite [Fintype α] [DecidableEq α] (a : α) :
    ∑ ψ : AddChar α ℂ, ψ a = if a = 0 then (Fintype.card α : ℂ) else 0 := by
  simpa using sum_eq_ite (doubleDualEmb a : AddChar (AddChar α ℂ) ℂ)

lemma expect_apply_eq_ite [Fintype α] [DecidableEq α] (a : α) :
    𝔼 ψ : AddChar α ℂ, ψ a = if a = 0 then 1 else 0 := by
  simpa using expect_eq_ite (doubleDualEmb a : AddChar (AddChar α ℂ) ℂ)

-- DISSOLVED: sum_apply_eq_zero_iff_ne_zero

-- DISSOLVED: sum_apply_ne_zero_iff_eq_zero

-- DISSOLVED: expect_apply_eq_zero_iff_ne_zero

-- DISSOLVED: expect_apply_ne_zero_iff_eq_zero

end AddChar
