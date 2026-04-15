/-
Extracted from NumberTheory/ModularForms/Basic.lean
Genuine: 8 of 10 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Modular forms

This file defines modular forms and proves some basic properties about them. Including constructing
the graded ring of modular forms.

We begin by defining modular forms and cusp forms as extension of `SlashInvariantForm`s then we
define the space of modular forms, cusp forms and prove that the product of two modular forms is a
modular form.
-/

open Complex UpperHalfPlane Matrix.SpecialLinearGroup

open scoped Topology Manifold MatrixGroups ComplexConjugate

noncomputable section

section ModularForm

open ModularForm

private lemma MDifferentiable.slash_of_pos {f : ℍ → ℂ} (hf : MDiff f)
    (k : ℤ) {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) :
    MDiff (f ∣[k] g) := by
  refine .mul (.mul ?_ mdifferentiable_const) (mdifferentiable_denom_zpow g _)
  simpa only [σ, hg, ↓reduceIte] using hf.comp (mdifferentiable_smul hg)

private lemma slash_J (f : ℍ → ℂ) (k : ℤ) :
    f ∣[k] J = fun τ : ℍ ↦ conj (f <| ofComplex <| -(conj ↑τ)) := by
  simp [slash_def, J_smul]

private lemma MDifferentiable.slashJ {f : ℍ → ℂ} (hf : MDiff f) (k : ℤ) :
    MDiff (f ∣[k] J) := by
  simp only [mdifferentiable_iff, slash_J, Function.comp_def] at hf ⊢
  have : {z | 0 < z.im}.EqOn (fun x ↦ conj (f <| ofComplex <| -conj ↑(ofComplex x)))
      (fun x ↦ conj (f <| ofComplex <| -conj x)) := fun z h ↦ by simp [ofComplex_apply_of_im_pos h]
  refine .congr (fun z hz ↦ DifferentiableAt.differentiableWithinAt ?_) this
  have : 0 < (-conj z).im := by simpa using hz
  have := hf.differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds this)
  simpa using (this.comp _ differentiable_neg.differentiableAt).star_star.neg

lemma MDifferentiable.slash {f : ℍ → ℂ} (hf : MDiff f)
    (k : ℤ) (g : GL (Fin 2) ℝ) : MDiff (f ∣[k] g) := by
  refine g.det_ne_zero.lt_or_gt.elim (fun hg ↦ ?_) (hf.slash_of_pos k)
  rw [show g = J * (J * g) by simp [← mul_assoc, ← sq], SlashAction.slash_mul]
  exact (hf.slashJ k).slash_of_pos _ (by simpa using hg)

variable (F : Type*) (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ)

open scoped ModularForm

structure ModularForm extends SlashInvariantForm Γ k where
  holo' : MDiff (toSlashInvariantForm : ℍ → ℂ)
  bdd_at_cusps' {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsBoundedAt toFun k

add_decl_doc ModularForm.toSlashInvariantForm

structure CuspForm extends SlashInvariantForm Γ k where
  holo' : MDiff (toSlashInvariantForm : ℍ → ℂ)
  zero_at_cusps' {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsZeroAt toFun k

add_decl_doc CuspForm.toSlashInvariantForm

class ModularFormClass (F : Type*) (Γ : outParam <| Subgroup (GL (Fin 2) ℝ)) (k : outParam ℤ)
    [FunLike F ℍ ℂ] : Prop extends SlashInvariantFormClass F Γ k where
  holo : ∀ f : F, MDiff (f : ℍ → ℂ)
  bdd_at_cusps (f : F) {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsBoundedAt f k

class CuspFormClass (F : Type*) (Γ : outParam <| Subgroup (GL (Fin 2) ℝ)) (k : outParam ℤ)
    [FunLike F ℍ ℂ] : Prop extends SlashInvariantFormClass F Γ k where
  holo : ∀ f : F, MDiff (f : ℍ → ℂ)
  zero_at_cusps (f : F) {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsZeroAt f k

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority
