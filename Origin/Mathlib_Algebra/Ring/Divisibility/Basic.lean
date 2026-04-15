/-
Extracted from Algebra/Ring/Divisibility/Basic.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lemmas about divisibility in rings

Note that this file is imported by basic tactics like `linarith` and so must have only minimal
imports. Further results about divisibility in rings may be found in
`Mathlib/Algebra/Ring/Divisibility/Lemmas.lean` which is not subject to this import constraint.
-/

variable {α β : Type*}

section Semigroup

variable [Semigroup α] [Semigroup β] {F : Type*} [EquivLike F α β] [MulEquivClass F α β]

theorem map_dvd_iff (f : F) {a b} : f a ∣ f b ↔ a ∣ b :=
  let f := MulEquivClass.toMulEquiv f
  ⟨fun h ↦ by rw [← f.left_inv a, ← f.left_inv b]; exact map_dvd f.symm h, map_dvd f⟩

theorem map_dvd_iff_dvd_symm (f : F) {a : α} {b : β} :
    f a ∣ b ↔ a ∣ (MulEquivClass.toMulEquiv f).symm b := by
  obtain ⟨c, rfl⟩ : ∃ c, f c = b := EquivLike.surjective f b
  simp [map_dvd_iff]

theorem MulEquiv.decompositionMonoid (f : F) [DecompositionMonoid β] : DecompositionMonoid α where
  primal a b c h := by
    rw [← map_dvd_iff f, map_mul] at h
    obtain ⟨a₁, a₂, h⟩ := DecompositionMonoid.primal _ h
    refine ⟨symm f a₁, symm f a₂, ?_⟩
    simp_rw [← map_dvd_iff f, ← map_mul, eq_symm_apply]
    iterate 2 erw [(f : α ≃* β).apply_symm_apply]
    exact h

protected noncomputable def Equiv.dvd {G : Type*} [LeftCancelSemigroup G] (g : G) :
    G ≃ {a : G // g ∣ a} where
  toFun := fun a ↦ ⟨g * a, ⟨a, rfl⟩⟩
  invFun := fun ⟨_, h⟩ ↦ h.choose
  left_inv := fun _ ↦ by simp
  right_inv := by
    rintro ⟨_, ⟨_, rfl⟩⟩
    simp
