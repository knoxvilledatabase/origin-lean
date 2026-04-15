/-
Extracted from RingTheory/Valuation/ExtendToLocalization.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Extending valuations to a localization

We show that, given a valuation `v` taking values in a linearly ordered commutative *group*
with zero `Γ`, and a submonoid `S` of `v.supp.primeCompl`, the valuation `v` can be naturally
extended to the localization `S⁻¹A`.

-/

variable {A : Type*} [CommRing A] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation A Γ) {S : Submonoid A} (hS : S ≤ v.supp.primeCompl) (B : Type*) [CommRing B]
  [Algebra A B] [IsLocalization S B]

noncomputable def Valuation.extendToLocalization : Valuation B Γ :=
  let f := IsLocalization.toLocalizationMap S B
  let h : ∀ s : S, IsUnit (v.1.toMonoidHom s) := fun s => isUnit_iff_ne_zero.2 (hS s.2)
  { f.lift h with
    map_zero' := by convert f.lift_eq (P := Γ) _ 0 <;> simp [f]
    map_add_le_max' := fun x y => by
      obtain ⟨a, b, s, rfl, rfl⟩ : ∃ (a b : A) (s : S), f.mk' a s = x ∧ f.mk' b s = y := by
        obtain ⟨a, s, rfl⟩ := f.mk'_surjective x
        obtain ⟨b, t, rfl⟩ := f.mk'_surjective y
        use a * t, b * s, s * t
        constructor <;>
          · rw [f.mk'_eq_iff_eq, Submonoid.coe_mul]
            ring_nf
      convert_to f.lift h (f.mk' (a + b) s) ≤ max (f.lift h _) (f.lift h _)
      · refine congr_arg (f.lift h) (IsLocalization.eq_mk'_iff_mul_eq.2 ?_)
        rw [add_mul, map_add]
        rw [← IsLocalization.toLocalizationMap_apply S B, f.mk'_spec, f.mk'_spec,
          IsLocalization.toLocalizationMap_apply,
          IsLocalization.toLocalizationMap_apply]
      iterate 3 rw [f.lift_mk']
      dsimp
      grw [max_mul_mul_right, v.map_add a b] }
