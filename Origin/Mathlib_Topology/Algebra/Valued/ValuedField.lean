/-
Extracted from Topology/Algebra/Valued/ValuedField.lean
Genuine: 5 of 11 | Dissolved: 2 | Infrastructure: 4
-/
import Origin.Core

/-!
# Valued fields and their completions

In this file we study the topology of a field `K` endowed with a valuation (in our application
to adic spaces, `K` will be the valuation field associated to some valuation on a ring, defined in
valuation.basic).

We already know from valuation.topology that one can build a topology on `K` which
makes it a topological ring.

The first goal is to show `K` is a topological *field*, i.e. inversion is continuous
at every non-zero element.

The next goal is to prove `K` is a *completable* topological field. This gives us
a completion `hat K` which is a topological field. We also prove that `K` is automatically
separated, so the map from `K` to `hat K` is injective.

Then we extend the valuation given on `K` to a valuation on `hat K`.
-/

open Filter Set

open Topology

section DivisionRing

variable {K : Type*} [DivisionRing K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

section ValuationTopologicalDivisionRing

section InversionEstimate

variable (v : Valuation K Γ₀)

-- DISSOLVED: Valuation.inversion_estimate

-- DISSOLVED: Valuation.inversion_estimate'

end InversionEstimate

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀ Valued

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

open WithZeroTopology

open Valued

theorem Valued.continuous_valuation [hv : Valued K Γ₀] :
    Continuous (v.restrict : K → (ValueGroup₀ hv.v)) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with (rfl | h)
  · rw [ContinuousAt, map_zero, WithZeroTopology.tendsto_zero]
    intro γ hγ
    rw [Filter.Eventually, Valued.mem_nhds_zero]
    use Units.mk0 γ hγ; rfl
  · have v_ne : (v.restrict x : ValueGroup₀ hv.v) ≠ 0 := (Valuation.ne_zero_iff _).mpr h
    rw [ContinuousAt, WithZeroTopology.tendsto_of_ne_zero v_ne]
    simp_rw [v.restrict_inj]
    apply Valued.locally_const (by simpa [restrict₀_apply] using v_ne)

theorem Valued.continuous_valuation_of_surjective [hv : Valued K Γ₀]
    (hsurj : Function.Surjective hv.v) : Continuous hv.v := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with (rfl | h)
  · rw [ContinuousAt, map_zero, WithZeroTopology.tendsto_zero]
    intro γ hγ
    rw [Filter.Eventually, Valued.mem_nhds_zero]
    obtain ⟨x, hx⟩ := hsurj γ
    use Units.mk0 (restrict₀ hv.v x) (by simp [restrict₀_apply, hx, hγ])
    simp only [Units.val_mk0, setOf_subset_setOf, ← v.restrict_def, Valuation.restrict_lt_iff, hx,
      imp_self, implies_true]
  · have h0 : hv.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr h
    rw [ContinuousAt, WithZeroTopology.tendsto_of_ne_zero h0]
    exact Valued.locally_const (by simpa using h0)

end

end ValuationTopologicalDivisionRing

end DivisionRing

namespace Valued

open UniformSpace

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀]

local notation "hat " => Completion

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): (priority

open MonoidWithZeroHom WithZeroTopology

lemma valuation_isClosedMap : IsClosedMap (v.restrict : K → (ValueGroup₀ hv.v)) := by
  refine IsClosedMap.of_nonempty ?_
  intro U hU hU'
  simp only [← isOpen_compl_iff, isOpen_iff_mem_nhds, mem_compl_iff, mem_nhds, subset_compl_comm,
    compl_setOf, not_lt] at hU
  simp only [isClosed_iff, mem_image, map_eq_zero, exists_eq_right, ne_eq, image_subset_iff]
  refine (em _).imp_right fun h ↦ ?_
  obtain ⟨γ, h⟩ := hU _ h
  simp only [sub_zero] at h
  refine ⟨γ.1, γ.ne_zero, h.trans ?_⟩
  intro
  simp

-- INSTANCE (free from Core): :

noncomputable def extension : hat K → ValueGroup₀ hv.v :=
  Completion.isDenseInducing_coe.extend (v.restrict : K → (ValueGroup₀ hv.v))

set_option backward.isDefEq.respectTransparency false in

theorem continuous_extension : Continuous (Valued.extension : hat K → ValueGroup₀ hv.v) := by
  refine Completion.isDenseInducing_coe.continuous_extend ?_
  intro x₀
  rcases eq_or_ne x₀ 0 with (rfl | h)
  · refine ⟨0, ?_⟩
    rw [← Completion.coe_zero, ← Completion.isDenseInducing_coe.isInducing.nhds_eq_comap]
    exact Valued.continuous_valuation.tendsto' 0 0 (map_zero v.restrict)
  · have preimage_one : v ⁻¹' {(1 : Γ₀)} ∈ 𝓝 (1 : K) := by
      have : (v (1 : K) : Γ₀) ≠ 0 := by
        rw [Valuation.map_one]
        exact zero_ne_one.symm
      convert Valued.locally_const this
      ext x
      rw [Valuation.map_one, mem_preimage, mem_singleton_iff, mem_setOf_eq]
    obtain ⟨V, V_in, hV⟩ : ∃ V ∈ 𝓝 (1 : hat K), ∀ x : K, (x : hat K) ∈ V → (v x : Γ₀) = 1 := by
      rwa [Completion.isDenseInducing_coe.nhds_eq_comap, mem_comap] at preimage_one
    have : ∃ V' ∈ 𝓝 (1 : hat K), (0 : hat K) ∉ V' ∧ ∀ (x) (_ : x ∈ V') (y) (_ : y ∈ V'),
      x * y⁻¹ ∈ V := by
      have : Tendsto (fun p : hat K × hat K => p.1 * p.2⁻¹) ((𝓝 1) ×ˢ (𝓝 1)) (𝓝 1) := by
        rw [← nhds_prod_eq]
        conv =>
          congr
          rfl
          rfl
          rw [← one_mul (1 : hat K)]
        refine
          Tendsto.mul continuous_fst.continuousAt (Tendsto.comp ?_ continuous_snd.continuousAt)
        convert (continuousAt_inv₀ (zero_ne_one.symm : 1 ≠ (0 : hat K))).tendsto
        exact inv_one.symm
      rcases tendsto_prod_self_iff.mp this V V_in with ⟨U, U_in, hU⟩
      let hatKstar := ({0}ᶜ : Set <| hat K)
      have : hatKstar ∈ 𝓝 (1 : hat K) := compl_singleton_mem_nhds zero_ne_one.symm
      exact ⟨U ∩ hatKstar, Filter.inter_mem U_in this,
        ⟨fun ⟨_, h'⟩ ↦ h' rfl, fun x ⟨hx, _⟩ y ⟨hy, _⟩ ↦ hU _ _  hx hy⟩⟩
    rcases this with ⟨V', V'_in, zeroV', hV'⟩
    have nhds_right : (fun x => x * x₀) '' V' ∈ 𝓝 x₀ := by
      have l : Function.LeftInverse (fun x : hat K => x * x₀⁻¹) fun x : hat K => x * x₀ := by
        intro x
        simp only [mul_assoc, mul_inv_cancel₀ h, mul_one]
      have r : Function.RightInverse (fun x : hat K => x * x₀⁻¹) fun x : hat K => x * x₀ := by
        intro x
        simp only [mul_assoc, inv_mul_cancel₀ h, mul_one]
      have c : Continuous fun x : hat K => x * x₀⁻¹ := by fun_prop
      rw [image_eq_preimage_of_inverse l r]
      rw [← mul_inv_cancel₀ h] at V'_in
      exact c.continuousAt V'_in
    have : ∃ z₀ : K, ∃ y₀ ∈ V', ↑z₀ = y₀ * x₀ ∧ z₀ ≠ 0 := by
      rcases Completion.denseRange_coe.mem_nhds nhds_right with ⟨z₀, y₀, y₀_in, H : y₀ * x₀ = z₀⟩
      refine ⟨z₀, y₀, y₀_in, ⟨H.symm, ?_⟩⟩
      rintro rfl
      exact mul_ne_zero (ne_of_mem_of_not_mem y₀_in zeroV') h H
    rcases this with ⟨z₀, y₀, y₀_in, hz₀, z₀_ne⟩
    have vz₀_ne : v.restrict z₀ ≠ 0 := by rwa [Valuation.ne_zero_iff]
    refine ⟨v.restrict z₀, ?_⟩
    rw [WithZeroTopology.tendsto_of_ne_zero vz₀_ne, eventually_comap]
    filter_upwards [nhds_right] with x x_in a ha
    rcases x_in with ⟨y, y_in, rfl⟩
    have : (v.restrict (a * z₀⁻¹)) = 1 := by
      rw [v.restrict_def, ValueGroup₀.restrict₀_eq_one_iff]
      apply hV
      have : (z₀⁻¹ : K) = (z₀ : hat K)⁻¹ := map_inv₀ (Completion.coeRingHom : K →+* hat K) z₀
      rw [Completion.coe_mul, this, ha, hz₀, mul_inv, mul_comm y₀⁻¹, ← mul_assoc, mul_assoc y,
        mul_inv_cancel₀ h, mul_one]
      solve_by_elim
    calc
      v.restrict a = v.restrict (a * z₀⁻¹ * z₀) := by rw [mul_assoc, inv_mul_cancel₀ z₀_ne, mul_one]
      _ = v.restrict (a * z₀⁻¹) * v.restrict z₀ := Valuation.map_mul _ _ _
      _ = v.restrict z₀ := by rw [this, one_mul]
