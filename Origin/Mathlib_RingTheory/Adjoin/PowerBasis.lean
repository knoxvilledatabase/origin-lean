/-
Extracted from RingTheory/Adjoin/PowerBasis.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Power basis for `R[x]`

This file defines the canonical power basis on `R[x]`,
where `x` is an integral element over `R`.
-/

open Module Polynomial PowerBasis

variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]

namespace Algebra

noncomputable def adjoin.powerBasisAux {x : S} (hx : IsIntegral K x) :
    Basis (Fin (minpoly K x).natDegree) K (K[(x : S)]) := by
  have hST : Function.Injective (algebraMap (K[(x : S)]) S) := Subtype.coe_injective
  have hx' :
    IsIntegral K (⟨x, subset_adjoin (Set.mem_singleton x)⟩ : K[(x : S)]) := by
    apply (isIntegral_algebraMap_iff hST).mp
    convert hx
  apply Basis.mk (v := fun i : Fin _ ↦ ⟨x, subset_adjoin (Set.mem_singleton x)⟩ ^ (i : ℕ))
  · have : LinearIndependent K _ := linearIndependent_pow
      (⟨x, self_mem_adjoin_singleton _ _⟩ : K[x])
    rwa [← minpoly.algebraMap_eq hST] at this
  · rintro ⟨y, hy⟩ _
    have := hx'.mem_span_pow (y := ⟨y, hy⟩)
    rw [← minpoly.algebraMap_eq hST] at this
    apply this
    rw [adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨f, rfl⟩ := (aeval x).mem_range.mp hy
    use f
    ext
    exact aeval_algebraMap_apply S (⟨x, _⟩ : K[x]) _
