/-
Extracted from RingTheory/Ideal/AssociatedPrime/Finiteness.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Finitely generated module over Noetherian ring have finitely many associated primes.

In this file we proved that any finitely generated module over a Noetherian ring have finitely many
associated primes.

## Main results

* `IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime`: If `A` is a Noetherian ring
  and `M` is a finitely generated `A`-module, then there exists a chain of submodules
  `0 = M₀ ≤ M₁ ≤ M₂ ≤ ... ≤ Mₙ = M` of `M`, such that for each `0 ≤ i < n`,
  `Mᵢ₊₁ / Mᵢ` is isomorphic to `A / pᵢ` for some prime ideal `pᵢ` of `A`.

* `IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime`: If a property on
  finitely generated modules over a Noetherian ring satisfies that:

  - it holds for zero module,
  - it holds for any module isomorphic to some `A ⧸ p` where `p` is a prime ideal of `A`,
  - it is stable by short exact sequences,

  then the property holds for every finitely generated modules.

* `associatedPrimes.finite`: There are only finitely many associated primes of a
  finitely generated module over a Noetherian ring.

-/

universe u v

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

def Submodule.IsQuotientEquivQuotientPrime (N₁ N₂ : Submodule A M) :=
  N₁ ≤ N₂ ∧ ∃ (p : PrimeSpectrum A), Nonempty ((↥N₂ ⧸ N₁.submoduleOf N₂) ≃ₗ[A] A ⧸ p.1)

set_option backward.isDefEq.respectTransparency false in

open LinearMap in

theorem Submodule.isQuotientEquivQuotientPrime_iff {N₁ N₂ : Submodule A M} :
    N₁.IsQuotientEquivQuotientPrime N₂ ↔
      ∃ x, Ideal.IsPrime ((⊥ : Submodule A (M ⧸ N₁)).colon {N₁.mkQ x}) ∧ N₂ = N₁ ⊔ span A {x} := by
  let f := mapQ (N₁.submoduleOf N₂) N₁ N₂.subtype le_rfl
  have hf₁ : ker f = ⊥ := ker_liftQ_eq_bot _ _ _ (by simp [ker_comp, submoduleOf])
  have hf₂ : range f = N₂.map N₁.mkQ := by simp [f, mapQ, range_liftQ, range_comp]
  refine ⟨fun ⟨h, p, ⟨e⟩⟩ ↦ ?_, fun ⟨x, hx, hx'⟩ ↦ ⟨le_sup_left.trans_eq hx'.symm, ⟨_, hx⟩, ?_⟩⟩
  · obtain ⟨⟨x, hx⟩, hx'⟩ := Submodule.mkQ_surjective _ (e.symm 1)
    have hx'' : N₁.mkQ x = f (e.symm 1) := by simp [f, ← hx']
    refine ⟨x, ?_, ?_⟩
    · convert p.2
      ext r
      simp [hx'', ← map_smul, Algebra.smul_def, show f _ = 0 ↔ _ from congr(_ ∈ $hf₁),
        Ideal.Quotient.eq_zero_iff_mem]
    · refine le_antisymm ?_ (sup_le h ((span_singleton_le_iff_mem _ _).mpr hx))
      have : (span A {x}).map N₁.mkQ = ((span A {1}).map e.symm.toLinearMap).map f := by
        simp only [map_span, Set.image_singleton, hx'', LinearEquiv.coe_coe]
      rw [← N₁.ker_mkQ, sup_comm, ← comap_map_eq, ← map_le_iff_le_comap, this]
      simp [hf₂, Ideal.Quotient.span_singleton_one]
  · have hxN₂ : x ∈ N₂ := (le_sup_right.trans_eq hx'.symm) (mem_span_singleton_self x)
    refine ⟨.symm (.ofBijective (Submodule.mapQ _ _ (toSpanSingleton A _ ⟨x, hxN₂⟩) ?_) ⟨?_, ?_⟩)⟩
    · simp [SetLike.le_def, ← Quotient.mk_smul, submoduleOf]
    · refine ker_eq_bot.mp (ker_liftQ_eq_bot _ _ _ ?_)
      simp [← Quotient.mk_smul, SetLike.le_def, submoduleOf]
    · rw [mapQ, ← range_eq_top, range_liftQ, range_comp]
      have := congr($(hx').submoduleOf N₂)
      rw [submoduleOf_self, submoduleOf_sup_of_le (by simp_all) (by simp_all),
        submoduleOf_span_singleton_of_mem _ hxN₂] at this
      simpa [← span_singleton_eq_range, LinearMap.range_toSpanSingleton] using this.symm

variable (A M) [IsNoetherianRing A] [Module.Finite A M]
