/-
Extracted from RingTheory/Noetherian/Orzech.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Noetherian rings have the Orzech property

## Main results

* `IsNoetherian.injective_of_surjective_of_injective`: if `M` and `N` are `R`-modules for a ring `R`
  (not necessarily commutative), `M` is Noetherian, `i : N →ₗ[R] M` is injective,
  `f : N →ₗ[R] M` is surjective, then `f` is also injective.
* `IsNoetherianRing.orzechProperty`: Any Noetherian ring satisfies the Orzech property.
-/

open Set Filter Pointwise

open IsNoetherian Submodule Function

universe w

variable {R M P : Type*} {N : Type w} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [AddCommGroup P] [Module R P] [IsNoetherian R M]

theorem IsNoetherian.injective_of_surjective_of_injective (i f : N →ₗ[R] M)
    (hi : Injective i) (hf : Surjective f) : Injective f := by
  haveI := isNoetherian_of_injective i hi
  obtain ⟨n, H⟩ := monotone_stabilizes_iff_noetherian.2 ‹_›
    ⟨_, monotone_nat_of_le_succ <| f.iterateMapComap_le_succ i ⊥ (by simp)⟩
  exact LinearMap.ker_eq_bot.1 <| bot_unique <|
    f.ker_le_of_iterateMapComap_eq_succ i ⊥ n (H _ (Nat.le_succ _)) hf hi

theorem IsNoetherian.injective_of_surjective_of_submodule
    {N : Submodule R M} (f : N →ₗ[R] M) (hf : Surjective f) : Injective f :=
  IsNoetherian.injective_of_surjective_of_injective N.subtype f N.injective_subtype hf

theorem IsNoetherian.injective_of_surjective_endomorphism (f : M →ₗ[R] M)
    (s : Surjective f) : Injective f :=
  IsNoetherian.injective_of_surjective_of_injective _ f (LinearEquiv.refl _ _).injective s

theorem IsNoetherian.bijective_of_surjective_endomorphism (f : M →ₗ[R] M)
    (s : Surjective f) : Bijective f :=
  ⟨IsNoetherian.injective_of_surjective_endomorphism f s, s⟩

theorem IsNoetherian.subsingleton_of_prod_injective (f : M × N →ₗ[R] M)
    (i : Injective f) : Subsingleton N := .intro fun x y ↦ by
  have h := IsNoetherian.injective_of_surjective_of_injective f _ i LinearMap.fst_surjective
  simpa using h (show LinearMap.fst R M N (0, x) = LinearMap.fst R M N (0, y) from rfl)
