/-
Extracted from RingTheory/Noetherian/Basic.lean
Genuine: 28 of 46 | Dissolved: 0 | Infrastructure: 18
-/
import Origin.Core

/-!
# Noetherian rings and modules

The following are equivalent for a module M over a ring R:
1. Every increasing chain of submodules M₁ ⊆ M₂ ⊆ M₃ ⊆ ⋯ eventually stabilises.
2. Every submodule is finitely generated.

A module satisfying these equivalent conditions is said to be a *Noetherian* R-module.
A ring is a *Noetherian ring* if it is Noetherian as a module over itself.

(Note that we do not assume yet that our rings are commutative,
so perhaps this should be called "left-Noetherian".
To avoid cumbersome names once we specialize to the commutative case,
we don't make this explicit in the declaration names.)

## Main definitions

Let `R` be a ring and let `M` and `P` be `R`-modules. Let `N` be an `R`-submodule of `M`.

* `IsNoetherian R M` is the proposition that `M` is a Noetherian `R`-module. It is a class,
  implemented as the predicate that all `R`-submodules of `M` are finitely generated.

## Main statements

* `isNoetherian_iff` is the theorem that an R-module M is Noetherian iff `>` is well-founded on
  `Submodule R M`.

Note that the Hilbert basis theorem, that if a commutative ring R is Noetherian then so is R[X],
is proved in `RingTheory.Polynomial`.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]

## Tags

Noetherian, noetherian, Noetherian ring, Noetherian module, noetherian ring, noetherian module

-/

assert_not_exists Matrix

open Set Pointwise

variable {R S M P : Type*}

variable [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid P]

variable [Module R M] [Module S P]

open IsNoetherian

theorem isNoetherian_of_surjective {σ : R →+* S} [RingHomSurjective σ] (f : M →ₛₗ[σ] P)
    (hf : LinearMap.range f = ⊤) [IsNoetherian R M] :
    IsNoetherian S P :=
  ⟨fun s ↦
    have : (s.comap f).map f = s := Submodule.map_comap_eq_self <| hf.symm ▸ le_top
    this ▸ (IsNoetherian.noetherian _).map _⟩

-- INSTANCE (free from Core): isNoetherian_range

-- INSTANCE (free from Core): isNoetherian_quotient

theorem isNoetherian_of_linearEquiv {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ']
    [RingHomInvPair σ' σ] (f : M ≃ₛₗ[σ] P) [IsNoetherian R M] : IsNoetherian S P :=
  isNoetherian_of_surjective f.toLinearMap f.range

theorem LinearEquiv.isNoetherian_iff {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ']
    [RingHomInvPair σ' σ] (f : M ≃ₛₗ[σ] P) : IsNoetherian R M ↔ IsNoetherian S P :=
  ⟨fun _ ↦ isNoetherian_of_linearEquiv f, fun _ ↦ isNoetherian_of_linearEquiv f.symm⟩

theorem isNoetherian_top_iff : IsNoetherian R (⊤ : Submodule R M) ↔ IsNoetherian R M :=
  Submodule.topEquiv.isNoetherian_iff

theorem isNoetherian_of_injective [IsNoetherian S P] {σ : R →+* S} {σ' : S →+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M →ₛₗ[σ] P) (hf : Function.Injective f) :
    IsNoetherian R M :=
  isNoetherian_of_linearEquiv (LinearEquiv.ofInjective f hf).symm

theorem fg_of_injective [IsNoetherian S P] {N : Submodule R M} {σ : R →+* S} {σ' : S →+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M →ₛₗ[σ] P)
    (hf : Function.Injective f) : N.FG :=
  haveI := isNoetherian_of_injective f hf
  IsNoetherian.noetherian N

end

namespace Module

variable {R S M N : Type*}

variable [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]

variable (R M)

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): {R₁

variable {R M}

theorem Finite.of_injective [IsNoetherian S N] {σ : R →+* S} {σ' : S →+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M →ₛₗ[σ] N) (hf : Function.Injective f) :
    Module.Finite R M :=
  ⟨fg_of_injective f hf⟩

end Module

variable {R S M N P : Type*}

variable [Ring R] [Ring S] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]

variable [Module R M] [Module R N] [Module S P]

open IsNoetherian

theorem isNoetherian_of_ker_bot [IsNoetherian S P] {σ : R →+* S} {σ' : S →+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M →ₛₗ[σ] P) (hf : LinearMap.ker f = ⊥) :
    IsNoetherian R M :=
  isNoetherian_of_linearEquiv (LinearEquiv.ofInjective f <| LinearMap.ker_eq_bot.mp hf).symm

theorem fg_of_ker_bot [IsNoetherian S P] {N : Submodule R M} {σ : R →+* S} {σ' : S →+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M →ₛₗ[σ] P) (hf : LinearMap.ker f = ⊥) :
    N.FG :=
  haveI := isNoetherian_of_ker_bot f hf
  IsNoetherian.noetherian N

-- INSTANCE (free from Core): isNoetherian_prod

-- INSTANCE (free from Core): isNoetherian_sup

variable {ι : Type*} [Finite ι]

-- INSTANCE (free from Core): isNoetherian_pi

-- INSTANCE (free from Core): isNoetherian_pi'

-- INSTANCE (free from Core): isNoetherian_iSup

theorem isNoetherian_of_range_eq_ker {P : Type*} [AddCommGroup P] [Module R P] [IsNoetherian R M]
    [IsNoetherian R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : LinearMap.range f = LinearMap.ker g) :
    IsNoetherian R N :=
  isNoetherian_mk <|
    wellFounded_gt_exact_sequence
      (LinearMap.range f)
      (Submodule.map ((LinearMap.ker f).liftQ f le_rfl))
      (Submodule.comap ((LinearMap.ker f).liftQ f le_rfl))
      (Submodule.comap g.rangeRestrict) (Submodule.map g.rangeRestrict)
      (Submodule.gciMapComap <| LinearMap.ker_eq_bot.mp <| Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
      (Submodule.giMapComap g.surjective_rangeRestrict)
      (by simp [Submodule.map_comap_eq, inf_comm, Submodule.range_liftQ])
      (by simp [Submodule.comap_map_eq, h])

theorem isNoetherian_iff_submodule_quotient (S : Submodule R N) :
    IsNoetherian R N ↔ IsNoetherian R S ∧ IsNoetherian R (N ⧸ S) := by
  refine ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ ?_⟩
  apply isNoetherian_of_range_eq_ker S.subtype S.mkQ
  rw [Submodule.ker_mkQ, Submodule.range_subtype]

end

section CommRing

variable (R M N : Type*) [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
  [IsNoetherian R M] [Module.Finite R N]

-- INSTANCE (free from Core): isNoetherian_linearMap_pi

-- INSTANCE (free from Core): isNoetherian_linearMap

end CommRing

open IsNoetherian Submodule Function

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

theorem IsNoetherian.induction [IsNoetherian R M] {P : Submodule R M → Prop}
    (hgt : ∀ I, (∀ J > I, P J) → P I) (I : Submodule R M) : P I :=
  IsWellFounded.induction _ I hgt

theorem LinearMap.isNoetherian_iff_of_bijective {S P} [Semiring S] [AddCommMonoid P] [Module S P]
    {σ : R →+* S} [RingHomSurjective σ] (l : M →ₛₗ[σ] P) (hl : Function.Bijective l) :
    IsNoetherian R M ↔ IsNoetherian S P := by
  simp_rw [isNoetherian_iff']
  let e := Submodule.orderIsoMapComapOfBijective l hl
  exact ⟨fun _ ↦ e.symm.strictMono.wellFoundedGT, fun _ ↦ e.strictMono.wellFoundedGT⟩

end

variable {R M N P : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [IsNoetherian R M]

lemma Submodule.finite_ne_bot_of_iSupIndep {ι : Type*} {N : ι → Submodule R M} (h : iSupIndep N) :
    Set.Finite {i | N i ≠ ⊥} :=
  WellFoundedGT.finite_ne_bot_of_iSupIndep h

theorem LinearIndependent.finite_of_isNoetherian [Nontrivial R] {ι} {v : ι → M}
    (hv : LinearIndependent R v) : Finite ι :=
  WellFoundedGT.finite_of_iSupIndep hv.iSupIndep_span_singleton fun i _ ↦ hv.ne_zero i (by simp_all)

variable [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P] [Nontrivial P]

theorem IsNoetherian.subsingleton_of_injective {P : Type*} [AddCommMonoid P] [Module R P]
    {f : P × M →ₗ[R] M} (inj : Injective f) : Subsingleton P :=
  subsingleton_of_forall_eq 0 fun p ↦ by_contra fun _ ↦
    have ⟨g, inj⟩ := LinearMap.exists_finsupp_nat_of_prod_injective inj
    Infinite.not_finite <| WellFoundedGT.finite_of_iSupIndep
      (g.iSupIndep_map inj (iSupIndep_range_lsingle ℕ R P))
      fun i ↦ (Submodule.ne_bot_iff _).mpr ⟨_, ⟨_, ⟨p, rfl⟩, rfl⟩, by simpa [inj]⟩

theorem LinearIndependent.set_finite_of_isNoetherian [Nontrivial R] {s : Set M}
    (hi : LinearIndependent R ((↑) : s → M)) : s.Finite :=
  hi.finite_of_isNoetherian

theorem IsNoetherian.disjoint_partialSups_eventually_bot
    (f : ℕ → Submodule R M) (h : ∀ n, Disjoint (partialSups f n) (f (n + 1))) :
    ∃ n : ℕ, ∀ m, n ≤ m → f m = ⊥ := by
  -- A little off-by-one cleanup first:
  suffices t : ∃ n : ℕ, ∀ m, n ≤ m → f (m + 1) = ⊥ by
    obtain ⟨n, w⟩ := t
    use n + 1
    rintro (_ | m) p
    · cases p
    · apply w
      exact Nat.succ_le_succ_iff.mp p
  obtain ⟨n, w⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance (partialSups f)
  refine ⟨n, fun m p ↦ (h m).eq_bot_of_ge <| sup_eq_left.mp ?_⟩
  simpa only [partialSups_add_one] using (w (m + 1) <| le_add_right p).symm.trans <| w m p

end

-- INSTANCE (free from Core): (priority

theorem isNoetherian_of_submodule_of_noetherian (R M) [Semiring R] [AddCommMonoid M] [Module R M]
    (N : Submodule R M) (h : IsNoetherian R M) : IsNoetherian R N :=
  isNoetherian_mk ⟨OrderEmbedding.wellFounded (Submodule.MapSubtype.orderEmbedding N).dual h.wf⟩

theorem isNoetherian_of_tower (R) {S M} [Semiring R] [Semiring S] [AddCommMonoid M] [SMul R S]
    [Module S M] [Module R M] [IsScalarTower R S M] (h : IsNoetherian R M) : IsNoetherian S M :=
  isNoetherian_mk ⟨(Submodule.restrictScalarsEmbedding R S M).dual.wellFounded h.wf⟩

-- INSTANCE (free from Core): isNoetherian_of_isNoetherianRing_of_finite

theorem isNoetherian_of_fg_of_noetherian {R M} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) [I : IsNoetherianRing R] (hN : N.FG) : IsNoetherian R N :=
  haveI : Module.Finite R N := .of_fg hN; inferInstance

theorem isNoetherian_span_of_finite (R) {M} [Ring R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] {A : Set M} (hA : A.Finite) : IsNoetherian R (Submodule.span R A) :=
  isNoetherian_of_fg_of_noetherian _ (Submodule.fg_def.mpr ⟨A, hA, rfl⟩)

theorem IsNoetherianRing.of_finite (R S) [Ring R] [Ring S] [Module R S] [IsScalarTower R S S]
    [IsNoetherianRing R] [Module.Finite R S] : IsNoetherianRing S :=
  isNoetherian_of_tower R inferInstance

theorem isNoetherianRing_of_surjective (R) [Semiring R] (S) [Semiring S] (f : R →+* S)
    (hf : Function.Surjective f) [H : IsNoetherianRing R] : IsNoetherianRing S :=
  isNoetherian_mk ⟨OrderEmbedding.wellFounded (Ideal.orderEmbeddingOfSurjective f hf).dual H.wf⟩

-- INSTANCE (free from Core): isNoetherianRing_rangeS

-- INSTANCE (free from Core): isNoetherianRing_range

theorem isNoetherianRing_of_ringEquiv (R) [Semiring R] {S} [Semiring S] (f : R ≃+* S)
    [IsNoetherianRing R] : IsNoetherianRing S :=
  isNoetherianRing_of_surjective R S f.toRingHom f.toEquiv.surjective

-- INSTANCE (free from Core): {R

-- INSTANCE (free from Core): {ι}

namespace Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

theorem FG.of_le_of_isNoetherian {S T : Submodule R M} [IsNoetherian R T] (hST : S ≤ T) : S.FG :=
  isNoetherian_submodule.mp inferInstance _ hST

lemma FG.of_le [IsNoetherianRing R] {S T : Submodule R M} (hT : T.FG) (hST : S ≤ T) : S.FG := by
  rw [← Module.Finite.iff_fg] at hT
  exact FG.of_le_of_isNoetherian hST

end Submodule

universe w v u

variable (R : Type u) [CommRing R]

theorem Module.exists_finite_presentation [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] : ∃ (P : Type v) (_ : AddCommGroup P) (_ : Module R P) (_ : Module.Free R P)
      (_ : Module.Finite R P) (f : P →ₗ[R] M), Function.Surjective f := by
  rcases Module.Finite.exists_fin' R M with ⟨m, f', hf'⟩
  let f := f'.comp ((Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v} R R)).trans
      (Finsupp.linearEquivFunOnFinite R R (Fin m))).1
  use (Fin m →₀ Shrink.{v, u} R), inferInstance, inferInstance, inferInstance, inferInstance, f
  simpa [f] using hf'
