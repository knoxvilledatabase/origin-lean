/-
Extracted from RingTheory/Artinian/Module.lean
Genuine: 47 of 67 | Dissolved: 0 | Infrastructure: 20
-/
import Origin.Core

/-!
# Artinian rings and modules

A module satisfying these equivalent conditions is said to be an *Artinian* R-module
if every decreasing chain of submodules is eventually constant, or equivalently,
if the relation `<` on submodules is well founded.

A ring is said to be left (or right) Artinian if it is Artinian as a left (or right) module over
itself, or simply Artinian if it is both left and right Artinian.

## Main results

* `IsArtinianRing.primeSpectrum_finite`, `IsArtinianRing.isMaximal_of_isPrime`: there are only
  finitely prime ideals in a commutative Artinian ring, and each of them is maximal.

* `IsArtinianRing.equivPi`: a reduced commutative Artinian ring `R` is isomorphic to a finite
  product of fields (and therefore is a semisimple ring and a decomposition monoid; moreover
  `R[X]` is also a decomposition monoid).

* `IsArtinian.isSemisimpleModule_iff_jacobson`: an Artinian module is semisimple
  iff its Jacobson radical is zero.

* `instIsSemiprimaryRingOfIsArtinianRing`: an Artinian ring `R` is semiprimary, in particular
  the Jacobson radical of `R` is a nilpotent ideal (`IsArtinianRing.isNilpotent_jacobson_bot`).

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]

## Tags

Artinian, artinian, Artinian ring, Artinian module, artinian ring, artinian module

-/

open Set Filter Pointwise

section Semiring

variable {R M P N : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid P] [AddCommMonoid N]

variable [Module R M] [Module R P] [Module R N]

theorem LinearMap.isArtinian_iff_of_bijective {S P} [Semiring S] [AddCommMonoid P] [Module S P]
    {σ : R →+* S} [RingHomSurjective σ] (l : M →ₛₗ[σ] P) (hl : Function.Bijective l) :
    IsArtinian R M ↔ IsArtinian S P :=
  let e := Submodule.orderIsoMapComapOfBijective l hl
  ⟨fun _ ↦ e.symm.strictMono.wellFoundedLT, fun _ ↦ e.strictMono.wellFoundedLT⟩

theorem isArtinian_of_injective (f : M →ₗ[R] P) (h : Function.Injective f) [IsArtinian R P] :
    IsArtinian R M :=
  ⟨Subrelation.wf
    (fun {A B} hAB => show A.map f < B.map f from Submodule.map_strictMono_of_injective h hAB)
    (InvImage.wf (Submodule.map f) IsWellFounded.wf)⟩

-- INSTANCE (free from Core): isArtinian_submodule'

theorem isArtinian_of_le {s t : Submodule R M} [IsArtinian R t] (h : s ≤ t) : IsArtinian R s :=
  isArtinian_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)

variable (M) in

theorem isArtinian_of_surjective (f : M →ₗ[R] P) (hf : Function.Surjective f) [IsArtinian R M] :
    IsArtinian R P :=
  ⟨Subrelation.wf
    (fun {A B} hAB =>
      show A.comap f < B.comap f from Submodule.comap_strictMono_of_surjective hf hAB)
    (InvImage.wf (Submodule.comap f) IsWellFounded.wf)⟩

theorem isArtinian_of_surjective_algebraMap {S : Type*} [CommSemiring S] [Algebra S R]
    [Module S M] [IsArtinian R M] [IsScalarTower S R M]
    (H : Function.Surjective (algebraMap S R)) : IsArtinian S M := by
  apply (OrderEmbedding.wellFoundedLT (β := Submodule R M))
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro N
    refine { toAddSubmonoid := N.toAddSubmonoid, smul_mem' := ?_ }
    intro c x hx
    obtain ⟨r, rfl⟩ := H c
    suffices r • x ∈ N by simpa [Algebra.algebraMap_eq_smul_one, smul_assoc]
    apply N.smul_mem _ hx
  · intro N1 N2 h
    rwa [Submodule.ext_iff] at h ⊢
  · intro N1 N2
    rfl

-- INSTANCE (free from Core): isArtinian_range

theorem isArtinian_of_linearEquiv (f : M ≃ₗ[R] P) [IsArtinian R M] : IsArtinian R P :=
  isArtinian_of_surjective _ f.toLinearMap f.toEquiv.surjective

theorem LinearEquiv.isArtinian_iff (f : M ≃ₗ[R] P) : IsArtinian R M ↔ IsArtinian R P :=
  ⟨fun _ ↦ isArtinian_of_linearEquiv f, fun _ ↦ isArtinian_of_linearEquiv f.symm⟩

lemma isArtinian_of_finite [Finite M] : IsArtinian R M :=
  ⟨Finite.wellFounded_of_trans_of_irrefl _⟩

open Submodule

theorem IsArtinian.finite_of_linearIndependent [Nontrivial R] [h : IsArtinian R M] {s : Set M}
    (hs : LinearIndependent R ((↑) : s → M)) : s.Finite :=
  WellFoundedLT.finite_of_iSupIndep hs.iSupIndep_span_singleton fun i _ ↦ hs.ne_zero i (by simp_all)

theorem set_has_minimal_iff_artinian :
    (∀ a : Set <| Submodule R M, a.Nonempty → ∃ M' ∈ a, ∀ I ∈ a, ¬I < M') ↔ IsArtinian R M := by
  rw [isArtinian_iff, WellFounded.wellFounded_iff_has_min]

theorem IsArtinian.set_has_minimal [IsArtinian R M] (a : Set <| Submodule R M) (ha : a.Nonempty) :
    ∃ M' ∈ a, ∀ I ∈ a, ¬I < M' :=
  set_has_minimal_iff_artinian.mpr ‹_› a ha

theorem monotone_stabilizes_iff_artinian :
    (∀ f : ℕ →o (Submodule R M)ᵒᵈ, ∃ n, ∀ m, n ≤ m → f n = f m) ↔ IsArtinian R M :=
  wellFoundedGT_iff_monotone_chain_condition.symm

namespace IsArtinian

variable [IsArtinian R M]

theorem monotone_stabilizes (f : ℕ →o (Submodule R M)ᵒᵈ) : ∃ n, ∀ m, n ≤ m → f n = f m :=
  monotone_stabilizes_iff_artinian.mpr ‹_› f

theorem eventuallyConst_of_isArtinian (f : ℕ →o (Submodule R M)ᵒᵈ) :
    atTop.EventuallyConst f := by
  simp_rw [eventuallyConst_atTop, eq_comm]
  exact monotone_stabilizes f

open Function

theorem surjective_of_injective_endomorphism (f : M →ₗ[R] M) (s : Injective f) : Surjective f := by
  have h := ‹IsArtinian R M›; contrapose h
  rw [IsArtinian, WellFoundedLT, isWellFounded_iff]
  refine (RelEmbedding.natGT (LinearMap.range <| f ^ ·) ?_).not_wellFounded
  intro n
  simp_rw [pow_succ, Module.End.mul_eq_comp, LinearMap.range_comp, ← Submodule.map_top (f ^ n)]
  refine Submodule.map_strictMono_of_injective (Module.End.iterate_injective s n) (Ne.lt_top ?_)
  rwa [Ne, LinearMap.range_eq_top]

theorem bijective_of_injective_endomorphism (f : M →ₗ[R] M) (s : Injective f) : Bijective f :=
  ⟨s, surjective_of_injective_endomorphism f s⟩

theorem disjoint_partial_infs_eventually_top (f : ℕ → Submodule R M)
    (h : ∀ n, Disjoint (partialSups (OrderDual.toDual ∘ f) n) (OrderDual.toDual (f (n + 1)))) :
    ∃ n : ℕ, ∀ m, n ≤ m → f m = ⊤ := by
  -- A little off-by-one cleanup first:
  rsuffices ⟨n, w⟩ : ∃ n : ℕ, ∀ m, n ≤ m → OrderDual.toDual f (m + 1) = ⊤
  · use n + 1
    rintro (_ | m) p
    · cases p
    · apply w
      exact Nat.succ_le_succ_iff.mp p
  obtain ⟨n, w⟩ := monotone_stabilizes (partialSups (OrderDual.toDual ∘ f))
  refine ⟨n, fun m p ↦ (h m).eq_bot_of_ge <| sup_eq_left.mp ?_⟩
  simpa only [partialSups_add_one] using (w (m + 1) <| le_add_right p).symm.trans <| w m p

end IsArtinian

lemma IsArtinian.subsingleton_of_injective [IsArtinian R N] {f : P × N →ₗ[R] N}
    (inj : Function.Injective f) : Subsingleton P :=
  subsingleton_of_forall_eq 0 fun p ↦
    have ⟨_, eq⟩ := IsArtinian.surjective_of_injective_endomorphism (f ∘ₗ .inr ..)
      (inj.comp (Prod.mk_right_injective _)) (f (p, 0))
    congr($(inj eq).1).symm

namespace LinearMap

variable [IsArtinian R M]

lemma eventually_iInf_range_pow_eq (f : Module.End R M) :
    ∀ᶠ n in atTop, ⨅ m, LinearMap.range (f ^ m) = LinearMap.range (f ^ n) := by
  obtain ⟨n, hn : ∀ m, n ≤ m → LinearMap.range (f ^ n) = LinearMap.range (f ^ m)⟩ :=
    IsArtinian.monotone_stabilizes f.iterateRange
  refine eventually_atTop.mpr ⟨n, fun l hl ↦ le_antisymm (iInf_le _ _) (le_iInf fun m ↦ ?_)⟩
  rcases le_or_gt l m with h | h
  · rw [← hn _ (hl.trans h), hn _ hl]
  · exact f.iterateRange.monotone h.le

end LinearMap

end Semiring

section Ring

variable {R M P N : Type*}

variable [Ring R] [AddCommGroup M] [AddCommGroup P] [AddCommGroup N]

variable [Module R M] [Module R P] [Module R N]

-- INSTANCE (free from Core): isArtinian_of_quotient_of_artinian

theorem isArtinian_of_range_eq_ker [IsArtinian R M] [IsArtinian R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (h : LinearMap.range f = LinearMap.ker g) : IsArtinian R N :=
  wellFounded_lt_exact_sequence (LinearMap.range f)
    (Submodule.map ((LinearMap.ker f).liftQ f le_rfl))
    (Submodule.comap ((LinearMap.ker f).liftQ f le_rfl))
    (Submodule.comap g.rangeRestrict) (Submodule.map g.rangeRestrict)
    (Submodule.gciMapComap <| LinearMap.ker_eq_bot.mp <| Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
    (Submodule.giMapComap g.surjective_rangeRestrict)
    (by simp [Submodule.map_comap_eq, inf_comm, Submodule.range_liftQ])
    (by simp [Submodule.comap_map_eq, h])

theorem isArtinian_iff_submodule_quotient (S : Submodule R P) :
    IsArtinian R P ↔ IsArtinian R S ∧ IsArtinian R (P ⧸ S) := by
  refine ⟨fun h ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ ?_⟩
  apply isArtinian_of_range_eq_ker S.subtype S.mkQ
  rw [Submodule.ker_mkQ, Submodule.range_subtype]

-- INSTANCE (free from Core): isArtinian_prod

-- INSTANCE (free from Core): isArtinian_sup

variable {ι : Type*} [Finite ι]

-- INSTANCE (free from Core): isArtinian_pi

-- INSTANCE (free from Core): isArtinian_pi'

-- INSTANCE (free from Core): isArtinian_finsupp

-- INSTANCE (free from Core): isArtinian_iSup

variable (R M) in

theorem IsArtinian.isSemisimpleModule_iff_jacobson [IsArtinian R M] :
    IsSemisimpleModule R M ↔ Module.jacobson R M = ⊥ :=
  ⟨fun _ ↦ IsSemisimpleModule.jacobson_eq_bot R M, fun h ↦
    have ⟨s, hs⟩ := Finset.exists_inf_le (Subtype.val (p := fun m : Submodule R M ↦ IsCoatom m))
    have _ (m : s) : IsSimpleModule R (M ⧸ m.1.1) := isSimpleModule_iff_isCoatom.mpr m.1.2
    let f : M →ₗ[R] ∀ m : s, M ⧸ m.1.1 := LinearMap.pi fun m ↦ m.1.1.mkQ
    .of_injective f <| LinearMap.ker_eq_bot.mp <| le_bot_iff.mp fun x hx ↦ by
      rw [← h, Module.jacobson, Submodule.mem_sInf]
      exact fun m hm ↦ hs ⟨m, hm⟩ <| Submodule.mem_finsetInf.mpr fun i hi ↦
        (Submodule.Quotient.mk_eq_zero i.1).mp <| congr_fun hx ⟨i, hi⟩⟩

open Submodule Function

namespace LinearMap

variable [IsArtinian R M]

theorem eventually_codisjoint_ker_pow_range_pow (f : Module.End R M) :
    ∀ᶠ n in atTop, Codisjoint (LinearMap.ker (f ^ n)) (LinearMap.range (f ^ n)) := by
  obtain ⟨n, hn : ∀ m, n ≤ m → LinearMap.range (f ^ n) = LinearMap.range (f ^ m)⟩ :=
    IsArtinian.monotone_stabilizes f.iterateRange
  refine eventually_atTop.mpr ⟨n, fun m hm ↦ codisjoint_iff.mpr ?_⟩
  simp_rw [← hn _ hm, Submodule.eq_top_iff', Submodule.mem_sup]
  intro x
  rsuffices ⟨y, hy⟩ : ∃ y, (f ^ m) ((f ^ n) y) = (f ^ m) x
  · exact ⟨x - (f ^ n) y, by simp [hy], (f ^ n) y, by simp⟩
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `mem_range` into `mem_range (f := _)`
  simp_rw [f.pow_apply n, f.pow_apply m, ← iterate_add_apply, ← f.pow_apply (m + n),
    ← f.pow_apply m, ← mem_range (f := _), ← hn _ (n.le_add_left m), hn _ hm]
  exact LinearMap.mem_range_self (f ^ m) x

theorem eventually_isCompl_ker_pow_range_pow [IsNoetherian R M] (f : Module.End R M) :
    ∀ᶠ n in atTop, IsCompl (LinearMap.ker (f ^ n)) (LinearMap.range (f ^ n)) := by
  filter_upwards [f.eventually_disjoint_ker_pow_range_pow.and
    f.eventually_codisjoint_ker_pow_range_pow] with n hn
  simpa only [isCompl_iff]

theorem isCompl_iSup_ker_pow_iInf_range_pow [IsNoetherian R M] (f : M →ₗ[R] M) :
    IsCompl (⨆ n, LinearMap.ker (f ^ n)) (⨅ n, LinearMap.range (f ^ n)) := by
  obtain ⟨k, hk⟩ := eventually_atTop.mp <| f.eventually_isCompl_ker_pow_range_pow.and <|
    f.eventually_iInf_range_pow_eq.and f.eventually_iSup_ker_pow_eq
  obtain ⟨h₁, h₂, h₃⟩ := hk k (le_refl k)
  rwa [h₂, h₃]

end LinearMap

end Ring

section CommSemiring

variable {R : Type*} (M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M] [IsArtinian R M]

namespace IsArtinian

theorem range_smul_pow_stabilizes (r : R) :
    ∃ n : ℕ, ∀ m, n ≤ m →
      LinearMap.range (r ^ n • LinearMap.id : M →ₗ[R] M) =
      LinearMap.range (r ^ m • LinearMap.id : M →ₗ[R] M) :=
  monotone_stabilizes
    ⟨fun n => LinearMap.range (r ^ n • LinearMap.id : M →ₗ[R] M), fun n m h x ⟨y, hy⟩ =>
      ⟨r ^ (m - n) • y, by
        dsimp at hy ⊢
        rw [← smul_assoc, smul_eq_mul, ← pow_add, ← hy, add_tsub_cancel_of_le h]⟩⟩

variable {M}

theorem exists_pow_succ_smul_dvd (r : R) (x : M) :
    ∃ (n : ℕ) (y : M), r ^ n.succ • y = r ^ n • x := by
  obtain ⟨n, hn⟩ := IsArtinian.range_smul_pow_stabilizes M r
  simp_rw [SetLike.ext_iff] at hn
  exact ⟨n, by simpa using hn n.succ n.le_succ (r ^ n • x)⟩

end IsArtinian

end CommSemiring

theorem isArtinian_of_submodule_of_artinian (R M) [Semiring R] [AddCommMonoid M] [Module R M]
    (N : Submodule R M) (_ : IsArtinian R M) : IsArtinian R N := inferInstance

theorem isArtinian_of_tower (R) {S M} [Semiring R] [Semiring S] [AddCommMonoid M] [SMul R S]
    [Module S M] [Module R M] [IsScalarTower R S M] (h : IsArtinian R M) : IsArtinian S M :=
  ⟨(Submodule.restrictScalarsEmbedding R S M).wellFounded h.wf⟩

-- INSTANCE (free from Core): DivisionSemiring.instIsArtinianRing

-- INSTANCE (free from Core): DivisionRing.instIsArtinianRing

theorem Ring.isArtinian_of_zero_eq_one {R} [Semiring R] (h01 : (0 : R) = 1) : IsArtinianRing R :=
  have := subsingleton_of_zero_eq_one h01
  inferInstance

-- INSTANCE (free from Core): (R)

-- INSTANCE (free from Core): (priority

open Submodule Function

-- INSTANCE (free from Core): isArtinian_of_fg_of_artinian'

theorem isArtinian_of_fg_of_artinian {R M} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) [IsArtinianRing R] (hN : N.FG) : IsArtinian R N := by
  rw [← Module.Finite.iff_fg] at hN; infer_instance

theorem IsArtinianRing.of_finite (R S) [Ring R] [Ring S] [Module R S] [IsScalarTower R S S]
    [IsArtinianRing R] [Module.Finite R S] : IsArtinianRing S :=
  isArtinian_of_tower R isArtinian_of_fg_of_artinian'

-- INSTANCE (free from Core): (n

-- INSTANCE (free from Core): (n

theorem isArtinian_span_of_finite (R) {M} [Ring R] [AddCommGroup M] [Module R M] [IsArtinianRing R]
    {A : Set M} (hA : A.Finite) : IsArtinian R (Submodule.span R A) :=
  isArtinian_of_fg_of_artinian _ (Submodule.fg_def.mpr ⟨A, hA, rfl⟩)

theorem Function.Surjective.isArtinianRing {R} [Semiring R] {S} [Semiring S] {F}
    [FunLike F R S] [RingHomClass F R S]
    {f : F} (hf : Function.Surjective f) [H : IsArtinianRing R] : IsArtinianRing S := by
  rw [isArtinianRing_iff] at H ⊢
  exact ⟨(Ideal.orderEmbeddingOfSurjective f hf).wellFounded H.wf⟩

-- INSTANCE (free from Core): isArtinianRing_rangeS

-- INSTANCE (free from Core): isArtinianRing_range

theorem RingEquiv.isArtinianRing {R S} [Semiring R] [Semiring S] (f : R ≃+* S)
    [IsArtinianRing R] : IsArtinianRing S :=
  f.surjective.isArtinianRing

-- INSTANCE (free from Core): {R

-- INSTANCE (free from Core): {ι}

namespace IsArtinianRing

section Semiring

variable {R : Type*} [Semiring R]

theorem isUnit_iff_isRightRegular [IsArtinianRing R] {x : R} : IsUnit x ↔ IsRightRegular x := by
  rw [IsRightRegular, IsUnit.isUnit_iff_mulRight_bijective, Bijective, and_iff_left_of_imp]
  exact IsArtinian.surjective_of_injective_endomorphism (.toSpanSingleton R R x)

theorem isUnit_iff_isRegular [IsArtinianRing R] {x : R} : IsUnit x ↔ IsRegular x := by
  rw [isRegular_iff, ← isUnit_iff_isRightRegular, and_iff_right_of_imp (·.isRegular.1)]

theorem isUnit_iff_isLeftRegular [IsArtinianRing Rᵐᵒᵖ] {x : R} : IsUnit x ↔ IsLeftRegular x := by
  rw [← isRightRegular_op, ← isUnit_op, isUnit_iff_isRightRegular]

theorem isUnit_iff_isRegular_of_mulOpposite [IsArtinianRing Rᵐᵒᵖ] {x : R} :
    IsUnit x ↔ IsRegular x := by
  rw [isRegular_iff, ← isUnit_iff_isLeftRegular, and_iff_left_of_imp (·.isRegular.2)]

end Semiring

section Ring

variable {R : Type*} [Ring R]

open nonZeroDivisors

theorem isUnit_of_mem_nonZeroDivisors [IsArtinianRing R] {a : R} (ha : a ∈ R⁰) : IsUnit a := by
  rwa [isUnit_iff_isRegular, isRegular_iff_mem_nonZeroDivisors]

theorem isUnit_of_mem_nonZeroDivisors_of_mulOpposite [IsArtinianRing Rᵐᵒᵖ] {a : R}
    (ha : a ∈ R⁰) : IsUnit a := by
  rwa [isUnit_iff_isRegular_of_mulOpposite, isRegular_iff_mem_nonZeroDivisors]

theorem isUnit_iff_mem_nonZeroDivisors [IsArtinianRing R] {a : R} : IsUnit a ↔ a ∈ R⁰ := by
  rw [isUnit_iff_isRegular, isRegular_iff_mem_nonZeroDivisors]

theorem isUnit_iff_mem_nonZeroDivisors_of_mulOpposite [IsArtinianRing Rᵐᵒᵖ] {a : R} :
    IsUnit a ↔ a ∈ R⁰ := by
  rw [isUnit_iff_isRegular_of_mulOpposite, isRegular_iff_mem_nonZeroDivisors]

variable (R)

theorem isUnitSubmonoid_eq [IsArtinianRing R] : IsUnit.submonoid R = R⁰ := by
  ext; simp [IsUnit.mem_submonoid_iff, isUnit_iff_mem_nonZeroDivisors]

theorem isUnitSubmonoid_eq_of_mulOpposite [IsArtinianRing Rᵐᵒᵖ] :
    IsUnit.submonoid R = R⁰ := by
  ext; simp [IsUnit.mem_submonoid_iff, isUnit_iff_mem_nonZeroDivisors_of_mulOpposite]

theorem isUnitSubmonoid_eq_nonZeroDivisorsRight [IsArtinianRing R] :
    IsUnit.submonoid R = nonZeroDivisorsRight R := by
  ext; rw [← isRightRegular_iff_mem_nonZeroDivisorsRight]; exact isUnit_iff_isRightRegular

theorem nonZeroDivisorsLeft_eq_isUnitSubmonoid [IsArtinianRing Rᵐᵒᵖ] :
    IsUnit.submonoid R = nonZeroDivisorsLeft R := by
  ext; rw [← isLeftRegular_iff_mem_nonZeroDivisorsLeft]; exact isUnit_iff_isLeftRegular

end Ring

section CommSemiring

variable (R : Type*) [CommSemiring R] [IsArtinianRing R]
