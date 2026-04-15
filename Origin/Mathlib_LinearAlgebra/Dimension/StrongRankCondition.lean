/-
Extracted from LinearAlgebra/Dimension/StrongRankCondition.lean
Genuine: 37 of 37 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lemmas about rank and `finrank` in rings satisfying strong rank condition.

## Main statements

For modules over rings satisfying the rank condition

* `Basis.le_span`:
  the cardinality of a basis is bounded by the cardinality of any spanning set

For modules over rings satisfying the strong rank condition

* `linearIndependent_le_span`:
  For any linearly independent family `v : ι → M`
  and any finite spanning set `w : Set M`,
  the cardinality of `ι` is bounded by the cardinality of `w`.
* `linearIndependent_le_basis`:
  If `b` is a basis for a module `M`,
  and `s` is a linearly independent set,
  then the cardinality of `s` is bounded by the cardinality of `b`.

For modules over rings with invariant basis number
(including all commutative rings and all Noetherian rings)

* `mk_eq_mk_of_basis`: the dimension theorem, any two bases of the same vector space have the same
  cardinality.

## Additional definition

* `Algebra.IsQuadraticExtension`: An extension of rings `R ⊆ S` is quadratic if `S` is a
  free `R`-algebra of rank `2`.

-/

noncomputable section

universe u v w w'

variable {R : Type u} {S : Type*} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

variable {ι : Type w} {ι' : Type w'}

open Cardinal Basis Submodule Function Set Module

attribute [local instance] nontrivial_of_invariantBasisNumber

section InvariantBasisNumber

variable [InvariantBasisNumber R]

theorem mk_eq_mk_of_basis (v : Basis ι R M) (v' : Basis ι' R M) :
    Cardinal.lift.{w'} #ι = Cardinal.lift.{w} #ι' := by
  classical
  haveI := nontrivial_of_invariantBasisNumber R
  cases fintypeOrInfinite ι
  · -- `v` is a finite basis, so by `basis_finite_of_finite_spans` so is `v'`.
    -- haveI : Finite (range v) := Set.finite_range v
    haveI := basis_finite_of_finite_spans (Set.finite_range v) v.span_eq v'
    cases nonempty_fintype ι'
    -- We clean up a little:
    rw [Cardinal.mk_fintype, Cardinal.mk_fintype]
    simp only [Cardinal.lift_natCast, Nat.cast_inj]
    -- Now we can use invariant basis number to show they have the same cardinality.
    apply card_eq_of_linearEquiv R
    exact
      (Finsupp.linearEquivFunOnFinite R R ι).symm.trans v.repr.symm ≪≫ₗ v'.repr ≪≫ₗ
        Finsupp.linearEquivFunOnFinite R R ι'
  · -- `v` is an infinite basis,
    -- so by `infinite_basis_le_maximal_linearIndependent`, `v'` is at least as big,
    -- and then applying `infinite_basis_le_maximal_linearIndependent` again
    -- we see they have the same cardinality.
    have w₁ := infinite_basis_le_maximal_linearIndependent' v _ v'.linearIndependent v'.maximal
    rcases Cardinal.lift_mk_le'.mp w₁ with ⟨f⟩
    haveI : Infinite ι' := Infinite.of_injective f f.2
    have w₂ := infinite_basis_le_maximal_linearIndependent' v' _ v.linearIndependent v.maximal
    exact le_antisymm w₁ w₂

def Module.Basis.indexEquiv (v : Basis ι R M) (v' : Basis ι' R M) : ι ≃ ι' :=
  (Cardinal.lift_mk_eq'.1 <| mk_eq_mk_of_basis v v').some

theorem mk_eq_mk_of_basis' {ι' : Type w} (v : Basis ι R M) (v' : Basis ι' R M) : #ι = #ι' :=
  Cardinal.lift_inj.1 <| mk_eq_mk_of_basis v v'

end InvariantBasisNumber

section RankCondition

variable [RankCondition R]

theorem Basis.le_span'' {ι : Type*} [Fintype ι] (b : Basis ι R M) {w : Set M} [Fintype w]
    (s : span R w = ⊤) : Fintype.card ι ≤ Fintype.card w := by
  -- We construct a surjective linear map `(w → R) →ₗ[R] (ι → R)`,
  -- by expressing a linear combination in `w` as a linear combination in `ι`.
  fapply card_le_of_surjective' R
  · exact b.repr.toLinearMap.comp (Finsupp.linearCombination R (↑))
  · apply Surjective.comp (g := b.repr.toLinearMap)
    · apply LinearEquiv.surjective
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    simpa using s

theorem basis_le_span' {ι : Type*} (b : Basis ι R M) {w : Set M} [Fintype w] (s : span R w = ⊤) :
    #ι ≤ Fintype.card w := by
  haveI := nontrivial_of_invariantBasisNumber R
  haveI := basis_finite_of_finite_spans w.toFinite s b
  cases nonempty_fintype ι
  rw [Cardinal.mk_fintype ι]
  simp only [Nat.cast_le]
  exact Basis.le_span'' b s

theorem Module.Basis.le_span {J : Set M} (v : Basis ι R M) (hJ : span R J = ⊤) :
    #(range v) ≤ #J := by
  haveI := nontrivial_of_invariantBasisNumber R
  cases fintypeOrInfinite J
  · rw [← Cardinal.lift_le, Cardinal.mk_range_eq_of_injective v.injective, Cardinal.mk_fintype J]
    convert Cardinal.lift_le.{v}.2 (basis_le_span' v hJ)
    simp
  · let S : J → Set ι := fun j => ↑(v.repr j).support
    let S' : J → Set M := fun j => v '' S j
    have hs : range v ⊆ ⋃ j, S' j := by
      intro b hb
      rcases mem_range.1 hb with ⟨i, hi⟩
      have : span R J ≤ comap v.repr.toLinearMap (Finsupp.supported R R (⋃ j, S j)) :=
        span_le.2 fun j hj x hx => ⟨_, ⟨⟨j, hj⟩, rfl⟩, hx⟩
      rw [hJ] at this
      replace : v.repr (v i) ∈ Finsupp.supported R R (⋃ j, S j) := this trivial
      rw [v.repr_self, Finsupp.mem_supported, Finsupp.support_single_ne_zero _ one_ne_zero] at this
      · subst b
        rcases mem_iUnion.1 (this (Finset.mem_singleton_self _)) with ⟨j, hj⟩
        exact mem_iUnion.2 ⟨j, (mem_image _ _ _).2 ⟨i, hj, rfl⟩⟩
    refine le_of_not_gt fun IJ => ?_
    suffices #(⋃ j, S' j) < #(range v) by exact not_le_of_gt this ⟨Set.embeddingOfSubset _ _ hs⟩
    refine lt_of_le_of_lt (le_trans Cardinal.mk_iUnion_le_sum_mk
      (Cardinal.sum_le_sum _ (fun _ => ℵ₀) ?_)) ?_
    · exact fun j => (Cardinal.lt_aleph0_of_finite _).le
    · simpa

end RankCondition

section StrongRankCondition

variable [StrongRankCondition R]

open Submodule Finsupp

theorem linearIndependent_le_span_aux' {ι : Type*} [Fintype ι] (v : ι → M)
    (i : LinearIndependent R v) (w : Set M) [Fintype w] (s : range v ≤ span R w) :
    Fintype.card ι ≤ Fintype.card w := by
  -- We construct an injective linear map `(ι → R) →ₗ[R] (w → R)`,
  -- by thinking of `f : ι → R` as a linear combination of the finite family `v`,
  -- and expressing that (using the axiom of choice) as a linear combination over `w`.
  -- We can do this linearly by constructing the map on a basis.
  fapply card_le_of_injective' R
  · apply Finsupp.linearCombination
    exact fun i => Span.repr R w ⟨v i, s (mem_range_self i)⟩
  · intro f g h
    apply_fun linearCombination R ((↑) : w → M) at h
    simp only [linearCombination_linearCombination,
               Span.finsupp_linearCombination_repr] at h
    exact i h

lemma LinearIndependent.finite_of_le_span_finite {ι : Type*} (v : ι → M) (i : LinearIndependent R v)
    (w : Set M) [Finite w] (s : range v ≤ span R w) : Finite ι :=
  letI := Fintype.ofFinite w
  Fintype.finite <| fintypeOfFinsetCardLe (Fintype.card w) fun t => by
    let v' := fun x : (t : Set ι) => v x
    have i' : LinearIndependent R v' := i.comp _ Subtype.val_injective
    have s' : range v' ≤ span R w := (range_comp_subset_range _ _).trans s
    simpa using linearIndependent_le_span_aux' v' i' w s'

theorem linearIndependent_le_span' {ι : Type*} (v : ι → M) (i : LinearIndependent R v) (w : Set M)
    [Fintype w] (s : range v ≤ span R w) : #ι ≤ Fintype.card w := by
  haveI : Finite ι := i.finite_of_le_span_finite v w s
  letI := Fintype.ofFinite ι
  rw [Cardinal.mk_fintype]
  simp only [Nat.cast_le]
  exact linearIndependent_le_span_aux' v i w s

theorem linearIndependent_le_span {ι : Type*} (v : ι → M) (i : LinearIndependent R v) (w : Set M)
    [Fintype w] (s : span R w = ⊤) : #ι ≤ Fintype.card w := by
  apply linearIndependent_le_span' v i w
  rw [s]
  exact le_top

theorem linearIndependent_le_span_finset {ι : Type*} (v : ι → M) (i : LinearIndependent R v)
    (w : Finset M) (s : span R (w : Set M) = ⊤) : #ι ≤ w.card := by
  simpa only [Finset.coe_sort_coe, Fintype.card_coe] using linearIndependent_le_span v i w s

theorem linearIndependent_le_infinite_basis {ι : Type w} (b : Basis ι R M) [Infinite ι] {κ : Type w}
    (v : κ → M) (i : LinearIndependent R v) : #κ ≤ #ι := by
  classical
  by_contra h
  rw [not_le, ← Cardinal.mk_finset_of_infinite ι] at h
  let Φ := fun k : κ => (b.repr (v k)).support
  obtain ⟨s, w : Infinite ↑(Φ ⁻¹' {s})⟩ := Cardinal.exists_infinite_fiber' Φ h
  let v' := fun k : Φ ⁻¹' {s} => v k
  have i' : LinearIndependent R v' := i.comp _ Subtype.val_injective
  have w' : Finite (Φ ⁻¹' {s}) := by
    apply i'.finite_of_le_span_finite v' (s.image b)
    rintro m ⟨⟨p, ⟨rfl⟩⟩, rfl⟩
    simp only [SetLike.mem_coe, Finset.coe_image]
    apply Basis.mem_span_repr_support
  exact w.false

theorem linearIndependent_le_basis {ι : Type w} (b : Basis ι R M) {κ : Type w} (v : κ → M)
    (i : LinearIndependent R v) : #κ ≤ #ι := by
  classical
  -- We split into cases depending on whether `ι` is infinite.
  cases fintypeOrInfinite ι
  · rw [Cardinal.mk_fintype ι] -- When `ι` is finite, we have `linearIndependent_le_span`,
    haveI : Nontrivial R := nontrivial_of_invariantBasisNumber R
    rw [Fintype.card_congr (Equiv.ofInjective b b.injective)]
    exact linearIndependent_le_span v i (range b) b.span_eq
  · -- and otherwise we have `linearIndependent_le_infinite_basis`.
    exact linearIndependent_le_infinite_basis b v i

theorem card_le_of_injective'' {α : Type v} {β : Type v} (f : (α →₀ R) →ₗ[R] β →₀ R)
    (i : Injective f) : #α ≤ #β := by
  let b : Basis β R (β →₀ R) := ⟨1⟩
  apply linearIndependent_le_basis b (fun (i : α) ↦ f (Finsupp.single i 1))
  rw [LinearIndependent]
  have : (linearCombination R fun i ↦ f (Finsupp.single i 1)) = f := by ext a b; simp
  exact this.symm ▸ i

theorem linearIndependent_le_span'' {ι : Type v} {v : ι → M} (i : LinearIndependent R v) (w : Set M)
    (s : span R w = ⊤) : #ι ≤ #w := by
  fapply card_le_of_injective'' (R := R)
  · apply Finsupp.linearCombination
    exact fun i ↦ Span.repr R w ⟨v i, s ▸ trivial⟩
  · intro f g h
    apply_fun linearCombination R ((↑) : w → M) at h
    simp only [linearCombination_linearCombination,
               Span.finsupp_linearCombination_repr] at h
    exact i h

theorem Basis.card_le_card_of_linearIndependent_aux {R : Type*} [Semiring R] [StrongRankCondition R]
    (n : ℕ) {m : ℕ} (v : Fin m → Fin n → R) : LinearIndependent R v → m ≤ n := fun h => by
  simpa using linearIndependent_le_basis (Pi.basisFun R (Fin n)) v h

theorem maximal_linearIndependent_eq_infinite_basis {ι : Type w} (b : Basis ι R M) [Infinite ι]
    {κ : Type w} (v : κ → M) (i : LinearIndependent R v) (m : i.Maximal) : #κ = #ι := by
  apply le_antisymm
  · exact linearIndependent_le_basis b v i
  · haveI : Nontrivial R := nontrivial_of_invariantBasisNumber R
    exact infinite_basis_le_maximal_linearIndependent b v i m

theorem Module.Basis.mk_eq_rank'' {ι : Type v} (v : Basis ι R M) : #ι = Module.rank R M := by
  haveI := nontrivial_of_invariantBasisNumber R
  rw [Module.rank_def]
  apply le_antisymm
  · trans
    swap
    · apply le_ciSup (Cardinal.bddAbove_range _)
      exact
        ⟨Set.range v, by
          rw [LinearIndepOn]
          convert v.reindexRange.linearIndependent
          simp⟩
    · exact (Cardinal.mk_range_eq v v.injective).ge
  · apply ciSup_le'
    rintro ⟨s, li⟩
    apply linearIndependent_le_basis v _ li

theorem Module.Basis.mk_range_eq_rank (v : Basis ι R M) : #(range v) = Module.rank R M :=
  v.reindexRange.mk_eq_rank''

theorem rank_eq_card_basis {ι : Type w} [Fintype ι] (h : Basis ι R M) :
    Module.rank R M = Fintype.card ι := by
  classical
  haveI := nontrivial_of_invariantBasisNumber R
  rw [← h.mk_range_eq_rank, Cardinal.mk_fintype, Set.card_range_of_injective h.injective]

namespace Module.Basis

theorem card_le_card_of_linearIndependent {ι : Type*} [Fintype ι] (b : Basis ι R M)
    {ι' : Type*} [Fintype ι'] {v : ι' → M} (hv : LinearIndependent R v) :
    Fintype.card ι' ≤ Fintype.card ι := by
  simpa [rank_eq_card_basis b, Cardinal.mk_fintype] using hv.cardinal_lift_le_rank

theorem card_le_card_of_submodule (N : Submodule R M) [Fintype ι] (b : Basis ι R M)
    [Fintype ι'] (b' : Basis ι' R N) : Fintype.card ι' ≤ Fintype.card ι :=
  b.card_le_card_of_linearIndependent
    (b'.linearIndependent.map_injOn N.subtype N.injective_subtype.injOn)

theorem card_le_card_of_le {N O : Submodule R M} (hNO : N ≤ O) [Fintype ι]
    (b : Basis ι R O) [Fintype ι'] (b' : Basis ι' R N) : Fintype.card ι' ≤ Fintype.card ι :=
  b.card_le_card_of_linearIndependent
    (b'.linearIndependent.map_injOn (inclusion hNO) (N.inclusion_injective _).injOn)

theorem mk_eq_rank (v : Basis ι R M) :
    Cardinal.lift.{v} #ι = Cardinal.lift.{w} (Module.rank R M) := by
  haveI := nontrivial_of_invariantBasisNumber R
  rw [← v.mk_range_eq_rank, Cardinal.mk_range_eq_of_injective v.injective]

theorem mk_eq_rank'.{m} (v : Basis ι R M) :
    Cardinal.lift.{max v m} #ι = Cardinal.lift.{max w m} (Module.rank R M) :=
  Cardinal.lift_umax_eq.{w, v, m}.mpr v.mk_eq_rank

end Module.Basis

theorem rank_span {v : ι → M} (hv : LinearIndependent R v) :
    Module.rank R ↑(span R (range v)) = #(range v) := by
  haveI := nontrivial_of_invariantBasisNumber R
  rw [← Cardinal.lift_inj, ← (Basis.span hv).mk_eq_rank,
    Cardinal.mk_range_eq_of_injective (@LinearIndependent.injective ι R M v _ _ _ _ hv)]

theorem rank_span_set {s : Set M} (hs : LinearIndepOn R id s) : Module.rank R ↑(span R s) = #s := by
  rw [← @setOf_mem_eq _ s, ← Subtype.range_coe_subtype]
  exact rank_span hs

theorem toENat_rank_span_set {v : ι → M} {s : Set ι} (hs : LinearIndepOn R v s) :
    (Module.rank R <| span R <| v '' s).toENat = s.encard := by
  rw [image_eq_range, ← hs.injOn.encard_image, ← toENat_cardinalMk, image_eq_range,
    ← rank_span hs.linearIndependent]

def Submodule.inductionOnRank {R M} [Ring R] [StrongRankCondition R] [AddCommGroup M] [Module R M]
    [IsDomain R] [Finite ι] (b : Basis ι R M) (P : Submodule R M → Sort*)
    (ih : ∀ N : Submodule R M,
      (∀ N' ≤ N, ∀ x ∈ N, (∀ (c : R), ∀ y ∈ N', c • x + y = (0 : M) → c = 0) → P N') → P N)
    (N : Submodule R M) : P N :=
  letI := Fintype.ofFinite ι
  Submodule.inductionOnRankAux b P ih (Fintype.card ι) N fun hs hli => by
    simpa using b.card_le_card_of_linearIndependent hli

theorem Ideal.rank_eq {R S : Type*} [CommRing R] [StrongRankCondition R] [Ring S] [IsDomain S]
    [Algebra R S] {n m : Type*} [Fintype n] [Fintype m] (b : Basis n R S) {I : Ideal S}
    (hI : I ≠ ⊥) (c : Basis m R I) : Fintype.card m = Fintype.card n := by
  obtain ⟨a, ha⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hI)
  have : LinearIndependent R fun i => b i • a := by
    have hb := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hb ⊢
    intro g hg
    apply hb g
    simp only [← smul_assoc, ← Finset.sum_smul, smul_eq_zero] at hg
    exact hg.resolve_right ha
  exact le_antisymm
    (b.card_le_card_of_linearIndependent (c.linearIndependent.map' (Submodule.subtype I)
      ((LinearMap.ker_eq_bot (f := (Submodule.subtype I : I →ₗ[R] S))).mpr Subtype.coe_injective)))
    (c.card_le_card_of_linearIndependent this)

namespace Module

omit [StrongRankCondition R] in

theorem rank_pos_of_free [Module.Free R M] [Nontrivial M] :
    0 < Module.rank R M :=
  have := Module.nontrivial R M
  (pos_of_ne_zero <| Cardinal.mk_ne_zero _).trans_le
    (Free.chooseBasis R M).linearIndependent.cardinal_le_rank

theorem rank_pos_iff_of_free [Module.Free R M] :
    0 < Module.rank R M ↔ Nontrivial M := by
  refine ⟨fun h ↦ ?_, fun _ ↦ rank_pos_of_free⟩
  rw [← not_subsingleton_iff_nontrivial]
  intro h'
  simp only [rank_subsingleton', lt_self_iff_false] at h

theorem rank_zero_iff_of_free [Module.Free R M] :
    Module.rank R M = 0 ↔ Subsingleton M := by
  rw [← not_nontrivial_iff_subsingleton, iff_not_comm,
    ← Module.rank_pos_iff_of_free (R := R), pos_iff_ne_zero]

theorem finrank_eq_nat_card_basis (h : Basis ι R M) :
    finrank R M = Nat.card ι := by
  rw [Nat.card, ← toNat_lift.{v}, h.mk_eq_rank, toNat_lift, finrank]

theorem finrank_eq_card_basis {ι : Type w} [Fintype ι] (h : Basis ι R M) :
    finrank R M = Fintype.card ι :=
  finrank_eq_of_rank_eq (rank_eq_card_basis h)

theorem mk_finrank_eq_card_basis [Module.Finite R M] {ι : Type w} (h : Basis ι R M) :
    (finrank R M : Cardinal.{w}) = #ι := by
  cases @nonempty_fintype _ (Module.Finite.finite_basis h)
  rw [Cardinal.mk_fintype, finrank_eq_card_basis h]

theorem finrank_eq_card_finset_basis {ι : Type w} {b : Finset ι} (h : Basis b R M) :
    finrank R M = Finset.card b := by rw [finrank_eq_card_basis h, Fintype.card_coe]

variable (R)
