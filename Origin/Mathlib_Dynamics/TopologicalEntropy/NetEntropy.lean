/-
Extracted from Dynamics/TopologicalEntropy/NetEntropy.lean
Genuine: 11 of 11 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy

/-!
# Topological entropy via nets
We implement Bowen-Dinaburg's definitions of the topological entropy, via nets.

The major design decisions are the same as in `Mathlib.Dynamics.TopologicalEntropy.CoverEntropy`,
and are explained in detail there: use of uniform spaces, definition of the topological entropy of
a subset, and values taken in `EReal`.

Given a map `T : X → X` and a subset `F ⊆ X`, the topological entropy is loosely defined using
nets as the exponential growth (in `n`) of the number of distinguishable orbits of length `n`
starting from `F`. More precisely, given an entourage `U`, two orbits of length `n` can be
distinguished if there exists some index `k < n` such that `T^[k] x` and `T^[k] y` are far enough
(i.e. `(T^[k] x, T^[k] y)` is not in `U`). The maximal number of distinguishable orbits of
length `n` is `netMaxcard T F U n`, and its exponential growth `netEntropyEntourage T F U`. This
quantity increases when `U` decreases, and a definition of the topological entropy is
`⨆ U ∈ 𝓤 X, netEntropyInfEntourage T F U`.

The definition of topological entropy using nets coincides with the definition using covers.
Instead of defining a new notion of topological entropy, we prove that
`coverEntropy` coincides with `⨆ U ∈ 𝓤 X, netEntropyEntourage T F U`.

## Main definitions
- `IsDynNetIn`: property that dynamical balls centered on a subset `s` of `F` are disjoint.
- `netMaxcard`: maximal cardinality of a dynamical net. Takes values in `ℕ∞`.
- `netEntropyInfEntourage`/`netEntropyEntourage`: exponential growth of `netMaxcard`. The former is
defined with a `liminf`, the latter with a `limsup`. Take values in `EReal`.

## Implementation notes
As when using covers, there are two competing definitions `netEntropyInfEntourage` and
`netEntropyEntourage` in this file: one uses a `liminf`, the other a `limsup`. When using covers,
we chose the `limsup` definition as the default.

## Main results
- `coverEntropy_eq_iSup_netEntropyEntourage`: equality between the notions of topological entropy
defined with covers and with nets. Has a variant for `coverEntropyInf`.

## Tags
net, entropy

## TODO
Get versions of the topological entropy on (pseudo-e)metric spaces.
-/

namespace Dynamics

open Set Uniformity UniformSpace

variable {X : Type*}

/-! ### Dynamical nets -/

def IsDynNetIn (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) (s : Set X) : Prop :=
  s ⊆ F ∧ s.PairwiseDisjoint (fun x : X ↦ ball x (dynEntourage T U n))

lemma IsDynNetIn.of_le {T : X → X} {F : Set X} {U : Set (X × X)} {m n : ℕ} (m_n : m ≤ n) {s : Set X}
    (h : IsDynNetIn T F U m s) :
    IsDynNetIn T F U n s :=
  ⟨h.1, PairwiseDisjoint.mono h.2 (fun x ↦ ball_mono (dynEntourage_antitone T U m_n) x)⟩

lemma IsDynNetIn.of_entourage_subset {T : X → X} {F : Set X} {U V : Set (X × X)} (U_V : U ⊆ V)
    {n : ℕ} {s : Set X} (h : IsDynNetIn T F V n s) :
    IsDynNetIn T F U n s :=
  ⟨h.1, PairwiseDisjoint.mono h.2 (fun x ↦ ball_mono (dynEntourage_monotone T n U_V) x)⟩

lemma isDynNetIn_empty {T : X → X} {F : Set X} {U : Set (X × X)} {n : ℕ} :
    IsDynNetIn T F U n ∅ :=
  ⟨empty_subset F, pairwise_empty _⟩

lemma isDynNetIn_singleton (T : X → X) {F : Set X} (U : Set (X × X)) (n : ℕ) {x : X} (h : x ∈ F) :
    IsDynNetIn T F U n {x} :=
  ⟨singleton_subset_iff.2 h, pairwise_singleton x _⟩

lemma IsDynNetIn.card_le_card_of_isDynCoverOf {T : X → X} {F : Set X} {U : Set (X × X)}
    (U_symm : SymmetricRel U) {n : ℕ} {s t : Finset X} (hs : IsDynNetIn T F U n s)
    (ht : IsDynCoverOf T F U n t) :
    s.card ≤ t.card := by
  have (x : X) (x_s : x ∈ s) : ∃ z ∈ t, x ∈ ball z (dynEntourage T U n) := by
    specialize ht (hs.1 x_s)
    simp only [Finset.coe_sort_coe, mem_iUnion, Subtype.exists, exists_prop] at ht
    exact ht
  choose! F s_t using this
  simp only [mem_ball_symmetry (U_symm.dynEntourage T n)] at s_t
  apply Finset.card_le_card_of_injOn F (fun x x_s ↦ (s_t x x_s).1)
  exact fun x x_s y y_s Fx_Fy ↦
    PairwiseDisjoint.elim_set hs.2 x_s y_s (F x) (s_t x x_s).2 (Fx_Fy ▸ (s_t y y_s).2)

/-! ### Maximal cardinality of dynamical nets -/

noncomputable def netMaxcard (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) : ℕ∞ :=
  ⨆ (s : Finset X) (_ : IsDynNetIn T F U n s), (s.card : ℕ∞)

lemma IsDynNetIn.card_le_netMaxcard {T : X → X} {F : Set X} {U : Set (X × X)} {n : ℕ} {s : Finset X}
    (h : IsDynNetIn T F U n s) :
    s.card ≤ netMaxcard T F U n :=
  le_iSup₂ (α := ℕ∞) s h

lemma netMaxcard_monotone_time (T : X → X) (F : Set X) (U : Set (X × X)) :
    Monotone (fun n : ℕ ↦ netMaxcard T F U n) :=
  fun _ _ m_n ↦ biSup_mono (fun _ h ↦ h.of_le m_n)

lemma netMaxcard_antitone (T : X → X) (F : Set X) (n : ℕ) :
    Antitone (fun U : Set (X × X) ↦ netMaxcard T F U n) :=
  fun _ _ U_V ↦ biSup_mono (fun _ h ↦ h.of_entourage_subset U_V)

lemma netMaxcard_finite_iff (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    netMaxcard T F U n < ⊤ ↔
    ∃ s : Finset X, IsDynNetIn T F U n s ∧ (s.card : ℕ∞) = netMaxcard T F U n := by
  apply Iff.intro <;> intro h
  · rcases WithTop.ne_top_iff_exists.1 h.ne with ⟨k, k_max⟩
    rw [← k_max]
    simp only [ENat.some_eq_coe, Nat.cast_inj]
    -- The criterion we want to use is `Nat.sSup_mem`. We rewrite `netMaxcard` with an `sSup`,
    -- then check its `BddAbove` and `Nonempty` hypotheses.
    have : netMaxcard T F U n
      = sSup (WithTop.some '' (Finset.card '' {s : Finset X | IsDynNetIn T F U n s})) := by
      rw [netMaxcard, ← image_comp, sSup_image]
      simp only [mem_setOf_eq, ENat.some_eq_coe, Function.comp_apply]
    rw [this] at k_max
    have h_bdda : BddAbove (Finset.card '' {s : Finset X | IsDynNetIn T F U n s}) := by
      refine ⟨k, mem_upperBounds.2 ?_⟩
      simp only [mem_image, mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro s h
      rw [← WithTop.coe_le_coe, k_max]
      apply le_sSup
      simp only [ENat.some_eq_coe, mem_image, mem_setOf_eq, Nat.cast_inj, exists_eq_right]
      exact Filter.frequently_principal.mp fun a ↦ a h rfl
    have h_nemp : (Finset.card '' {s : Finset X | IsDynNetIn T F U n s}).Nonempty := by
      refine ⟨0, ?_⟩
      simp only [mem_image, mem_setOf_eq, Finset.card_eq_zero, exists_eq_right, Finset.coe_empty]
      exact isDynNetIn_empty
    rw [← WithTop.coe_sSup' h_bdda, ENat.some_eq_coe, Nat.cast_inj] at k_max
    have key := Nat.sSup_mem h_nemp h_bdda
    rw [← k_max, mem_image] at key
    simp only [mem_setOf_eq] at key
    exact key
  · rcases h with ⟨s, _, s_netMaxcard⟩
    rw [← s_netMaxcard]
    exact WithTop.coe_lt_top s.card
