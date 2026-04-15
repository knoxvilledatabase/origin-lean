/-
Extracted from Order/KonigLemma.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Kőnig's infinity lemma

Kőnig's infinity lemma is most often stated as a graph theory result:
every infinite, locally finite connected graph contains an infinite path.
It has links to computability and proof theory, and it has a number of formulations.

In practice, most applications are not to an abstract graph,
but to a concrete collection of objects that are organized in a graph-like way,
often where the graph is a rooted tree representing a graded order.
In fact, the lemma is most easily stated and proved
in terms of covers in a strongly atomic order rather than a graph;
in this setting, the proof is almost trivial.

A common formulation of Kőnig's lemma is in terms of directed systems,
with the grading explicitly represented using an `ℕ`-indexed family of types,
which we also provide in this module.
This is a specialization of the much more general `nonempty_sections_of_finite_cofiltered_system`,
which goes through topology and category theory,
but here it is stated and proved independently with much fewer dependencies.

We leave the explicitly graph-theoretic version of the statement as TODO.

## Main Results

* `exists_seq_covby_of_forall_covby_finite` : Kőnig's lemma for strongly atomic orders.

* `exists_orderEmbedding_covby_of_forall_covby_finite` : Kőnig's lemma, where the sequence
  is given as an `OrderEmbedding` instead of a function.

* `exists_orderEmbedding_covby_of_forall_covby_finite_of_bot` : Kőnig's lemma where the sequence
  starts at the minimum of an infinite type.

* `exist_seq_forall_proj_of_forall_finite` : Kőnig's lemma for inverse systems,
  proved using the above applied to an order on a sigma-type `(i : ℕ) × α i`.

## TODO

Formulate the lemma as a statement about graphs.

-/

open Set

section Sequence

variable {α : Type*} [PartialOrder α] [IsStronglyAtomic α] {b : α}

theorem exists_seq_covby_of_forall_covby_finite (hfin : ∀ (a : α), {x | a ⋖ x}.Finite)
    (hb : (Ici b).Infinite) : ∃ f : ℕ → α, f 0 = b ∧ ∀ i, f i ⋖ f (i + 1) :=
  let h := fun a : {a : α // (Ici a).Infinite} ↦
    exists_covby_infinite_Ici_of_infinite_Ici a.2 (hfin a)
  let ks : ℕ → {a : α // (Ici a).Infinite} := Nat.rec ⟨b, hb⟩ fun _ a ↦ ⟨_, (h a).choose_spec.2⟩
  ⟨fun i ↦ (ks i).1, by simp [ks], fun i ↦ by simpa using (h (ks i)).choose_spec.1⟩

theorem exists_orderEmbedding_covby_of_forall_covby_finite (hfin : ∀ (a : α), {x | a ⋖ x}.Finite)
    (hb : (Ici b).Infinite) : ∃ f : ℕ ↪o α, f 0 = b ∧ ∀ i, f i ⋖ f (i + 1) := by
  obtain ⟨f, hf⟩ := exists_seq_covby_of_forall_covby_finite hfin hb
  exact ⟨OrderEmbedding.ofStrictMono f (strictMono_nat_of_lt_succ (fun i ↦ (hf.2 i).lt)), hf⟩

theorem exists_orderEmbedding_covby_of_forall_covby_finite_of_bot [OrderBot α] [Infinite α]
    (hfin : ∀ (a : α), {x | a ⋖ x}.Finite) : ∃ f : ℕ ↪o α, f 0 = ⊥ ∧ ∀ i, f i ⋖ f (i + 1) :=
  exists_orderEmbedding_covby_of_forall_covby_finite hfin (by simpa using infinite_univ)

theorem GradeMinOrder.exists_nat_orderEmbedding_of_forall_covby_finite
    [GradeMinOrder ℕ α] [OrderBot α] [Infinite α] (hfin : ∀ (a : α), {x | a ⋖ x}.Finite) :
    ∃ f : ℕ ↪o α, f 0 = ⊥ ∧ (∀ i, f i ⋖ f (i + 1)) ∧ ∀ i, grade ℕ (f i) = i := by
  obtain ⟨f, h0, hf⟩ := exists_orderEmbedding_covby_of_forall_covby_finite_of_bot hfin
  refine ⟨f, h0, hf, fun i ↦ ?_⟩
  induction i with
  | zero => simp [h0]
  | succ i ih => simpa [Order.covBy_iff_add_one_eq, ih, eq_comm] using CovBy.grade ℕ <| hf i

end Sequence

section Graded

end Graded
