/-
Extracted from Combinatorics/Digraph/Basic.lean
Genuine: 11 | Conflates: 0 | Dissolved: 0 | Infrastructure: 30
-/
import Origin.Core
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Data.Fintype.Pi

noncomputable section

/-!
# Digraphs

This module defines directed graphs on a vertex type `V`,
which is the same notion as a relation `V → V → Prop`.
While this might be too simple of a notion to deserve the grandeur of a new definition,
the intention here is to develop relations using the language of graph theory.

Note that in this treatment, a digraph may have self loops.

The type `Digraph V` is structurally equivalent to `Quiver.{0} V`,
but a difference between these is that `Quiver` is a class —
its purpose is to attach a quiver structure to a particular type `V`.
In contrast, for `Digraph V` we are interested in working with the entire lattice
of digraphs on `V`.

## Main definitions

* `Digraph` is a structure for relations. Unlike `SimpleGraph`, the relation does not need to be
  symmetric or irreflexive.

* `CompleteAtomicBooleanAlgebra` instance: Under the subgraph relation, `Digraph` forms a
  `CompleteAtomicBooleanAlgebra`. In other words, this is the complete lattice of spanning subgraphs
  of the complete graph.
-/

open Finset Function

@[ext]
structure Digraph (V : Type*) where
  /-- The adjacency relation of a digraph. -/
  Adj : V → V → Prop

@[simps]
def Digraph.mk' {V : Type*} : (V → V → Bool) ↪ Digraph V where
  toFun x := ⟨fun v w ↦ x v w⟩
  inj' adj adj' := by
    simp_rw [mk.injEq]
    intro h
    funext v w
    simpa only [eq_iff_iff, Bool.coe_iff_coe] using congr($h v w)

instance {V : Type*} (adj : V → V → Bool) : DecidableRel (Digraph.mk' adj).Adj :=
  inferInstanceAs <| DecidableRel (fun v w ↦ adj v w)

instance {V : Type*} [DecidableEq V] [Fintype V] : Fintype (Digraph V) :=
  Fintype.ofBijective Digraph.mk' <| by
    classical
    refine ⟨Embedding.injective _, ?_⟩
    intro G
    use fun v w ↦ G.Adj v w
    ext v w
    simp

namespace Digraph

protected def completeDigraph (V : Type*) : Digraph V where Adj := ⊤

protected def emptyDigraph (V : Type*) : Digraph V where Adj _ _ := False

@[simps]
def completeBipartiteGraph (V W : Type*) : Digraph (Sum V W) where
  Adj v w := v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft

variable {ι : Sort*} {V : Type*} (G : Digraph V) {a b : V}

theorem adj_injective : Injective (Adj : Digraph V → V → V → Prop) := fun _ _ ↦ Digraph.ext

@[simp] theorem adj_inj {G H : Digraph V} : G.Adj = H.Adj ↔ G = H := Digraph.ext_iff.symm

section Order

protected def IsSubgraph (x y : Digraph V) : Prop :=
  ∀ ⦃v w : V⦄, x.Adj v w → y.Adj v w

instance : LE (Digraph V) := ⟨Digraph.IsSubgraph⟩

instance : Max (Digraph V) where
  max x y := { Adj := x.Adj ⊔ y.Adj }

instance : Min (Digraph V) where
  min x y := { Adj := x.Adj ⊓ y.Adj }

instance hasCompl : HasCompl (Digraph V) where
  compl G := { Adj := fun v w ↦ ¬G.Adj v w }

instance sdiff : SDiff (Digraph V) where
  sdiff x y := { Adj := x.Adj \ y.Adj }

instance supSet : SupSet (Digraph V) where
  sSup s := { Adj := fun a b ↦ ∃ G ∈ s, Adj G a b }

instance infSet : InfSet (Digraph V) where
  sInf s := { Adj := fun a b ↦ (∀ ⦃G⦄, G ∈ s → Adj G a b) }

@[simp]
theorem iSup_adj {f : ι → Digraph V} : (⨆ i, f i).Adj a b ↔ ∃ i, (f i).Adj a b := by simp [iSup]

@[simp]
theorem iInf_adj {f : ι → Digraph V} : (⨅ i, f i).Adj a b ↔ (∀ i, (f i).Adj a b) := by simp [iInf]

instance distribLattice : DistribLattice (Digraph V) :=
  { adj_injective.distribLattice Digraph.Adj (fun _ _ ↦ rfl) fun _ _ ↦ rfl with
    le := fun G H ↦ ∀ ⦃a b⦄, G.Adj a b → H.Adj a b }

instance completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra (Digraph V) :=
  { Digraph.distribLattice with
    le := (· ≤ ·)
    sup := (· ⊔ ·)
    inf := (· ⊓ ·)
    compl := HasCompl.compl
    sdiff := (· \ ·)
    top := Digraph.completeDigraph V
    bot := Digraph.emptyDigraph V
    le_top := fun _ _ _ _ ↦ trivial
    bot_le := fun _ _ _ h ↦ h.elim
    sdiff_eq := fun _ _ ↦ rfl
    inf_compl_le_bot := fun _ _ _ h ↦ absurd h.1 h.2
    top_le_sup_compl := fun G v w _ ↦ by tauto
    sSup := sSup
    le_sSup := fun _ G hG _ _ hab ↦ ⟨G, hG, hab⟩
    sSup_le := fun s G hG a b ↦ by
      rintro ⟨H, hH, hab⟩
      exact hG _ hH hab
    sInf := sInf
    sInf_le := fun _ _ hG _ _ hab ↦ hab hG
    le_sInf := fun _ _ hG _ _ hab ↦ fun _ hH ↦ hG _ hH hab
    iInf_iSup_eq := fun f ↦ by ext; simp [Classical.skolem] }

@[simp] theorem top_adj (v w : V) : (⊤ : Digraph V).Adj v w := trivial

@[simps] instance (V : Type*) : Inhabited (Digraph V) := ⟨⊥⟩

instance [IsEmpty V] : Unique (Digraph V) where
  default := ⊥
  uniq G := by ext1; congr!

instance [Nonempty V] : Nontrivial (Digraph V) := by
  use ⊥, ⊤
  have v := Classical.arbitrary V
  exact ne_of_apply_ne (·.Adj v v) (by simp)

section Decidable

variable (V) (H : Digraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]

instance Bot.adjDecidable : DecidableRel (⊥ : Digraph V).Adj :=
  inferInstanceAs <| DecidableRel fun _ _ ↦ False

instance Sup.adjDecidable : DecidableRel (G ⊔ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w ↦ G.Adj v w ∨ H.Adj v w

instance Inf.adjDecidable : DecidableRel (G ⊓ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w ↦ G.Adj v w ∧ H.Adj v w

instance SDiff.adjDecidable : DecidableRel (G \ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w ↦ G.Adj v w ∧ ¬H.Adj v w

instance Top.adjDecidable : DecidableRel (⊤ : Digraph V).Adj :=
  inferInstanceAs <| DecidableRel fun _ _ ↦ True

instance Compl.adjDecidable : DecidableRel (Gᶜ.Adj) :=
  inferInstanceAs <| DecidableRel fun v w ↦ ¬G.Adj v w

end Decidable

end Order

end Digraph
