/-
Extracted from Combinatorics/SimpleGraph/Sum.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Disjoint sum of graphs

This file defines the disjoint sum of graphs. The disjoint sum of `G : SimpleGraph α` and
`H : SimpleGraph β` is a graph on `α ⊕ β` where `u` and `v` are adjacent if and only if they are
both in `G` and adjacent in `G`, or they are both in `H` and adjacent in `H`.

## Main declarations

* `SimpleGraph.Sum`: The disjoint sum of graphs.

## Notation

* `G ⊕g H`: The disjoint sum of `G` and `H`.
-/

variable {α β γ : Type*}

namespace SimpleGraph

@[simps!]
protected def sum (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α ⊕ β) where
  Adj u v := match u, v with
    | Sum.inl u, Sum.inl v => G.Adj u v
    | Sum.inr u, Sum.inr v => H.Adj u v
    | _, _ => false
  symm u v := match u, v with
    | Sum.inl u, Sum.inl v => G.adj_symm
    | Sum.inr u, Sum.inr v => H.adj_symm
    | Sum.inl _, Sum.inr _ | Sum.inr _, Sum.inl _ => id
  loopless u := by cases u <;> simp

variable {G : SimpleGraph α} {H : SimpleGraph β}

@[simps!]
def Iso.sumComm : G ⊕g H ≃g H ⊕g G := ⟨Equiv.sumComm α β, by
  intro u v
  cases u <;> cases v <;> simp⟩

@[simps!]
def Iso.sumAssoc {I : SimpleGraph γ} : (G ⊕g H) ⊕g I ≃g G ⊕g (H ⊕g I) := ⟨Equiv.sumAssoc α β γ, by
  intro u v
  cases u <;> cases v <;> rename_i u v
  · cases u <;> cases v <;> simp
  · cases u <;> simp
  · cases v <;> simp
  · simp⟩

@[simps]
def Embedding.sumInl : G ↪g G ⊕g H where
  toFun u := _root_.Sum.inl u
  inj' u v := by simp
  map_rel_iff' := by simp

@[simps]
def Embedding.sumInr : H ↪g G ⊕g H where
  toFun u := _root_.Sum.inr u
  inj' u v := by simp
  map_rel_iff' := by simp

end SimpleGraph
