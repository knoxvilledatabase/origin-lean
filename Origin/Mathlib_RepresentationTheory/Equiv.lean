/-
Extracted from RepresentationTheory/Equiv.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
## Main purpose

This file is a preliminary file for the `Iso`s in `Rep`, we build all the isomorphisms from
representation level to avoid abusing defeq.

TODO (Edison) : refactor `Rep` into a two-field structure (bundled `Representation`) and rebuild
all the `Iso`s in `Rep` using the equivs in this file.

-/

universe u u' v v' w w'

variable {k : Type u} [Semiring k] {G : Type v} [Monoid G] {V : Type v'} [AddCommMonoid V]
  [Module k V] {W : Type w'} [AddCommMonoid W] [Module k W] (H : Type w) [Subsingleton H]
  [MulOneClass H] [MulAction G H]

namespace Representation

noncomputable section

variable (k G) in

def ofMulActionSubsingletonEquivTrivial : (ofMulAction k G H).Equiv (trivial k G k) :=
  letI : Unique H := uniqueOfSubsingleton 1
  .mk (Finsupp.LinearEquiv.finsuppUnique _ _ _) fun g ↦ by
    ext a; simp [Subsingleton.elim (g • a) a]
