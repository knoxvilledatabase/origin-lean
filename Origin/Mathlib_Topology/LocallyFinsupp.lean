/-
Extracted from Topology/LocallyFinsupp.lean
Genuine: 11 of 13 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Type of functions with locally finite support

This file defines functions with locally finite support, provides supporting API. For suitable
targets, it establishes functions with locally finite support as an instance of a lattice ordered
commutative group.

Throughout the present file, `X` denotes a topologically space and `U` a subset of `X`.
-/

open Filter Function Set Topology

variable
  {X : Type*} [TopologicalSpace X] {U : Set X}
  {Y : Type*}

/-!
## Definition, coercion to functions and basic extensionality lemmas

A function with locally finite support within `U` is a function `X → Y` whose support is locally
finite within `U` and entirely contained in `U`.  For T1-spaces, the theorem
`supportDiscreteWithin_iff_locallyFiniteWithin` shows that the first condition is equivalent to the
condition that the support `f` is discrete within `U`.
-/

variable (U Y) in

structure Function.locallyFinsuppWithin [Zero Y] where
  /-- A function `X → Y` -/
  toFun : X → Y
  /-- A proof that the support of `toFun` is contained in `U` -/
  supportWithinDomain' : toFun.support ⊆ U
  /-- A proof that the support is locally finite within `U` -/
  supportLocallyFiniteWithinDomain' : ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ toFun.support)

variable (X Y) in

abbrev Function.locallyFinsupp [Zero Y] := locallyFinsuppWithin (Set.univ : Set X) Y

-- INSTANCE (free from Core): [Zero

theorem supportDiscreteWithin_iff_locallyFiniteWithin [T1Space X] [Zero Y] {f : X → Y}
    (h : f.support ⊆ U) :
    f =ᶠ[codiscreteWithin U] 0 ↔ ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ f.support) := by
  have : f.support = (U \ {x | f x = (0 : X → Y) x}) := by
    ext x
    simp only [mem_support, ne_eq, Pi.zero_apply, mem_diff, mem_setOf_eq, iff_and_self]
    exact (h ·)
  rw [EventuallyEq, Filter.Eventually, codiscreteWithin_iff_locallyFiniteComplementWithin, this]

def LocallyFiniteSupport [Zero Y] (f : X → Y) : Prop :=
  ∀ z : X, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ f.support)

lemma LocallyFiniteSupport.iff_locallyFinite_support [Zero Y] (f : X → Y) :
    LocallyFinite (fun s : f.support ↦ ({s.val} : Set X)) ↔ LocallyFiniteSupport f := by
  dsimp only [LocallyFinite]
  peel with z t ht
  have aux1 : t ∩ f.support = {i : f.support | ↑i ∈ t} := by aesop
  have aux2 : InjOn Subtype.val {i : f.support | ↑i ∈ t} := by aesop
  simp only [singleton_inter_nonempty, aux1, finite_image_iff aux2]

lemma LocallyFiniteSupport.locallyFinite_support [Zero Y] (f : X → Y) (h : LocallyFiniteSupport f) :
    LocallyFinite (fun s : f.support ↦ ({s.val} : Set X)) :=
  (LocallyFiniteSupport.iff_locallyFinite_support f).mpr h

lemma LocallyFiniteSupport.finite_inter_support_of_isCompact {W : Set X}
   [Zero Y] {f : X → Y} (h : LocallyFiniteSupport f)
   (hW : IsCompact W) : (W ∩ f.support).Finite := by
  have := LocallyFinite.finite_nonempty_inter_compact
    (LocallyFiniteSupport.locallyFinite_support f h) hW
  have lem {α : Type u_1} (s t : Set α) : {i : s | ({↑i} ∩ t).Nonempty} = (t ∩ s) := by aesop
  rw [← lem f.support W]
  exact Finite.image Subtype.val this

lemma Function.locallyFinsupp.locallyFiniteSupport [Zero Y] (f : locallyFinsupp X Y) :
    LocallyFiniteSupport f.toFun :=
  (f.supportLocallyFiniteWithinDomain' · (by trivial))

namespace Function.locallyFinsuppWithin

-- INSTANCE (free from Core): [Zero

abbrev support [Zero Y] (D : locallyFinsuppWithin U Y) := Function.support D

lemma supportWithinDomain [Zero Y] (D : locallyFinsuppWithin U Y) :
    D.support ⊆ U := D.supportWithinDomain'

lemma supportLocallyFiniteWithinDomain [Zero Y] (D : locallyFinsuppWithin U Y) :
    ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ D.support) := D.supportLocallyFiniteWithinDomain'
