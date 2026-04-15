/-
Extracted from Algebra/Group/Action/Equidecomp.lean
Genuine: 7 of 8 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Equidecompositions

This file develops the basic theory of equidecompositions.

## Main Definitions

Let `G` be a group acting on a space `X`, and `A B : Set X`.

An *equidecomposition* of `A` and `B` is typically defined as a finite partition of `A` together
with a finite list of elements of `G` of the same size such that applying each element to the
matching piece of the partition yields a partition of `B`.

This yields a bijection `f : A ≃ B` where, given `a : A`, `f a = γ • a` for `γ : G` the group
element for `a`'s piece of the partition. Reversing this is easy, and so we get an equivalent
(up to the choice of group elements) definition: an *Equidecomposition* of `A` and `B` is a
bijection `f : A ≃ B` such that for some `S : Finset G`, `f a ∈ S • a` for all `a`.

We take this as our definition as it is easier to work with. It is implemented as an element
`PartialEquiv X X` with source `A` and target `B`.

## Implementation Notes

* Equidecompositions are implemented as elements of `PartialEquiv X X` together with a
  `Finset` of elements of the acting group and a proof that every point in the source is moved
  by an element in the finset.

* The requirement that `G` be a group is relaxed where possible.

* We introduce a non-standard predicate, `IsDecompOn`, to state that a function satisfies the main
  combinatorial property of equidecompositions, even if it is not injective or surjective.

## TODO

* Prove that if two sets equidecompose into subsets of each other, they are equidecomposable
  (Schroeder-Bernstein type theorem)
* Define equidecomposability into subsets as a preorder on sets and
  prove that its induced equivalence relation is equidecomposability.
* Prove the definition of equidecomposition used here is equivalent to the more familiar one
  using partitions.

-/

variable {X G : Type*} {A B C : Set X}

open Function Set Pointwise PartialEquiv

namespace Equidecomp

section SMul

variable [SMul G X]

def IsDecompOn (f : X → X) (A : Set X) (S : Finset G) : Prop := ∀ a ∈ A, ∃ g ∈ S, f a = g • a

variable (X G)

structure _root_.Equidecomp extends PartialEquiv X X where
  isDecompOn' : ∃ S : Finset G, IsDecompOn toFun source S

variable {X G}

-- INSTANCE (free from Core): :

noncomputable

def witness (f : Equidecomp X G) : Finset G := f.isDecompOn'.choose

theorem isDecompOn (f : Equidecomp X G) : IsDecompOn f f.source f.witness :=
  f.isDecompOn'.choose_spec

theorem apply_mem_target {f : Equidecomp X G} {x : X} (h : x ∈ f.source) :
    f x ∈ f.target := by simp [h]

theorem toPartialEquiv_injective : Injective <| toPartialEquiv (X := X) (G := G) := by
  intro ⟨_, _, _⟩ _ _
  congr

theorem IsDecompOn.mono {f f' : X → X} {A A' : Set X} {S : Finset G} (h : IsDecompOn f A S)
    (hA' : A' ⊆ A) (hf' : EqOn f f' A') : IsDecompOn f' A' S := by
  intro a ha
  rw [← hf' ha]
  exact h a (hA' ha)
