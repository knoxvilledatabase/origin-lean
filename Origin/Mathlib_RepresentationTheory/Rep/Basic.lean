/-
Extracted from RepresentationTheory/Rep/Basic.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# `Rep k G` is the category of `k`-linear representations of `G`.

Given a `G`-representation `ρ` on a module `V`, you can construct the bundled representation as
`Rep.of ρ`. Conversely, given a bundled representation `A : Rep k G`, you can get the underlying
module as `A.V` and the representation on it as `A.ρ`.

-/

universe w w' u u' v v'

open CategoryTheory

set_option backward.privateInPublic true in

structure Rep (k : Type u) (G : Type v) [Semiring k] [Monoid G] where
  private mk ::
  /-- the underlying type of an object in `Rep k G` -/
  V : Type w
  [hV1 : AddCommGroup V]
  [hV2 : Module k V]
  /-- the underlying representation of an object in `Rep k G` -/
  ρ : Representation k G V

namespace Rep

noncomputable section

section semiring

variable {k : Type u} {G : Type v} [Semiring k] [Monoid G] {X Y : Type w} [AddCommGroup X]
  [AddCommGroup Y] [Module k X] [Module k Y] {ρ : Representation k G X} {σ : Representation k G Y}
  (A B C : Rep.{w} k G)

attribute [instance] hV1 hV2

initialize_simps_projections Rep (-hV1, -hV2)

-- INSTANCE (free from Core): :

attribute [coe] V

variable (ρ) in

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

abbrev of : Rep.{w} k G := ⟨X, ρ⟩

variable (X ρ) in

lemma of_V : (of ρ).V = X := by with_reducible rfl

variable (X ρ) in

lemma of_ρ : (of ρ).ρ = ρ := by with_reducible rfl

set_option backward.privateInPublic true in
