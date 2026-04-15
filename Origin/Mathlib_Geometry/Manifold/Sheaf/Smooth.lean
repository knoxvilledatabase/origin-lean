/-
Extracted from Geometry/Manifold/Sheaf/Smooth.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-! # The sheaf of smooth functions on a manifold

The sheaf of `𝕜`-smooth functions from a manifold `M` to a manifold `N` can be defined as a sheaf of
types using the construction `StructureGroupoid.LocalInvariantProp.sheaf` from the file
`Mathlib/Geometry/Manifold/Sheaf/Basic.lean`.  In this file we write that down (a one-liner), then
do the work of upgrading this to a sheaf of [groups]/[abelian groups]/[rings]/[commutative rings]
when `N` carries more algebraic structure.  For example, if `N` is `𝕜` then the sheaf of smooth
functions from `M` to `𝕜` is a sheaf of commutative rings, the *structure sheaf* of `M`.

## Main definitions

* `smoothSheaf`: The sheaf of smooth functions from `M` to `N`, as a sheaf of types
* `smoothSheaf.eval`: Canonical map onto `N` from the stalk of `smoothSheaf IM I M N` at `x`,
  given by evaluating sections at `x`
* `smoothSheafGroup`, `smoothSheafCommGroup`, `smoothSheafRing`, `smoothSheafCommRing`: The
  sheaf of smooth functions into a [Lie group]/[abelian Lie group]/[smooth ring]/[smooth commutative
  ring], as a sheaf of [groups]/[abelian groups]/[rings]/[commutative rings]
* `smoothSheafCommRing.forgetStalk`: Identify the stalk at a point of the sheaf-of-commutative-rings
  of functions from `M` to `R` (for `R` a smooth ring) with the stalk at that point of the
  corresponding sheaf of types.
* `smoothSheafCommRing.eval`: upgrade `smoothSheaf.eval` to a ring homomorphism when considering the
  sheaf of smooth functions into a smooth commutative ring
* `smoothSheafCommGroup.compLeft`: For a manifold `M` and a smooth homomorphism `φ` between
  abelian Lie groups `A`, `A'`, the 'postcomposition-by-`φ`' morphism of sheaves from
  `smoothSheafCommGroup IM I M A` to `smoothSheafCommGroup IM I' M A'`

## Main results

* `smoothSheaf.eval_surjective`: `smoothSheaf.eval` is surjective.
* `smoothSheafCommRing.eval_surjective`: `smoothSheafCommRing.eval` is surjective.

## TODO

There are variants of `smoothSheafCommGroup.compLeft` for `GrpCat`, `RingCat`, `CommRingCat`;
this is just boilerplate and can be added as needed.

Similarly, there are variants of `smoothSheafCommRing.forgetStalk` and `smoothSheafCommRing.eval`
for `GrpCat`, `CommGrpCat` and `RingCat` which can be added as needed.

Currently there is a universe restriction: one can consider the sheaf of smooth functions from `M`
to `N` only if `M` and `N` are in the same universe.  For example, since `ℂ` is in `Type`, we can
only consider the structure sheaf of complex manifolds in `Type`, which is unsatisfactory. The
obstacle here is in the underlying category theory constructions, which are not sufficiently
universe polymorphic.  A direct attempt to generalize the universes worked in Lean 3 but was
reverted because it was hard to port to Lean 4, see
https://github.com/leanprover-community/mathlib/pull/19230
The current (Oct 2023) proposal to permit these generalizations is to use the new `UnivLE`
typeclass, and some (but not all) of the underlying category theory constructions have now been
generalized by this method: see https://github.com/leanprover-community/mathlib4/pull/5724,
https://github.com/leanprover-community/mathlib4/pull/5726.
-/

noncomputable section

open TopologicalSpace Opposite

open scoped ContDiff

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E H')
  (M : Type u) [TopologicalSpace M] [ChartedSpace HM M]
  (N G A A' R : Type u) [TopologicalSpace N] [ChartedSpace H N]
  [TopologicalSpace G] [ChartedSpace H G] [TopologicalSpace A] [ChartedSpace H A]
  [TopologicalSpace A'] [ChartedSpace H' A'] [TopologicalSpace R] [ChartedSpace H R]

variable {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] (IP : ModelWithCorners 𝕜 EP HP)
  (P : Type u) [TopologicalSpace P] [ChartedSpace HP P]

section TypeCat

def smoothSheaf : TopCat.Sheaf (Type u) (TopCat.of M) :=
  (contDiffWithinAt_localInvariantProp (I := IM) (I' := I) ∞).sheaf M N

variable {M}

-- INSTANCE (free from Core): smoothSheaf.coeFun

open Manifold in

def smoothSheaf.eval (x : M) : (smoothSheaf IM I M N).presheaf.stalk x → N :=
  TopCat.stalkToFiber (StructureGroupoid.LocalInvariantProp.localPredicate M N _) x

def smoothSheaf.evalHom (x : TopCat.of M) :
    (smoothSheaf IM I M N).presheaf.stalk x ⟶ N :=
  TopCat.stalkToFiber (StructureGroupoid.LocalInvariantProp.localPredicate M N _) x

open CategoryTheory Limits

def smoothSheaf.evalAt (x : TopCat.of M) (U : OpenNhds x)
    (i : (smoothSheaf IM I M N).presheaf.obj (Opposite.op U.val)) : N :=
  i.1 ⟨x, U.2⟩
