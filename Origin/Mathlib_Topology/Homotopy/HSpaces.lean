/-
Extracted from Topology/Homotopy/HSpaces.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# H-spaces

This file defines H-spaces mainly following the approach proposed by Serre in his paper
*Homologie singulière des espaces fibrés*. The idea beneath `H-spaces` is that they are topological
spaces with a binary operation `⋀ : X → X → X` that is a homotopy-theoretic weakening of an
operation that would make `X` into a topological monoid.
In particular, there exists a "neutral element" `e : X` such that `fun x ↦ e ⋀ x` and
`fun x ↦ x ⋀ e` are homotopic to the identity on `X`, see
[the Wikipedia page of H-spaces](https://en.wikipedia.org/wiki/H-space).

Some notable properties of `H-spaces` are
* Their fundamental group is always abelian (by the same argument for topological groups);
* Their cohomology ring comes equipped with a structure of a Hopf-algebra;
* The loop space based at every `x : X` carries a structure of an `H-space`.

## Main Results

* Every topological group `G` is an `H-space` using its operation `* : G → G → G` (this is already
  true if `G` has an instance of a `MulOneClass` and `ContinuousMul`);
* Given two `H-spaces` `X` and `Y`, their product is again an `H`-space. We show in an example that
  starting with two topological groups `G, G'`, the `H`-space structure on `G × G'` is
  definitionally equal to the product of `H-space` structures on `G` and `G'`.
* The loop space based at every `x : X` carries a structure of an `H-space`.

## To Do
* Prove that for every `NormedAddTorsor Z` and every `z : Z`, the operation
  `fun x y ↦ midpoint x y` defines an `H-space` structure with `z` as a "neutral element".
* Prove that `S^0`, `S^1`, `S^3` and `S^7` are the unique spheres that are `H-spaces`, where the
  first three inherit the structure because they are topological groups (they are Lie groups,
  actually), isomorphic to the invertible elements in `ℤ`, in `ℂ` and in the quaternions; and the
  fourth from the fact that `S^7` coincides with the octonions of norm 1 (it is not a group, in
  particular, only has an instance of `MulOneClass`).

## References

* [J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*,
  Ann. of Math (2) 1951, 54, 425–505][serre1951]
-/

universe u v

noncomputable section

open scoped unitInterval

open Path ContinuousMap Set.Icc TopologicalSpace

class HSpace (X : Type u) [TopologicalSpace X] where
  hmul : C(X × X, X)
  e : X
  hmul_e_e : hmul (e, e) = e
  eHmul :
    (hmul.comp <| (const X e).prodMk <| ContinuousMap.id X).HomotopyRel (ContinuousMap.id X) {e}
  hmulE :
    (hmul.comp <| (ContinuousMap.id X).prodMk <| const X e).HomotopyRel (ContinuousMap.id X) {e}

scoped[HSpaces] notation x "⋀" y => HSpace.hmul (x, y)

open HSpaces

-- INSTANCE (free from Core): HSpace.prod

namespace IsTopologicalGroup
