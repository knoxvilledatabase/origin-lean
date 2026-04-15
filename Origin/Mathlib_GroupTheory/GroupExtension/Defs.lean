/-
Extracted from GroupTheory/GroupExtension/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Group Extensions

This file defines extensions of multiplicative and additive groups and their associated structures
such as splittings and equivalences.

## Main definitions

- `(Add?)GroupExtension N E G`: structure for extensions of `G` by `N` as short exact sequences
  `1 → N → E → G → 1` (`0 → N → E → G → 0` for additive groups)
- `(Add?)GroupExtension.Equiv S S'`: structure for equivalences of two group extensions `S` and `S'`
  as specific homomorphisms `E → E'` such that each diagram below is commutative

```text
For multiplicative groups:
      ↗ E  ↘
1 → N   ↓    G → 1
      ↘ E' ↗

For additive groups:
      ↗ E  ↘
0 → N   ↓    G → 0
      ↘ E' ↗
```

- `(Add?)GroupExtension.Section S`: structure for right inverses to `rightHom` of a group extension
  `S` of `G` by `N`
- `(Add?)GroupExtension.Splitting S`: structure for section homomorphisms of a group extension `S`
  of `G` by `N`
- `SemidirectProduct.toGroupExtension φ`: the multiplicative group extension associated to the
  semidirect product coming from `φ : G →* MulAut N`, `1 → N → N ⋊[φ] G → G → 1`

## TODO

If `N` is abelian,

- there is a bijection between `N`-conjugacy classes of
  `(SemidirectProduct.toGroupExtension φ).Splitting` and `groupCohomology.H1`
  (which will be available in the planned file `Mathlib/GroupTheory/GroupExtension/Abelian.lean` to
  be added in a later PR).
- there is a bijection between equivalence classes of group extensions and `groupCohomology.H2`
  (which is also stated as a TODO in `Mathlib/RepresentationTheory/GroupCohomology/LowDegree.lean`).
-/

variable (N E G : Type*)

structure AddGroupExtension [AddGroup N] [AddGroup E] [AddGroup G] where
  /-- The inclusion homomorphism `N →+ E` -/
  inl : N →+ E
  /-- The projection homomorphism `E →+ G` -/
  rightHom : E →+ G
  /-- The inclusion map is injective. -/
  inl_injective : Function.Injective inl
  /-- The range of the inclusion map is equal to the kernel of the projection map. -/
  range_inl_eq_ker_rightHom : inl.range = rightHom.ker
  /-- The projection map is surjective. -/
  rightHom_surjective : Function.Surjective rightHom
