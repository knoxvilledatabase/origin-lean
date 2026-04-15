/-
Extracted from AlgebraicGeometry/EllipticCurve/Affine/Point.lean
Genuine: 5 of 9 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Nonsingular points and the group law in affine coordinates

Let `W` be a Weierstrass curve over a field `F` given by a Weierstrass equation `W(X, Y) = 0` in
affine coordinates. The type of nonsingular points `W⟮F⟯` in affine coordinates is an inductive,
consisting of the unique point at infinity `𝓞` and nonsingular affine points `(x, y)`. Then `W⟮F⟯`
can be endowed with a group law, with `𝓞` as the identity nonsingular point, which is uniquely
determined by the formulae in `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean`.

With this description, there is an addition-preserving injection between `W⟮F⟯` and the ideal class
group of the *affine coordinate ring* `F[W] := F[X, Y] / ⟨W(X, Y)⟩` of `W`. This is given by mapping
`𝓞` to the trivial ideal class and a nonsingular affine point `(x, y)` to the ideal class of the
invertible ideal `⟨X - x, Y - y⟩`. Proving that this is well-defined and preserves addition reduces
to equalities of integral ideals checked in `WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul`
and in `WeierstrassCurve.Affine.CoordinateRing.XYIdeal_mul_XYIdeal` via explicit ideal computations.
Now `F[W]` is a free rank two `F[X]`-algebra with basis `{1, Y}`, so every element of `F[W]` is of
the form `p + qY` for some `p, q` in `F[X]`, and there is an algebra norm `N : F[W] → F[X]`.
Injectivity can then be shown by computing the degree of such a norm `N(p + qY)` in two different
ways, which is done in `WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis` and in the
auxiliary lemmas in the proof of `WeierstrassCurve.Affine.Point.instAddCommGroup`.

This file defines the group law on nonsingular points `W⟮F⟯` in affine coordinates.

## Main definitions

* `WeierstrassCurve.Affine.CoordinateRing`: the affine coordinate ring `F[W]`.
* `WeierstrassCurve.Affine.CoordinateRing.basis`: the power basis of `F[W]` over `F[X]`.
* `WeierstrassCurve.Affine.Point`: a nonsingular point in affine coordinates.
* `WeierstrassCurve.Affine.Point.neg`: the negation of a nonsingular point in affine coordinates.
* `WeierstrassCurve.Affine.Point.add`: the addition of a nonsingular point in affine coordinates.

## Main statements

* `WeierstrassCurve.Affine.CoordinateRing.instIsDomainCoordinateRing`: the affine coordinate ring
  of a Weierstrass curve is an integral domain.
* `WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis`: the degree of the norm of an
  element in the affine coordinate ring in terms of its power basis.
* `WeierstrassCurve.Affine.Point.instAddCommGroup`: the type of nonsingular points `W⟮F⟯` in affine
  coordinates forms an abelian group under addition.

## Notation

* `W⟮K⟯`: the group of nonsingular points on `W` base changed to `K`.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]
* https://drops.dagstuhl.de/storage/00lipics/lipics-vol268-itp2023/LIPIcs.ITP.2023.6/LIPIcs.ITP.2023.6.pdf

## Tags

elliptic curve, affine, point, group law, class group
-/

open FractionalIdeal (coeIdeal_mul)

open Ideal hiding map_mul

open Module Polynomial

open scoped nonZeroDivisors Polynomial.Bivariate

local macro "C_simp" : tactic =>

  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

universe r s u v w

namespace WeierstrassCurve

variable {R : Type r} {S : Type s} {A F : Type u} {B K : Type v} {L : Type w} [CommRing R]
  [CommRing S] [CommRing A] [CommRing B] [Field F] [Field K] [Field L] {W' : Affine R}
  {W : Affine F}

namespace Affine

/-! ## The affine coordinate ring -/

variable (W') in

abbrev CoordinateRing : Type r :=
  AdjoinRoot W'.polynomial

variable (W') in

abbrev FunctionField : Type r :=
  FractionRing W'.CoordinateRing

namespace CoordinateRing

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): [Subsingleton

variable (W') in

noncomputable abbrev mk : R[X][Y] →+* W'.CoordinateRing :=
  AdjoinRoot.mk W'.polynomial

open scoped Classical in

variable (W') in

protected noncomputable def basis : Basis (Fin 2) R[X] W'.CoordinateRing :=
  (subsingleton_or_nontrivial R).by_cases (fun _ => default) fun _ =>
    (AdjoinRoot.powerBasis' monic_polynomial).basis.reindex <| finCongr natDegree_polynomial

set_option backward.isDefEq.respectTransparency false in

lemma basis_apply (n : Fin 2) :
    CoordinateRing.basis W' n = (AdjoinRoot.powerBasis' monic_polynomial).gen ^ (n : ℕ) := by
  classical
  nontriviality R
  rw [CoordinateRing.basis, Or.by_cases, dif_neg <| not_subsingleton R, Basis.reindex_apply,
    PowerBasis.basis_eq_pow, finCongr_symm_apply, Fin.val_cast]
