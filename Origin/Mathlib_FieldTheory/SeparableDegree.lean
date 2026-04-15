/-
Extracted from FieldTheory/SeparableDegree.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!

# Separable degree

This file contains basics about the separable degree of a field extension.

## Main definitions

- `Field.Emb F E`: the type of `F`-algebra homomorphisms from `E` to the algebraic closure of `E`
  (the algebraic closure of `F` is usually used in the literature, but our definition has the
  advantage that `Field.Emb F E` lies in the same universe as `E` rather than the maximum over `F`
  and `E`). Usually denoted by $\operatorname{Emb}_F(E)$ in textbooks.

- `Field.finSepDegree F E`: the (finite) separable degree $[E:F]_s$ of an extension `E / F`
  of fields, defined to be the number of `F`-algebra homomorphisms from `E` to the algebraic
  closure of `E`, as a natural number. It is zero if `Field.Emb F E` is not finite.
  Note that if `E / F` is not algebraic, then this definition makes no mathematical sense.

  **Remark:** the `Cardinal`-valued, potentially infinite separable degree `Field.sepDegree F E`
  for a general algebraic extension `E / F` is defined to be the degree of `L / F`, where `L` is
  the separable closure of `F` in `E`, which is not defined in this file yet. Later we
  will show that (`Field.finSepDegree_eq`), if `Field.Emb F E` is finite, then these two
  definitions coincide. If `E / F` is algebraic with infinite separable degree, we have
  `#(Field.Emb F E) = 2 ^ Field.sepDegree F E` instead.
  (See `Field.Emb.cardinal_eq_two_pow_sepDegree` in another file.) For example, if
  $F = \mathbb{Q}$ and $E = \mathbb{Q}( \mu_{p^\infty} )$, then $\operatorname{Emb}_F (E)$
  is in bijection with $\operatorname{Gal}(E/F)$, which is isomorphic to
  $\mathbb{Z}_p^\times$, which is uncountable, whereas $ [E:F] $ is countable.

- `Polynomial.natSepDegree`: the separable degree of a polynomial is a natural number,
  defined to be the number of distinct roots of it over its splitting field.

## Main results

- `Field.embEquivOfEquiv`, `Field.finSepDegree_eq_of_equiv`:
  a random bijection between `Field.Emb F E` and `Field.Emb F K` when `E` and `K` are isomorphic
  as `F`-algebras. In particular, they have the same cardinality (so their
  `Field.finSepDegree` are equal).

- `Field.embEquivOfAdjoinSplits`,
  `Field.finSepDegree_eq_of_adjoin_splits`: a random bijection between `Field.Emb F E` and
  `E →ₐ[F] K` if `E = F(S)` such that every element `s` of `S` is integral (= algebraic) over `F`
  and whose minimal polynomial splits in `K`. In particular, they have the same cardinality.

- `Field.embEquivOfIsAlgClosed`,
  `Field.finSepDegree_eq_of_isAlgClosed`: a random bijection between `Field.Emb F E` and
  `E →ₐ[F] K` when `E / F` is algebraic and `K / F` is algebraically closed.
  In particular, they have the same cardinality.

- `Field.embProdEmbOfIsAlgebraic`, `Field.finSepDegree_mul_finSepDegree_of_isAlgebraic`:
  if `K / E / F` is a field extension tower, such that `K / E` is algebraic,
  then there is a non-canonical bijection `Field.Emb F E × Field.Emb E K ≃ Field.Emb F K`.
  In particular, the separable degrees satisfy the tower law: $[E:F]_s [K:E]_s = [K:F]_s$
  (see also `Module.finrank_mul_finrank`).

- `Field.infinite_emb_of_transcendental`: `Field.Emb` is infinite for transcendental extensions.

- `Polynomial.natSepDegree_le_natDegree`: the separable degree of a polynomial is smaller than
  its degree.

- `Polynomial.natSepDegree_eq_natDegree_iff`: the separable degree of a non-zero polynomial is
  equal to its degree if and only if it is separable.

- `Polynomial.natSepDegree_eq_of_splits`: if a polynomial splits over `E`, then its separable degree
  is equal to the number of distinct roots of it over `E`.

- `Polynomial.natSepDegree_eq_of_isAlgClosed`: the separable degree of a polynomial is equal to
  the number of distinct roots of it over any algebraically closed field.

- `Polynomial.natSepDegree_expand`: if a field `F` is of exponential characteristic
  `q`, then `Polynomial.expand F (q ^ n) f` and `f` have the same separable degree.

- `Polynomial.HasSeparableContraction.natSepDegree_eq`: if a polynomial has separable
  contraction, then its separable degree is equal to its separable contraction degree.

- `Irreducible.natSepDegree_dvd_natDegree`: the separable degree of an irreducible
  polynomial divides its degree.

- `IntermediateField.finSepDegree_adjoin_simple_eq_natSepDegree`: the separable degree of
  `F⟮α⟯ / F` is equal to the separable degree of the minimal polynomial of `α` over `F`.

- `IntermediateField.finSepDegree_adjoin_simple_eq_finrank_iff`: if `α` is algebraic over `F`, then
  the separable degree of `F⟮α⟯ / F` is equal to the degree of `F⟮α⟯ / F` if and only if `α` is a
  separable element.

- `Field.finSepDegree_dvd_finrank`: the separable degree of any field extension `E / F` divides
  the degree of `E / F`.

- `Field.finSepDegree_le_finrank`: the separable degree of a finite extension `E / F` is smaller
  than the degree of `E / F`.

- `Field.finSepDegree_eq_finrank_iff`: if `E / F` is a finite extension, then its separable degree
  is equal to its degree if and only if it is a separable extension.

- `IntermediateField.isSeparable_adjoin_simple_iff_isSeparable`: `F⟮x⟯ / F` is a separable extension
  if and only if `x` is a separable element.

- `Algebra.IsSeparable.trans`: if `E / F` and `K / E` are both separable, then `K / F` is also
  separable.

## Tags

separable degree, degree, polynomial

-/

open Module Polynomial IntermediateField Field

noncomputable section

universe u v w

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

variable (K : Type w) [Field K] [Algebra F K]

namespace Field

abbrev Emb := E →ₐ[F] AlgebraicClosure E

def finSepDegree : ℕ := Nat.card (Emb F E)

-- INSTANCE (free from Core): instInhabitedEmb

-- INSTANCE (free from Core): instNeZeroFinSepDegree

def embEquivOfEquiv (i : E ≃ₐ[F] K) :
    Emb F E ≃ Emb F K := AlgEquiv.arrowCongr i <| AlgEquiv.symm <| by
  let _ : Algebra E K := i.toAlgHom.toRingHom.toAlgebra
  have : Algebra.IsAlgebraic E K := by
    constructor
    intro x
    have h := isAlgebraic_algebraMap (R := E) (A := K) (i.symm.toAlgHom x)
    rw [show ∀ y : E, (algebraMap E K) y = i.toAlgHom y from fun y ↦ rfl] at h
    simpa only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, AlgEquiv.apply_symm_apply] using h
  apply AlgEquiv.restrictScalars (R := F) (S := E)
  exact IsAlgClosure.equivOfAlgebraic E K (AlgebraicClosure K) (AlgebraicClosure E)

theorem finSepDegree_eq_of_equiv (i : E ≃ₐ[F] K) :
    finSepDegree F E = finSepDegree F K := Nat.card_congr (embEquivOfEquiv F E K i)
