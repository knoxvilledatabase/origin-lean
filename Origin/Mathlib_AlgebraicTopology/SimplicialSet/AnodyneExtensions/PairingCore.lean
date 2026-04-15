/-
Extracted from AlgebraicTopology/SimplicialSet/AnodyneExtensions/PairingCore.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Helper structure in order to construct pairings

In this file, we introduce a helper structure `Subcomplex.PairingCore`
in order to construct a pairing for a subcomplex of a simplicial set.
The main difference with `Subcomplex.Pairing` are that we provide
an index type `ι` and a function `dim : ι → ℕ` which allow to
parametrize type (II) and (I) simplices in such a way that, *definitionally*,
their dimensions are respectively `dim s` or `dim s + 1` for `s : ι`.

-/

universe v u

open CategoryTheory Simplicial

namespace SSet.Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

structure PairingCore where
  /-- the index type -/
  ι : Type v
  /-- the dimension of each type (II) simplex -/
  dim (s : ι) : ℕ
  /-- the family of type (I) simplices -/
  simplex (s : ι) : X _⦋dim s + 1⦌
  /-- the corresponding type (II) simplex is the `1`-codimensional
    face given by this index -/
  index (s : ι) : Fin (dim s + 2)
  nonDegenerate₁ (s : ι) : simplex s ∈ X.nonDegenerate _
  nonDegenerate₂ (s : ι) : X.δ (index s) (simplex s) ∈ X.nonDegenerate _
  notMem₁ (s : ι) : simplex s ∉ A.obj _
  notMem₂ (s : ι) : X.δ (index s) (simplex s) ∉ A.obj _
  injective_type₁' {s t : ι} (h : S.mk (simplex s) = S.mk (simplex t)) : s = t
  injective_type₂' {s t : ι}
    (h : S.mk (X.δ (index s) (simplex s)) = S.mk (X.δ (index t) (simplex t))) : s = t
  type₁_ne_type₂' (s t : ι) : S.mk (simplex s) ≠ S.mk (X.δ (index t) (simplex t))
  surjective' (x : A.N) :
    ∃ (s : ι), x.toS = S.mk (simplex s) ∨ x.toS = S.mk (X.δ (index s) (simplex s))

variable {A}

noncomputable def Pairing.pairingCore (P : A.Pairing) [P.IsProper] :
    A.PairingCore where
  ι := P.II
  dim s := s.val.dim
  simplex s := ((P.p s).val.cast (P.isUniquelyCodimOneFace s).dim_eq).simplex
  index s := (P.isUniquelyCodimOneFace s).index rfl
  nonDegenerate₁ s := ((P.p s).val.cast (P.isUniquelyCodimOneFace s).dim_eq).nonDegenerate
  nonDegenerate₂ s := by
    rw [(P.isUniquelyCodimOneFace s).δ_index rfl]
    exact s.val.nonDegenerate
  notMem₁ s := ((P.p s).val.cast (P.isUniquelyCodimOneFace s).dim_eq).notMem
  notMem₂ s := by
    rw [(P.isUniquelyCodimOneFace s).δ_index rfl]
    exact s.val.notMem
  injective_type₁' {s t} _ := by
    apply P.p.injective
    rwa [Subtype.ext_iff, N.ext_iff, SSet.N.ext_iff,
      ← (P.p s).val.cast_eq_self (P.isUniquelyCodimOneFace s).dim_eq,
      ← (P.p t).val.cast_eq_self (P.isUniquelyCodimOneFace t).dim_eq]
  injective_type₂' {s t} h := by
    rw [(P.isUniquelyCodimOneFace s).δ_index rfl,
      (P.isUniquelyCodimOneFace t).δ_index rfl] at h
    rwa [Subtype.ext_iff, N.ext_iff, SSet.N.ext_iff]
  type₁_ne_type₂' s t h := (P.ne (P.p s) t) (by
    rw [(P.isUniquelyCodimOneFace t).δ_index rfl] at h
    rwa [← (P.p s).val.cast_eq_self (P.isUniquelyCodimOneFace s).dim_eq,
      N.ext_iff, SSet.N.ext_iff])
  surjective' x := by
    obtain ⟨s, rfl | rfl⟩ := P.exists_or x
    · refine ⟨s, Or.inr ?_⟩
      simp [(P.isUniquelyCodimOneFace s).δ_index]
    · refine ⟨s, Or.inl ?_⟩
      nth_rw 1 [← (P.p s).val.cast_eq_self (P.isUniquelyCodimOneFace s).dim_eq]
      rfl

namespace PairingCore

variable (h : A.PairingCore)
