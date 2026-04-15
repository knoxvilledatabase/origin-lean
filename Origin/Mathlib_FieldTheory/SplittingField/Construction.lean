/-
Extracted from FieldTheory/SplittingField/Construction.lean
Genuine: 11 of 25 | Dissolved: 4 | Infrastructure: 10
-/
import Origin.Core

/-!
# Splitting fields

In this file we prove the existence and uniqueness of splitting fields.

## Main definitions

* `Polynomial.SplittingField f`: A fixed splitting field of the polynomial `f`.

## Main statements

* `Polynomial.IsSplittingField.algEquiv`: Every splitting field of a polynomial `f` is isomorphic
  to `SplittingField f` and thus, being a splitting field is unique up to isomorphism.

## Implementation details
We construct a `SplittingFieldAux` without worrying about whether the instances satisfy nice
definitional equalities. Then the actual `SplittingField` is defined to be a quotient of a
`MvPolynomial` ring by the kernel of the obvious map into `SplittingFieldAux`. Because the
actual `SplittingField` will be a quotient of a `MvPolynomial`, it has nice instances on it.

-/

noncomputable section

universe u v w

variable {F : Type u} {K : Type v} {L : Type w}

namespace Polynomial

variable [Field K] [Field L] [Field F]

open Polynomial

section SplittingField

open Classical in

def factor (f : K[X]) : K[X] :=
  if H : ∃ g, Irreducible g ∧ g ∣ f then Classical.choose H else X

theorem irreducible_factor (f : K[X]) : Irreducible (factor f) := by
  rw [factor]
  split_ifs with H
  · exact (Classical.choose_spec H).1
  · exact irreducible_X

theorem fact_irreducible_factor (f : K[X]) : Fact (Irreducible (factor f)) :=
  ⟨irreducible_factor f⟩

attribute [local instance] fact_irreducible_factor

theorem factor_dvd_of_not_isUnit {f : K[X]} (hf1 : ¬IsUnit f) : factor f ∣ f := by
  by_cases hf2 : f = 0; · rw [hf2]; exact dvd_zero _
  rw [factor, dif_pos (WfDvdMonoid.exists_irreducible_factor hf1 hf2)]
  exact (Classical.choose_spec <| WfDvdMonoid.exists_irreducible_factor hf1 hf2).2

-- DISSOLVED: factor_dvd_of_degree_ne_zero

-- DISSOLVED: factor_dvd_of_natDegree_ne_zero

-- DISSOLVED: isCoprime_iff_aeval_ne_zero

def removeFactor (f : K[X]) : Polynomial (AdjoinRoot <| factor f) :=
  map (AdjoinRoot.of f.factor) f /ₘ (X - C (AdjoinRoot.root f.factor))

-- DISSOLVED: X_sub_C_mul_removeFactor

theorem natDegree_removeFactor (f : K[X]) : f.removeFactor.natDegree = f.natDegree - 1 := by
  rw [removeFactor, natDegree_divByMonic _ (monic_X_sub_C _), natDegree_map, natDegree_X_sub_C]

theorem natDegree_removeFactor' {f : K[X]} {n : ℕ} (hfn : f.natDegree = n + 1) :
    f.removeFactor.natDegree = n := by rw [natDegree_removeFactor, hfn, n.add_sub_cancel]

def SplittingFieldAuxAux (n : ℕ) : ∀ {K : Type u} [Field K], K[X] →
    Σ (L : Type u) (_ : Field L), Algebra K L :=
  -- Porting note: added motive
  Nat.recOn (motive := fun (_x : ℕ) => ∀ {K : Type u} [_inst_4 : Field K], K[X] →
      Σ (L : Type u) (_ : Field L), Algebra K L) n
    (fun {K} _ _ => ⟨K, inferInstance, inferInstance⟩)
    fun _ ih _ _ f =>
      let ⟨L, fL, _⟩ := ih f.removeFactor
      ⟨L, fL, (RingHom.comp (algebraMap _ _) (AdjoinRoot.of f.factor)).toAlgebra⟩

def SplittingFieldAux (n : ℕ) {K : Type u} [Field K] (f : K[X]) : Type u :=
  (SplittingFieldAuxAux n f).1

-- INSTANCE (free from Core): SplittingFieldAux.field

-- INSTANCE (free from Core): (n

-- INSTANCE (free from Core): SplittingFieldAux.algebra

namespace SplittingFieldAux

-- INSTANCE (free from Core): algebra'''

-- INSTANCE (free from Core): algebra'

-- INSTANCE (free from Core): algebra''

-- INSTANCE (free from Core): scalar_tower'

set_option backward.isDefEq.respectTransparency false in

protected theorem splits (n : ℕ) :
    ∀ {K : Type u} [Field K], ∀ (f : K[X]) (_hfn : f.natDegree = n),
      Splits (f.map (algebraMap K <| SplittingFieldAux n f)) :=
  Nat.recOn (motive := fun n => ∀ {K : Type u} [Field K], ∀ (f : K[X]) (_hfn : f.natDegree = n),
      Splits (f.map (algebraMap K <| SplittingFieldAux n f))) n
    (fun {_} _ _ hf =>
      Splits.of_degree_le_one <| degree_map_le.trans
        (le_trans degree_le_natDegree <| hf.symm ▸ WithBot.coe_le_coe.2 zero_le_one))
    fun n ih {K} _ f hf => by
    rw [algebraMap_succ, ← map_map,
      ← X_sub_C_mul_removeFactor f fun h => by rw [h] at hf; cases hf]
    rw [Polynomial.map_mul]
    exact Splits.mul ((Splits.X_sub_C _).map _) (ih _ (natDegree_removeFactor' hf))

set_option backward.isDefEq.respectTransparency false in

theorem adjoin_rootSet (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (_hfn : f.natDegree = n),
        Algebra.adjoin K (f.rootSet (SplittingFieldAux n f)) = ⊤ :=
  Nat.recOn (motive := fun n =>
    ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (_hfn : f.natDegree = n),
        Algebra.adjoin K (f.rootSet (SplittingFieldAux n f)) = ⊤)
    n (fun {_} _ _ _hf => Algebra.eq_top_iff.2 fun x => Subalgebra.range_le _ ⟨x, rfl⟩)
    fun n ih {K} _ f hfn => by
    have hndf : f.natDegree ≠ 0 := by intro h; rw [h] at hfn; cases hfn
    have hfn0 : f ≠ 0 := by intro h; rw [h] at hndf; exact hndf rfl
    have hmf0 : map (algebraMap K (SplittingFieldAux n.succ f)) f ≠ 0 := map_ne_zero hfn0
    classical
    rw [rootSet_def, aroots_def]
    rw [algebraMap_succ, ← map_map, ← X_sub_C_mul_removeFactor _ hndf, Polynomial.map_mul] at hmf0 ⊢
    rw [roots_mul hmf0, Polynomial.map_sub, map_X, map_C, roots_X_sub_C, Multiset.toFinset_add,
      Finset.coe_union, Multiset.toFinset_singleton, Finset.coe_singleton,
      Algebra.adjoin_union_eq_adjoin_adjoin, ← Set.image_singleton]
    -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [Algebra.adjoin_algebraMap K (SplittingFieldAux n f.removeFactor)]
    rw [AdjoinRoot.adjoinRoot_eq_top, Algebra.map_top]
    -- Porting note: was `rw`
    erw [IsScalarTower.adjoin_range_toAlgHom K (AdjoinRoot f.factor)
        (SplittingFieldAux n f.removeFactor)
        (f.removeFactor.rootSet (SplittingFieldAux n f.removeFactor))]
    rw [ih _ (natDegree_removeFactor' hfn), Subalgebra.restrictScalars_top]

-- INSTANCE (free from Core): (f

end SplittingFieldAux
