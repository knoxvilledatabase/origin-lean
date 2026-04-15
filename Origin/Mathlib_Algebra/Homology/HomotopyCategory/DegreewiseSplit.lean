/-
Extracted from Algebra/Homology/HomotopyCategory/DegreewiseSplit.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Degreewise split exact sequences of cochain complexes

The main result of this file is the lemma
`HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit` which asserts
that a triangle in `HomotopyCategory C (ComplexShape.up ℤ)`
is distinguished iff it is isomorphic to the triangle attached to a
degreewise split short exact sequence of cochain complexes.

-/

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits Pretriangulated Preadditive

universe v

variable {C : Type*} [Category.{v} C] [Preadditive C]

namespace CochainComplex

open HomologicalComplex HomComplex

variable (S : ShortComplex (CochainComplex C ℤ))
  (σ : ∀ n, (S.map (eval C _ n)).Splitting)

set_option backward.isDefEq.respectTransparency false in

def cocycleOfDegreewiseSplit : Cocycle S.X₃ S.X₁ 1 :=
  Cocycle.mk
    (Cochain.mk (fun p q _ => (σ p).s ≫ S.X₂.d p q ≫ (σ q).r)) 2 (by lia) (by
      ext p _ rfl
      have := mono_of_mono_fac (σ (p + 2)).f_r
      have r_f := fun n => (σ n).r_f
      have s_g := fun n => (σ n).s_g
      dsimp at this r_f s_g ⊢
      rw [δ_v 1 2 (by lia) _ p (p + 2) (by lia) (p + 1) (p + 1)
        (by lia) (by lia), Cochain.mk_v, Cochain.mk_v,
        show Int.negOnePow 2 = 1 by rfl, one_smul, assoc, assoc,
        ← cancel_mono (S.f.f (p + 2)), add_comp, assoc, assoc, assoc,
        assoc, assoc, assoc, zero_comp, ← S.f.comm, reassoc_of% (r_f (p + 1)),
        sub_comp, comp_sub, comp_sub, assoc, id_comp, d_comp_d, comp_zero, zero_sub,
        ← S.g.comm_assoc, reassoc_of% (s_g p), r_f (p + 2), comp_sub, comp_sub, comp_id,
        comp_sub, ← S.g.comm_assoc, reassoc_of% (s_g (p + 1)), d_comp_d_assoc, zero_comp,
        sub_zero, neg_add_cancel])

def homOfDegreewiseSplit : S.X₃ ⟶ S.X₁⟦(1 : ℤ)⟧ :=
  ((Cocycle.equivHom _ _).symm ((cocycleOfDegreewiseSplit S σ).rightShift 1 0 (zero_add 1)))
