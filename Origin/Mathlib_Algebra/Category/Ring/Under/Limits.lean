/-
Extracted from Algebra/Category/Ring/Under/Limits.lean
Genuine: 9 of 11 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Limits in `Under R` for a commutative ring `R`

We show that `Under.pushout f` is left-exact, i.e. preserves finite limits, if `f : R ⟶ S` is
flat.

-/

noncomputable section

universe v u

open TensorProduct CategoryTheory Limits

variable {R S : CommRingCat.{u}}

namespace CommRingCat.Under

section Algebra

variable [Algebra R S]

section Pi

variable {ι : Type u} (P : ι → Under R)

def piFan : Fan P :=
  Fan.mk (Under.mk <| ofHom <| Pi.ringHom (fun i ↦ (P i).hom.hom))
    (fun i ↦ Under.homMk (ofHom <| Pi.evalRingHom _ i))

def piFanIsLimit : IsLimit (piFan P) :=
  isLimitOfReflects (Under.forget R) <|
    (isLimitMapConeFanMkEquiv (Under.forget R) P _).symm <|
      CommRingCat.piFanIsLimit (fun i ↦ (P i).right)

variable (S) in

def tensorProductFan : Fan (fun i ↦ mkUnder S (S ⊗[R] (P i).right)) :=
  Fan.mk (mkUnder S <| S ⊗[R] ∀ i, (P i).right)
    (fun i ↦ AlgHom.toUnder <|
      Algebra.TensorProduct.map (AlgHom.id S S) (Pi.evalAlgHom R (fun j ↦ (P j).right) i))

variable (S) in

def tensorProductFan' : Fan (fun i ↦ mkUnder S (S ⊗[R] (P i).right)) :=
  Fan.mk (mkUnder S <| ∀ i, S ⊗[R] (P i).right)
    (fun i ↦ AlgHom.toUnder <| Pi.evalAlgHom S _ i)

set_option backward.isDefEq.respectTransparency false in

def tensorProductFanIso [Fintype ι] [DecidableEq ι] :
    tensorProductFan S P ≅ tensorProductFan' S P :=
  Fan.ext (Algebra.TensorProduct.piRight R S _ _).toUnder <| fun i ↦ by
    dsimp only [tensorProductFan, Fan.mk_pt, fan_mk_proj, tensorProductFan']
    apply CommRingCat.mkUnder_ext
    intro c
    induction c
    · simp only [map_zero, Under.comp_right]
    · simp only [AlgHom.toUnder_right, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
        Pi.evalAlgHom_apply, Under.comp_right, comp_apply, AlgEquiv.toUnder_hom_right_apply,
        Algebra.TensorProduct.piRight_tmul]
    · simp_all

open Classical in

def tensorProductFanIsLimit [Finite ι] : IsLimit (tensorProductFan S P) :=
  letI : Fintype ι := Fintype.ofFinite ι
  (IsLimit.equivIsoLimit (tensorProductFanIso P)).symm (Under.piFanIsLimit _)

noncomputable -- marked noncomputable for performance (only)

def piFanTensorProductIsLimit [Finite ι] : IsLimit ((tensorProd R S).mapCone (Under.piFan P)) :=
  (isLimitMapConeFanMkEquiv (tensorProd R S) P _).symm <| tensorProductFanIsLimit P

-- INSTANCE (free from Core): (J

-- INSTANCE (free from Core): :

end Pi

section Equalizer

lemma equalizer_comp {A B : Under R} (f g : A ⟶ B) :
    (AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder ≫ f =
    (AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder ≫ g := by
  ext (a : AlgHom.equalizer (toAlgHom f) (toAlgHom g))
  exact a.property

set_option backward.isDefEq.respectTransparency false in

def equalizerFork {A B : Under R} (f g : A ⟶ B) :
    Fork f g :=
  Fork.ofι ((AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder)
    (by rw [equalizer_comp])
