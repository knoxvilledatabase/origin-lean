/-
Extracted from CategoryTheory/Sites/NonabelianCohomology/H1.lean
Genuine: 15 | Conflates: 0 | Dissolved: 0 | Infrastructure: 14
-/
import Origin.Core
import Mathlib.Algebra.Category.Grp.Basic

noncomputable section

/-! The cohomology of a sheaf of groups in degree 1

In this file, we shall define the cohomology in degree 1 of a sheaf
of groups (TODO).

Currently, given a presheaf of groups `G : Cᵒᵖ ⥤ Grp` and a family
of objects `U : I → C`, we define 1-cochains/1-cocycles/H^1 with values
in `G` over `U`. (This definition neither requires the assumption that `G`
is a sheaf, nor that `U` covers the terminal object.)
As we do not assume that `G` is a presheaf of abelian groups, this
cohomology theory is only defined in low degrees; in the abelian
case, it would be a particular case of Čech cohomology (TODO).

## TODO

* show that if `1 ⟶ G₁ ⟶ G₂ ⟶ G₃ ⟶ 1` is a short exact sequence of sheaves
of groups, and `x₃` is a global section of `G₃` which can be locally lifted
to a section of `G₂`, there is an associated canonical cohomology class of `G₁`
which is trivial iff `x₃` can be lifted to a global section of `G₂`.
(This should hold more generally if `G₂` is a sheaf of sets on which `G₁` acts
freely, and `G₃` is the quotient sheaf.)
* deduce a similar result for abelian sheaves
* when the notion of quasi-coherent sheaves on schemes is defined, show that
if `0 ⟶ Q ⟶ M ⟶ N ⟶ 0` is an exact sequence of abelian sheaves over a scheme `X`
and `Q` is the underlying sheaf of a quasi-coherent sheaf, then `M(U) ⟶ N(U)`
is surjective for any affine open `U`.
* take the colimit of `OneCohomology G U` over all covering families `U` (for
a Grothendieck topology)

# References

* [J. Frenkel, *Cohomologie non abélienne et espaces fibrés*][frenkel1957]

-/

universe w' w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace PresheafOfGroups

variable (G : Cᵒᵖ ⥤ Grp.{w}) {I : Type w'} (U : I → C)

def ZeroCochain := ∀ (i : I), G.obj (Opposite.op (U i))

instance : Group (ZeroCochain G U) := Pi.group

namespace Cochain₀

@[simp]
lemma inv_apply (γ : ZeroCochain G U) (i : I) : γ⁻¹ i = (γ i)⁻¹ := rfl

end Cochain₀

@[ext]
structure OneCochain where
  /-- the data involved in a 1-cochain -/
  ev (i j : I) ⦃T : C⦄ (a : T ⟶ U i) (b : T ⟶ U j) : G.obj (Opposite.op T)
  ev_precomp (i j : I) ⦃T T' : C⦄ (φ : T ⟶ T') (a : T' ⟶ U i) (b : T' ⟶ U j) :
    G.map φ.op (ev i j a b) = ev i j (φ ≫ a) (φ ≫ b) := by aesop

namespace OneCochain

attribute [simp] OneCochain.ev_precomp

instance : One (OneCochain G U) where
  one := { ev := fun _ _ _ _ _ ↦ 1 }

variable {G U}

instance : Mul (OneCochain G U) where
  mul γ₁ γ₂ := { ev := fun i j _ a b ↦ γ₁.ev i j a b * γ₂.ev i j a b }

instance : Inv (OneCochain G U) where
  inv γ := { ev := fun i j _ a b ↦ (γ.ev i j a b) ⁻¹}

instance : Group (OneCochain G U) where
  mul_assoc _ _ _ := by ext; apply mul_assoc
  one_mul _ := by ext; apply one_mul
  mul_one _ := by ext; apply mul_one
  inv_mul_cancel _ := by ext; apply inv_mul_cancel

end OneCochain

structure OneCocycle extends OneCochain G U where
  ev_trans (i j k : I) ⦃T : C⦄ (a : T ⟶ U i) (b : T ⟶ U j) (c : T ⟶ U k) :
      ev i j a b * ev j k b c = ev i k a c := by aesop

namespace OneCocycle

instance : One (OneCocycle G U) where
  one := OneCocycle.mk 1

@[simp]
lemma ev_refl (γ : OneCocycle G U) (i : I) ⦃T : C⦄ (a : T ⟶ U i) :
    γ.ev i i a a = 1 := by
  simpa using γ.ev_trans i i i a a a

lemma ev_symm (γ : OneCocycle G U) (i j : I) ⦃T : C⦄ (a : T ⟶ U i) (b : T ⟶ U j) :
    γ.ev i j a b = (γ.ev j i b a)⁻¹ := by
  rw [← mul_left_inj (γ.ev j i b a), γ.ev_trans i j i a b a,
    ev_refl, inv_mul_cancel]

end OneCocycle

variable {G U}

def OneCohomologyRelation (γ₁ γ₂ : OneCochain G U) (α : ZeroCochain G U) : Prop :=
  ∀ (i j : I) ⦃T : C⦄ (a : T ⟶ U i) (b : T ⟶ U j),
    G.map a.op (α i) * γ₁.ev i j a b = γ₂.ev i j a b * G.map b.op (α j)

namespace OneCohomologyRelation

lemma refl (γ : OneCochain G U) : OneCohomologyRelation γ γ 1 := fun _ _ _ _ _ ↦ by simp

lemma symm {γ₁ γ₂ : OneCochain G U} {α : ZeroCochain G U} (h : OneCohomologyRelation γ₁ γ₂ α) :
    OneCohomologyRelation γ₂ γ₁ α⁻¹ := fun i j T a b ↦ by
  rw [← mul_left_inj (G.map b.op (α j)), mul_assoc, ← h i j a b,
    mul_assoc, Cochain₀.inv_apply, map_inv, inv_mul_cancel_left,
    Cochain₀.inv_apply, map_inv, inv_mul_cancel, mul_one]

lemma trans {γ₁ γ₂ γ₃ : OneCochain G U} {α β : ZeroCochain G U}
    (h₁₂ : OneCohomologyRelation γ₁ γ₂ α) (h₂₃ : OneCohomologyRelation γ₂ γ₃ β) :
    OneCohomologyRelation γ₁ γ₃ (β * α) := fun i j T a b ↦ by
  dsimp
  rw [map_mul, map_mul, mul_assoc, h₁₂ i j a b, ← mul_assoc,
    h₂₃ i j a b, mul_assoc]

end OneCohomologyRelation

namespace OneCocycle

def IsCohomologous (γ₁ γ₂ : OneCocycle G U) : Prop :=
  ∃ (α : ZeroCochain G U), OneCohomologyRelation γ₁.toOneCochain γ₂.toOneCochain α

variable (G U)

lemma equivalence_isCohomologous :
    _root_.Equivalence (IsCohomologous (G := G) (U := U)) where
  refl γ := ⟨_, OneCohomologyRelation.refl γ.toOneCochain⟩
  symm := by
    rintro γ₁ γ₂ ⟨α, h⟩
    exact ⟨_, h.symm⟩
  trans := by
    rintro γ₁ γ₂ γ₂ ⟨α, h⟩ ⟨β, h'⟩
    exact ⟨_, h.trans h'⟩

end OneCocycle

variable (G U) in

def H1 := Quot (OneCocycle.IsCohomologous (G := G) (U := U))

def OneCocycle.class (γ : OneCocycle G U) : H1 G U := Quot.mk _ γ

instance : One (H1 G U) where
  one := OneCocycle.class 1

lemma OneCocycle.class_eq_iff (γ₁ γ₂ : OneCocycle G U) :
    γ₁.class = γ₂.class ↔ γ₁.IsCohomologous γ₂ :=
  (equivalence_isCohomologous _ _ ).quot_mk_eq_iff _ _

lemma OneCocycle.IsCohomologous.class_eq {γ₁ γ₂ : OneCocycle G U} (h : γ₁.IsCohomologous γ₂) :
    γ₁.class = γ₂.class :=
  Quot.sound h

end PresheafOfGroups

end CategoryTheory
