/-
Extracted from Order/Category/BoolAlg.lean
Genuine: 7 | Conflates: 0 | Dissolved: 0 | Infrastructure: 10
-/
import Origin.Core
import Mathlib.Order.Category.HeytAlg
import Mathlib.Order.Hom.CompleteLattice

noncomputable section

/-!
# The category of boolean algebras

This defines `BoolAlg`, the category of boolean algebras.
-/

open OrderDual Opposite Set

universe u

open CategoryTheory

def BoolAlg :=
  Bundled BooleanAlgebra

namespace BoolAlg

instance : CoeSort BoolAlg Type* :=
  Bundled.coeSort

instance instBooleanAlgebra (X : BoolAlg) : BooleanAlgebra X :=
  X.str

def of (α : Type*) [BooleanAlgebra α] : BoolAlg :=
  Bundled.of α

instance : Inhabited BoolAlg :=
  ⟨of PUnit⟩

def toBddDistLat (X : BoolAlg) : BddDistLat :=
  BddDistLat.of X

instance : LargeCategory.{u} BoolAlg :=
  InducedCategory.category toBddDistLat

instance : ConcreteCategory BoolAlg :=
  InducedCategory.concreteCategory toBddDistLat

instance hasForgetToBddDistLat : HasForget₂ BoolAlg BddDistLat :=
  InducedCategory.hasForget₂ toBddDistLat

section

attribute [local instance] BoundedLatticeHomClass.toBiheytingHomClass

@[simps]
instance hasForgetToHeytAlg : HasForget₂ BoolAlg HeytAlg where
  forget₂ :=
    { obj := fun X => {α := X}
      -- Porting note: was `fun {X Y} f => show BoundedLatticeHom X Y from f`
      -- which already looks like a hack, but I don't understand why this hack works now and
      -- the old one didn't
      map := fun {X Y} (f : BoundedLatticeHom X Y) => show HeytingHom X Y from f }

end

@[simps]
def Iso.mk {α β : BoolAlg.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

@[simps]
def dual : BoolAlg ⥤ BoolAlg where
  obj X := of Xᵒᵈ
  map {_ _} := BoundedLatticeHom.dual

@[simps functor inverse]
def dualEquiv : BoolAlg ≌ BoolAlg where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X

end BoolAlg

@[simps]
def typeToBoolAlgOp : Type u ⥤ BoolAlgᵒᵖ where
  obj X := op <| BoolAlg.of (Set X)
  map {X Y} f := Quiver.Hom.op
    (CompleteLatticeHom.setPreimage f : BoundedLatticeHom (Set Y) (Set X))
