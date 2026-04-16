/-
Extracted from Order/Category/BddDistLat.lean
Genuine: 6 | Conflates: 0 | Dissolved: 0 | Infrastructure: 11
-/
import Origin.Core
import Mathlib.Order.Category.BddLat
import Mathlib.Order.Category.DistLat

noncomputable section

/-!
# The category of bounded distributive lattices

This defines `BddDistLat`, the category of bounded distributive lattices.

Note that this category is sometimes called [`DistLat`](https://ncatlab.org/nlab/show/DistLat) when
being a lattice is understood to entail having a bottom and a top element.
-/

universe u

open CategoryTheory

structure BddDistLat where
  /-- The underlying distrib lattice of a bounded distributive lattice. -/
  toDistLat : DistLat
  [isBoundedOrder : BoundedOrder toDistLat]

namespace BddDistLat

instance : CoeSort BddDistLat Type* :=
  ⟨fun X => X.toDistLat⟩

instance (X : BddDistLat) : DistribLattice X :=
  X.toDistLat.str

attribute [instance] BddDistLat.isBoundedOrder

def of (α : Type*) [DistribLattice α] [BoundedOrder α] : BddDistLat :=
  -- Porting note: was `⟨⟨α⟩⟩`
  -- see https://github.com/leanprover-community/mathlib4/issues/4998
  ⟨{α := α}⟩

@[simp]
theorem coe_of (α : Type*) [DistribLattice α] [BoundedOrder α] : ↥(of α) = α :=
  rfl

instance : Inhabited BddDistLat :=
  ⟨of PUnit⟩

def toBddLat (X : BddDistLat) : BddLat :=
  BddLat.of X

@[simp]
theorem coe_toBddLat (X : BddDistLat) : ↥X.toBddLat = ↥X :=
  rfl

instance : LargeCategory.{u} BddDistLat :=
  InducedCategory.category toBddLat

instance : ConcreteCategory BddDistLat :=
  InducedCategory.concreteCategory toBddLat

instance hasForgetToDistLat : HasForget₂ BddDistLat DistLat where
  forget₂ :=
    -- Porting note: was `⟨X⟩`
    -- see https://github.com/leanprover-community/mathlib4/issues/4998
    { obj := fun X => { α := X }
      map := fun {_ _} => BoundedLatticeHom.toLatticeHom }

instance hasForgetToBddLat : HasForget₂ BddDistLat BddLat :=
  InducedCategory.hasForget₂ toBddLat

@[simps]
def Iso.mk {α β : BddDistLat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

@[simps]
def dual : BddDistLat ⥤ BddDistLat where
  obj X := of Xᵒᵈ
  map {_ _} := BoundedLatticeHom.dual

@[simps functor inverse]
def dualEquiv : BddDistLat ≌ BddDistLat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X

end BddDistLat
