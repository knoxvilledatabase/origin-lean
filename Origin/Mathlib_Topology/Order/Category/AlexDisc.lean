/-
Extracted from Topology/Order/Category/AlexDisc.lean
Genuine: 5 | Conflates: 0 | Dissolved: 0 | Infrastructure: 12
-/
import Origin.Core
import Mathlib.Topology.Specialization

noncomputable section

/-!
# Category of Alexandrov-discrete topological spaces

This defines `AlexDisc`, the category of Alexandrov-discrete topological spaces with continuous
maps, and proves it's equivalent to the category of preorders.
-/

open CategoryTheory Topology

class AlexandrovDiscreteSpace (α : Type*) extends TopologicalSpace α, AlexandrovDiscrete α

def AlexDisc := Bundled AlexandrovDiscreteSpace

namespace AlexDisc

instance instCoeSort : CoeSort AlexDisc Type* := Bundled.coeSort

instance instTopologicalSpace (α : AlexDisc) : TopologicalSpace α := α.2.1

instance instAlexandrovDiscrete (α : AlexDisc) : AlexandrovDiscrete α := α.2.2

instance : BundledHom.ParentProjection @AlexandrovDiscreteSpace.toTopologicalSpace := ⟨⟩

deriving instance LargeCategory for AlexDisc

instance instConcreteCategory : ConcreteCategory AlexDisc := BundledHom.concreteCategory _

instance instHasForgetToTop : HasForget₂ AlexDisc TopCat := BundledHom.forget₂ _ _

instance forgetToTop_full : (forget₂ AlexDisc TopCat).Full := BundledHom.forget₂_full _ _

instance forgetToTop_faithful : (forget₂ AlexDisc TopCat).Faithful where

def of (α : Type*) [TopologicalSpace α] [AlexandrovDiscrete α] : AlexDisc := ⟨α, ⟨⟩⟩

attribute [local instance] CategoryTheory.ConcreteCategory.instFunLike

@[simps]
def Iso.mk {α β : AlexDisc} (e : α ≃ₜ β) : α ≅ β where
  hom := (e : ContinuousMap α β)
  inv := (e.symm : ContinuousMap β α)
  hom_inv_id := DFunLike.ext _ _ e.symm_apply_apply
  inv_hom_id := DFunLike.ext _ _ e.apply_symm_apply

end AlexDisc

@[simps]
def alexDiscEquivPreord : AlexDisc ≌ Preord where
  functor := forget₂ _ _ ⋙ topToPreord
  inverse := { obj := fun X ↦ AlexDisc.of (WithUpperSet X), map := WithUpperSet.map }
  unitIso := NatIso.ofComponents fun X ↦ AlexDisc.Iso.mk <| by
    dsimp; exact homeoWithUpperSetTopologyorderIso X
  counitIso := NatIso.ofComponents fun X ↦ Preord.Iso.mk <| by
    dsimp; exact (orderIsoSpecializationWithUpperSetTopology X).symm
