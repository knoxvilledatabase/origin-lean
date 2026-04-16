/-
Extracted from Topology/Category/Sequential.lean
Genuine: 7 | Conflates: 0 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core
import Mathlib.CategoryTheory.Elementwise
import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Category.TopCat.Basic

noncomputable section

/-!

# The category of sequential topological spaces

We define the category `Sequential` of sequential topological spaces. We follow the usual template
for defining categories of topological spaces, by giving it the induced category structure from
`TopCat`.
-/

open CategoryTheory

attribute [local instance] ConcreteCategory.instFunLike

universe u

structure Sequential where
  /-- The underlying topological space of an object of `Sequential`. -/
  toTop : TopCat.{u}
  /-- The underlying topological space is sequential. -/
  [is_sequential : SequentialSpace toTop]

namespace Sequential

instance : Inhabited Sequential.{u} :=
  ⟨{ toTop := { α := ULift (Fin 37) } }⟩

instance : CoeSort Sequential Type* :=
  ⟨fun X => X.toTop⟩

attribute [instance] is_sequential

instance : Category.{u, u+1} Sequential.{u} :=
  InducedCategory.category toTop

instance : ConcreteCategory.{u} Sequential.{u} :=
  InducedCategory.concreteCategory _

variable (X : Type u) [TopologicalSpace X] [SequentialSpace X]

def of : Sequential.{u} where
  toTop := TopCat.of X
  is_sequential := ‹_›

@[simps!]
def sequentialToTop : Sequential.{u} ⥤ TopCat.{u} :=
  inducedFunctor _

def fullyFaithfulSequentialToTop : sequentialToTop.FullyFaithful :=
  fullyFaithfulInducedFunctor _

instance : sequentialToTop.{u}.Full  :=
  inferInstanceAs (inducedFunctor _).Full

instance : sequentialToTop.{u}.Faithful :=
  inferInstanceAs (inducedFunctor _).Faithful

@[simps hom inv]
def isoOfHomeo {X Y : Sequential.{u}} (f : X ≃ₜ Y) : X ≅ Y where
  hom := ⟨f, f.continuous⟩
  inv := ⟨f.symm, f.symm.continuous⟩
  hom_inv_id := by
    ext x
    exact f.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact f.apply_symm_apply x

@[simps]
def homeoOfIso {X Y : Sequential.{u}} (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.hom
  invFun := f.inv
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := f.hom.continuous
  continuous_invFun := f.inv.continuous

@[simps]
def isoEquivHomeo {X Y : Sequential.{u}} : (X ≅ Y) ≃ (X ≃ₜ Y) where
  toFun := homeoOfIso
  invFun := isoOfHomeo
  left_inv f := by
    ext
    rfl
  right_inv f := by
    ext
    rfl

end Sequential
