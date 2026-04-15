/-
Extracted from Topology/Category/Stonean/Adjunctions.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Topology.Category.Stonean.Basic
import Mathlib.Topology.Category.TopCat.Adjunctions
import Mathlib.Topology.StoneCech

/-!
# Adjunctions involving the category of Stonean spaces

This file constructs the left adjoint `typeToStonean` to the forgetful functor from Stonean spaces
to sets, using the Stone-Cech compactification. This allows to conclude that the monomorphisms in
`Stonean` are precisely the injective maps (see `Stonean.mono_iff_injective`).
-/

universe u

open CategoryTheory Adjunction

namespace Stonean

def stoneCechObj (X : Type u) : Stonean :=
  letI : TopologicalSpace X := ⊥
  haveI : DiscreteTopology X := ⟨rfl⟩
  haveI : ExtremallyDisconnected (StoneCech X) :=
    CompactT2.Projective.extremallyDisconnected StoneCech.projective
  of (StoneCech X)

noncomputable def stoneCechEquivalence (X : Type u) (Y : Stonean.{u}) :
    (stoneCechObj X ⟶ Y) ≃ (X ⟶ (forget Stonean).obj Y) := by
  letI : TopologicalSpace X := ⊥
  haveI : DiscreteTopology X := ⟨rfl⟩
  refine fullyFaithfulToCompHaus.homEquiv.trans ?_
  exact (_root_.stoneCechEquivalence (TopCat.of X) (toCompHaus.obj Y)).trans
    (TopCat.adj₁.homEquiv _ _)

end Stonean

noncomputable def typeToStonean : Type u ⥤ Stonean.{u} :=
  leftAdjointOfEquiv Stonean.stoneCechEquivalence fun _ _ _ _ _ => rfl

namespace Stonean

noncomputable def stoneCechAdjunction : typeToStonean ⊣ (forget Stonean) :=
  adjunctionOfEquivLeft stoneCechEquivalence fun _ _ _ _ _ => rfl

noncomputable instance forget.preservesLimits : Limits.PreservesLimits (forget Stonean) :=
  rightAdjoint_preservesLimits stoneCechAdjunction

end Stonean
