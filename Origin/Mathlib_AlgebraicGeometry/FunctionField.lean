/-
Extracted from AlgebraicGeometry/FunctionField.lean
Genuine: 5 of 10 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Function field of integral schemes

We define the function field of an irreducible scheme as the stalk of the generic point.
This is a field when the scheme is integral.

## Main definition
* `AlgebraicGeometry.Scheme.functionField`: The function field of an integral scheme.
* `AlgebraicGeometry.Scheme.germToFunctionField`: The canonical map from a component into the
  function field. This map is injective.
-/

universe u v

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits TopCat

namespace AlgebraicGeometry

variable (X : Scheme)

noncomputable abbrev Scheme.functionField [IrreducibleSpace X] : CommRingCat :=
  X.presheaf.stalk (genericPoint X)

noncomputable abbrev Scheme.germToFunctionField [IrreducibleSpace X] (U : X.Opens)
    [h : Nonempty U] : Γ(X, U) ⟶ X.functionField :=
  X.presheaf.germ U
    (genericPoint X)
      (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using h))

-- INSTANCE (free from Core): [IrreducibleSpace

-- INSTANCE (free from Core): [IsIntegral

theorem germ_injective_of_isIntegral [IsIntegral X] {U : X.Opens} (x : X) (hx : x ∈ U) :
    Function.Injective (X.presheaf.germ U x hx) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  rw [← (X.presheaf.germ U x hx).hom.map_zero] at hy
  obtain ⟨W, hW, iU, iV, e⟩ := X.presheaf.germ_eq _ hx hx _ _ hy
  cases Subsingleton.elim iU iV
  haveI : Nonempty W := ⟨⟨_, hW⟩⟩
  exact map_injective_of_isIntegral X iU e

theorem Scheme.germToFunctionField_injective [IsIntegral X] (U : X.Opens) [Nonempty U] :
    Function.Injective (X.germToFunctionField U) :=
  germ_injective_of_isIntegral _ _ _

theorem genericPoint_eq_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    [hX : IrreducibleSpace X] [IrreducibleSpace Y] :
    f (genericPoint X) = genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  convert (genericPoint_spec X).image f.continuous
  symm
  rw [← Set.univ_subset_iff]
  convert subset_closure_inter_of_isPreirreducible_of_isOpen _ f.isOpenEmbedding.isOpen_range _
  · rw [Set.univ_inter, Set.image_univ]
  · apply PreirreducibleSpace.isPreirreducible_univ (X := Y)
  · exact ⟨_, trivial, Set.mem_range_self hX.2.some⟩

-- INSTANCE (free from Core): stalkFunctionFieldAlgebra

-- INSTANCE (free from Core): functionField_isScalarTower

-- INSTANCE (free from Core): (R

set_option backward.isDefEq.respectTransparency false in
