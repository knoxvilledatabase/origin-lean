/-
Extracted from Algebra/Category/Grp/FilteredColimits.lean
Genuine: 11 of 20 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.MonCat.FilteredColimits

/-!
# The forgetful functor from (commutative) (additive) groups preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a small filtered category `J` and a functor `F : J ⥤ Grp`.
We show that the colimit of `F ⋙ forget₂ Grp MonCat` (in `MonCat`) carries the structure of a
group,
thereby showing that the forgetful functor `forget₂ Grp MonCat` preserves filtered colimits.
In particular, this implies that `forget Grp` preserves filtered colimits.
Similarly for `AddGrp`, `CommGrp` and `AddCommGrp`.

-/

universe v u

noncomputable section

open CategoryTheory Limits

open IsFiltered renaming max → max' -- avoid name collision with `_root_.max`.

namespace Grp.FilteredColimits

section

open MonCat.FilteredColimits (colimit_one_eq colimit_mul_mk_eq)

variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ Grp.{max v u})

@[to_additive
  "The colimit of `F ⋙ forget₂ AddGrp AddMonCat` in the category `AddMonCat`.
  In the following, we will show that this has the structure of an additive group."]
noncomputable abbrev G : MonCat :=
  MonCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ Grp MonCat.{max v u})

@[to_additive "The canonical projection into the colimit, as a quotient type."]
abbrev G.mk : (Σ j, F.obj j) → G.{v, u} F :=
  Quot.mk (Types.Quot.Rel (F ⋙ forget Grp.{max v u}))

@[to_additive]
theorem G.mk_eq (x y : Σ j, F.obj j)
    (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) :
    G.mk.{v, u} F x = G.mk F y :=
  Quot.eqvGen_sound (Types.FilteredColimit.eqvGen_quot_rel_of_rel (F ⋙ forget Grp) x y h)

@[to_additive "The \"unlifted\" version of negation in the colimit."]
def colimitInvAux (x : Σ j, F.obj j) : G.{v, u} F :=
  G.mk F ⟨x.1, x.2⁻¹⟩

@[to_additive]
theorem colimitInvAux_eq_of_rel (x y : Σ j, F.obj j)
    (h : Types.FilteredColimit.Rel (F ⋙ forget Grp) x y) :
    colimitInvAux.{v, u} F x = colimitInvAux F y := by
  apply G.mk_eq
  obtain ⟨k, f, g, hfg⟩ := h
  use k, f, g
  rw [MonoidHom.map_inv, MonoidHom.map_inv, inv_inj]
  exact hfg

@[to_additive "Negation in the colimit. See also `colimitNegAux`."]
instance colimitInv : Inv (G.{v, u} F) where
  inv x := by
    refine Quot.lift (colimitInvAux.{v, u} F) ?_ x
    intro x y h
    apply colimitInvAux_eq_of_rel
    apply Types.FilteredColimit.rel_of_quot_rel
    exact h

@[to_additive (attr := simp)]
theorem colimit_inv_mk_eq (x : Σ j, F.obj j) : (G.mk.{v, u} F x)⁻¹ = G.mk F ⟨x.1, x.2⁻¹⟩ :=
  rfl

@[to_additive]
noncomputable instance colimitGroup : Group (G.{v, u} F) :=
  { colimitInv.{v, u} F, (G.{v, u} F).str with
    inv_mul_cancel := fun x => by
      refine Quot.inductionOn x ?_; clear x; intro x
      obtain ⟨j, x⟩ := x
      erw [colimit_inv_mk_eq,
        colimit_mul_mk_eq (F ⋙ forget₂ Grp MonCat.{max v u}) ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j),
        colimit_one_eq (F ⋙ forget₂ Grp MonCat.{max v u}) j]
      dsimp
      erw [CategoryTheory.Functor.map_id, inv_mul_cancel] }

@[to_additive "The bundled additive group giving the filtered colimit of a diagram."]
noncomputable def colimit : Grp.{max v u} :=
  Grp.of (G.{v, u} F)

@[to_additive "The cocone over the proposed colimit additive group."]
noncomputable def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι := { (MonCat.FilteredColimits.colimitCocone (F ⋙ forget₂ Grp MonCat.{max v u})).ι with }

@[to_additive "The proposed colimit cocone is a colimit in `AddGroup`."]
def colimitCoconeIsColimit : IsColimit (colimitCocone.{v, u} F) where
  desc t :=
    MonCat.FilteredColimits.colimitDesc.{v, u} (F ⋙ forget₂ Grp MonCat.{max v u})
      ((forget₂ Grp MonCat).mapCocone t)
  fac t j :=
    DFunLike.coe_injective <|
      (Types.TypeMax.colimitCoconeIsColimit.{v, u} (F ⋙ forget Grp)).fac
      ((forget Grp).mapCocone t) j
  uniq t _ h :=
    DFunLike.coe_injective' <|
      (Types.TypeMax.colimitCoconeIsColimit.{v, u} (F ⋙ forget Grp)).uniq
      ((forget Grp).mapCocone t) _
        fun j => funext fun x => DFunLike.congr_fun (h j) x

@[to_additive forget₂AddMon_preservesFilteredColimits]
noncomputable instance forget₂Mon_preservesFilteredColimits :
    PreservesFilteredColimits.{u} (forget₂ Grp.{u} MonCat.{u}) where
      preserves_filtered_colimits x hx1 _ :=
      letI : Category.{u, u} x := hx1
      ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (MonCat.FilteredColimits.colimitCoconeIsColimit.{u, u} _)⟩

@[to_additive]
noncomputable instance forget_preservesFilteredColimits :
    PreservesFilteredColimits (forget Grp.{u}) :=
  Limits.comp_preservesFilteredColimits (forget₂ Grp MonCat) (forget MonCat.{u})

end

end Grp.FilteredColimits

namespace CommGrp.FilteredColimits

section

variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ CommGrp.{max v u})

@[to_additive
  "The colimit of `F ⋙ forget₂ AddCommGrp AddGrp` in the category `AddGrp`.
  In the following, we will show that this has the structure of a _commutative_ additive group."]
noncomputable abbrev G : Grp.{max v u} :=
  Grp.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ CommGrp.{max v u} Grp.{max v u})

@[to_additive]
noncomputable instance colimitCommGroup : CommGroup.{max v u} (G.{v, u} F) :=
  { (G F).str,
    CommMonCat.FilteredColimits.colimitCommMonoid
      (F ⋙ forget₂ CommGrp CommMonCat.{max v u}) with }

@[to_additive "The bundled additive commutative group giving the filtered colimit of a diagram."]
noncomputable def colimit : CommGrp :=
  CommGrp.of (G.{v, u} F)

@[to_additive "The cocone over the proposed colimit additive commutative group."]
noncomputable def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι :=
    { (Grp.FilteredColimits.colimitCocone
          (F ⋙ forget₂ CommGrp Grp.{max v u})).ι with }

@[to_additive "The proposed colimit cocone is a colimit in `AddCommGroup`."]
def colimitCoconeIsColimit : IsColimit (colimitCocone.{v, u} F) where
  desc t :=
    (Grp.FilteredColimits.colimitCoconeIsColimit.{v, u}
          (F ⋙ forget₂ CommGrp Grp.{max v u})).desc
      ((forget₂ CommGrp Grp.{max v u}).mapCocone t)
  fac t j :=
    DFunLike.coe_injective <|
      (Types.TypeMax.colimitCoconeIsColimit.{v, u} (F ⋙ forget CommGrp)).fac
        ((forget CommGrp).mapCocone t) j
  uniq t _ h :=
    DFunLike.coe_injective <|
      (Types.TypeMax.colimitCoconeIsColimit.{v, u} (F ⋙ forget CommGrp)).uniq
        ((forget CommGrp).mapCocone t) _ fun j => funext fun x => DFunLike.congr_fun (h j) x

@[to_additive]
noncomputable instance forget₂Group_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ CommGrp Grp.{u}) where
  preserves_filtered_colimits J hJ1 _ :=
    letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (Grp.FilteredColimits.colimitCoconeIsColimit.{u, u}
            (F ⋙ forget₂ CommGrp Grp.{u})) }

@[to_additive]
noncomputable instance forget_preservesFilteredColimits :
    PreservesFilteredColimits (forget CommGrp.{u}) :=
  Limits.comp_preservesFilteredColimits (forget₂ CommGrp Grp) (forget Grp.{u})

end

end CommGrp.FilteredColimits
