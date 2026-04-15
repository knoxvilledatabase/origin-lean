/-
Extracted from Topology/Category/TopCat/OpenNhds.lean
Genuine: 11 of 25 | Dissolved: 0 | Infrastructure: 14
-/
import Origin.Core
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Data.Set.Subsingleton

/-!
# The category of open neighborhoods of a point

Given an object `X` of the category `TopCat` of topological spaces and a point `x : X`, this file
builds the type `OpenNhds x` of open neighborhoods of `x` in `X` and endows it with the partial
order given by inclusion and the corresponding category structure (as a full subcategory of the
poset category `Set X`). This is used in `Topology.Sheaves.Stalks` to build the stalk of a sheaf
at `x` as a limit over `OpenNhds x`.

## Main declarations

Besides `OpenNhds`, the main constructions here are:

* `inclusion (x : X)`: the obvious functor `OpenNhds x ⥤ Opens X`
* `functorNhds`: An open map `f : X ⟶ Y` induces a functor `OpenNhds x ⥤ OpenNhds (f x)`
* `adjunctionNhds`: An open map `f : X ⟶ Y` induces an adjunction between `OpenNhds x` and
                    `OpenNhds (f x)`.
-/

open CategoryTheory TopologicalSpace Opposite Topology

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

namespace TopologicalSpace

def OpenNhds (x : X) :=
  FullSubcategory fun U : Opens X => x ∈ U

namespace OpenNhds

instance partialOrder (x : X) : PartialOrder (OpenNhds x) where
  le U V := U.1 ≤ V.1
  le_refl _ := by dsimp [LE.le]; exact le_rfl
  le_trans _ _ _ := by dsimp [LE.le]; exact le_trans
  le_antisymm _ _ i j := FullSubcategory.ext <| le_antisymm i j

instance (x : X) : Lattice (OpenNhds x) :=
  { OpenNhds.partialOrder x with
    inf := fun U V => ⟨U.1 ⊓ V.1, ⟨U.2, V.2⟩⟩
    le_inf := fun U V W => @le_inf _ _ U.1.1 V.1.1 W.1.1
    inf_le_left := fun U V => @inf_le_left _ _ U.1.1 V.1.1
    inf_le_right := fun U V => @inf_le_right _ _ U.1.1 V.1.1
    sup := fun U V => ⟨U.1 ⊔ V.1, Set.mem_union_left V.1.1 U.2⟩
    sup_le := fun U V W => @sup_le _ _ U.1.1 V.1.1 W.1.1
    le_sup_left := fun U V => @le_sup_left _ _ U.1.1 V.1.1
    le_sup_right := fun U V => @le_sup_right _ _ U.1.1 V.1.1 }

instance (x : X) : OrderTop (OpenNhds x) where
  top := ⟨⊤, trivial⟩
  le_top _ := by dsimp [LE.le]; exact le_top

instance (x : X) : Inhabited (OpenNhds x) :=
  ⟨⊤⟩

instance openNhdsCategory (x : X) : Category.{u} (OpenNhds x) := inferInstance

instance opensNhdsHomHasCoeToFun {x : X} {U V : OpenNhds x} : CoeFun (U ⟶ V) fun _ => U.1 → V.1 :=
  ⟨fun f x => ⟨x, f.le x.2⟩⟩

def infLELeft {x : X} (U V : OpenNhds x) : U ⊓ V ⟶ U :=
  homOfLE inf_le_left

def infLERight {x : X} (U V : OpenNhds x) : U ⊓ V ⟶ V :=
  homOfLE inf_le_right

def inclusion (x : X) : OpenNhds x ⥤ Opens X :=
  fullSubcategoryInclusion _

@[simp]
theorem inclusion_obj (x : X) (U) (p) : (inclusion x).obj ⟨U, p⟩ = U :=
  rfl

theorem isOpenEmbedding {x : X} (U : OpenNhds x) : IsOpenEmbedding U.1.inclusion' :=
  U.1.isOpenEmbedding

alias openEmbedding := isOpenEmbedding

def map (x : X) : OpenNhds (f x) ⥤ OpenNhds x where
  obj U := ⟨(Opens.map f).obj U.1, U.2⟩
  map i := (Opens.map f).map i

@[simp]
theorem map_obj (x : X) (U) (q) : (map f x).obj ⟨U, q⟩ = ⟨(Opens.map f).obj U, q⟩ :=
  rfl

@[simp]
theorem map_id_obj (x : X) (U) : (map (𝟙 X) x).obj U = U := rfl

@[simp]
theorem map_id_obj' (x : X) (U) (p) (q) : (map (𝟙 X) x).obj ⟨⟨U, p⟩, q⟩ = ⟨⟨U, p⟩, q⟩ :=
  rfl

@[simp]
theorem map_id_obj_unop (x : X) (U : (OpenNhds x)ᵒᵖ) : (map (𝟙 X) x).obj (unop U) = unop U := by
  simp

@[simp]
theorem op_map_id_obj (x : X) (U : (OpenNhds x)ᵒᵖ) : (map (𝟙 X) x).op.obj U = U := by simp

@[simps! hom_app inv_app]
def inclusionMapIso (x : X) : inclusion (f x) ⋙ Opens.map f ≅ map f x ⋙ inclusion x :=
  NatIso.ofComponents fun U => { hom := 𝟙 _, inv := 𝟙 _ }

@[simp]
theorem inclusionMapIso_hom (x : X) : (inclusionMapIso f x).hom = 𝟙 _ :=
  rfl

@[simp]
theorem inclusionMapIso_inv (x : X) : (inclusionMapIso f x).inv = 𝟙 _ :=
  rfl

end OpenNhds

end TopologicalSpace

namespace IsOpenMap

open TopologicalSpace

variable {f}

@[simps]
def functorNhds (h : IsOpenMap f) (x : X) : OpenNhds x ⥤ OpenNhds (f x) where
  obj U := ⟨h.functor.obj U.1, ⟨x, U.2, rfl⟩⟩
  map i := h.functor.map i

def adjunctionNhds (h : IsOpenMap f) (x : X) : IsOpenMap.functorNhds h x ⊣ OpenNhds.map f x where
  unit := { app := fun _ => homOfLE fun x hxU => ⟨x, hxU, rfl⟩ }
  counit := { app := fun _ => homOfLE fun _ ⟨_, hfxV, hxy⟩ => hxy ▸ hfxV }

end IsOpenMap

namespace Topology.IsInducing

open TopologicalSpace

variable {f}

@[simps]
def functorNhds (h : IsInducing f) (x : X) :
    OpenNhds x ⥤ OpenNhds (f x) where
  obj U := ⟨h.functor.obj U.1, (h.mem_functorObj_iff U.1).mpr U.2⟩
  map := h.functor.map

def adjunctionNhds (h : IsInducing f) (x : X) :
    OpenNhds.map f x ⊣ h.functorNhds x where
  unit := { app := fun U => homOfLE (h.adjunction.unit.app U.1).le }
  counit := { app := fun U => homOfLE (h.adjunction.counit.app U.1).le }

end Topology.IsInducing
