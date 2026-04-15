/-
Extracted from Topology/Sheaves/Sheaf.lean
Genuine: 8 of 13 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Sheaves

We define sheaves on a topological space, with values in an arbitrary category.

A presheaf on a topological space `X` is a sheaf precisely when it is a sheaf under the
Grothendieck topology on `opens X`, which expands out to say: For each open cover `{ Uᵢ }` of
`U`, and a family of compatible functions `A ⟶ F(Uᵢ)` for an `A : X`, there exists a unique
gluing `A ⟶ F(U)` compatible with the restriction.

See the docstring of `TopCat.Presheaf.IsSheaf` for an explanation on the design decisions and a list
of equivalent conditions.

We provide the instance `CategoryTheory.Category (TopCat.Sheaf C X)` as the full subcategory of
presheaves, and the fully faithful functor `Sheaf.forget : TopCat.Sheaf C X ⥤ TopCat.Presheaf C X`.

-/

universe w v u

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopologicalSpace.Opens

namespace TopCat

variable {C : Type u} [Category.{v} C]

variable {X : TopCat.{w}} (F : Presheaf C X) {ι : Type v} (U : ι → Opens X)

namespace Presheaf

nonrec def IsSheaf (F : Presheaf.{w, v, u} C X) : Prop :=
  Presheaf.IsSheaf (Opens.grothendieckTopology X) F

theorem isSheaf_unit (F : Presheaf (CategoryTheory.Discrete Unit) X) : F.IsSheaf :=
  fun x U S _ x _ => ⟨eqToHom (Subsingleton.elim _ _), by cat_disch, fun _ => by cat_disch⟩

theorem isSheaf_iso_iff {F G : Presheaf C X} (α : F ≅ G) : F.IsSheaf ↔ G.IsSheaf :=
  Presheaf.isSheaf_of_iso_iff α

theorem isSheaf_of_iso {F G : Presheaf C X} (α : F ≅ G) (h : F.IsSheaf) : G.IsSheaf :=
  (isSheaf_iso_iff α).1 h

end Presheaf

variable (C X)

nonrec def Sheaf : Type max u v w :=
  Sheaf (Opens.grothendieckTopology X) C

deriving Category

variable {C X}

abbrev Sheaf.presheaf (F : X.Sheaf C) : TopCat.Presheaf C X :=
  F.1

variable (C X)

-- INSTANCE (free from Core): sheafInhabited

namespace Sheaf

def forget : TopCat.Sheaf C X ⥤ TopCat.Presheaf C X :=
  sheafToPresheaf _ _

-- INSTANCE (free from Core): forget_full

-- INSTANCE (free from Core): forgetFaithful

end Sheaf

lemma Presheaf.IsSheaf.section_ext {X : TopCat.{u}}
    {A : Type*} [Category.{u} A] {FC : A → A → Type*} {CC : A → Type u}
    [∀ X Y : A, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{u} A FC]
    [HasLimits A] [PreservesLimits (forget A)] [(forget A).ReflectsIsomorphisms]
    {F : TopCat.Presheaf A X} (hF : TopCat.Presheaf.IsSheaf F)
    {U : (Opens X)ᵒᵖ} {s t : ToType (F.obj U)}
    (hst : ∀ x ∈ U.unop, ∃ V, ∃ hV : V ≤ U.unop, x ∈ V ∧
      F.map (homOfLE hV).op s = F.map (homOfLE hV).op t) :
    s = t := by
  have := (isSheaf_iff_isSheaf_of_type _ _).mp
    ((Presheaf.isSheaf_iff_isSheaf_forget (C := Opens X) (A' := A) _ F (forget _)).mp hF)
  choose V hV hxV H using fun x : U.unop ↦ hst x.1 x.2
  refine (this.isSheafFor (.ofArrows V fun x ↦ homOfLE (hV x)) ?_).isSeparatedFor.ext ?_
  · exact fun x hx ↦ ⟨V ⟨x, hx⟩, homOfLE (hV _), Sieve.ofArrows_mk _ _ _, hxV _⟩
  · rintro _ _ ⟨x⟩; exact H x

end TopCat
