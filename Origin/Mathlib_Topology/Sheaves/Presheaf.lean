/-
Extracted from Topology/Sheaves/Presheaf.lean
Genuine: 22 | Conflates: 0 | Dissolved: 0 | Infrastructure: 10
-/
import Origin.Core
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.Topology.Sheaves.Init
import Mathlib.Data.Set.Subsingleton

/-!
# Presheaves on a topological space

We define `TopCat.Presheaf C X` simply as `(TopologicalSpace.Opens X)ᵒᵖ ⥤ C`,
and inherit the category structure with natural transformations as morphisms.

We define
* Given `{X Y : TopCat.{w}}` and `f : X ⟶ Y`, we define
`TopCat.Presheaf.pushforward C f : X.Presheaf C ⥤ Y.Presheaf C`,
with notation `f _* ℱ` for `ℱ : X.Presheaf C`.
and for `ℱ : X.Presheaf C` provide the natural isomorphisms
* `TopCat.Presheaf.Pushforward.id : (𝟙 X) _* ℱ ≅ ℱ`
* `TopCat.Presheaf.Pushforward.comp : (f ≫ g) _* ℱ ≅ g _* (f _* ℱ)`
along with their `@[simp]` lemmas.

We also define the functors `pullback C f : Y.Presheaf C ⥤ X.Presheaf c`,
and provide their adjunction at
`TopCat.Presheaf.pushforwardPullbackAdjunction`.
-/

universe w v u

open CategoryTheory TopologicalSpace Opposite

variable (C : Type u) [Category.{v} C]

namespace TopCat

def Presheaf (X : TopCat.{w}) : Type max u v w :=
  (Opens X)ᵒᵖ ⥤ C

instance (X : TopCat.{w}) : Category (Presheaf.{w, v, u} C X) :=
  inferInstanceAs (Category ((Opens X)ᵒᵖ ⥤ C : Type max u v w))

variable {C}

namespace Presheaf

@[simp] theorem comp_app {X : TopCat} {U : (Opens X)ᵒᵖ} {P Q R : Presheaf C X}
    (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).app U = f.app U ≫ g.app U := rfl

@[ext]
lemma ext {X : TopCat} {P Q : Presheaf C X} {f g : P ⟶ Q}
    (w : ∀ U : Opens X, f.app (op U) = g.app (op U)) :
    f = g := by
  apply NatTrans.ext
  ext U
  induction U with | _ U => ?_
  apply w

attribute [local instance] CategoryTheory.ConcreteCategory.hasCoeToSort
  CategoryTheory.ConcreteCategory.instFunLike

macro "sheaf_restrict" : attr =>

  `(attr|aesop safe 50 apply (rule_sets := [$(Lean.mkIdent `Restrict):ident]))

attribute [sheaf_restrict] bot_le le_top le_refl inf_le_left inf_le_right
  le_sup_left le_sup_right

macro (name := restrict_tac) "restrict_tac" c:Aesop.tactic_clause* : tactic =>

`(tactic| first | assumption |

  aesop $c*

    (config := { terminal := true

                 assumptionTransparency := .reducible

                 enableSimp := false })

    (rule_sets := [-default, -builtin, $(Lean.mkIdent `Restrict):ident]))

macro (name := restrict_tac?) "restrict_tac?" c:Aesop.tactic_clause* : tactic =>

`(tactic|

  aesop? $c*

    (config := { terminal := true

                 assumptionTransparency := .reducible

                 enableSimp := false

                 maxRuleApplications := 300 })

  (rule_sets := [-default, -builtin, $(Lean.mkIdent `Restrict):ident]))

attribute[aesop 10% (rule_sets := [Restrict])] le_trans

attribute[aesop safe destruct (rule_sets := [Restrict])] Eq.trans_le

attribute[aesop safe -50 (rule_sets := [Restrict])] Aesop.BuiltinRules.assumption

example {X} [CompleteLattice X] (v : Nat → X) (w x y z : X) (e : v 0 = v 1) (_ : v 1 = v 2)
    (h₀ : v 1 ≤ x) (_ : x ≤ z ⊓ w) (h₂ : x ≤ y ⊓ z) : v 0 ≤ y := by
  restrict_tac

def restrict {X : TopCat} {C : Type*} [Category C] [ConcreteCategory C] {F : X.Presheaf C}
    {V : Opens X} (x : F.obj (op V)) {U : Opens X} (h : U ⟶ V) : F.obj (op U) :=
  F.map h.op x

scoped[AlgebraicGeometry] infixl:80 " |_ₕ " => TopCat.Presheaf.restrict

scoped[AlgebraicGeometry] notation:80 x " |_ₗ " U " ⟪" e "⟫ " =>

  @TopCat.Presheaf.restrict _ _ _ _ _ _ x U (@homOfLE (Opens _) _ U _ e)

open AlgebraicGeometry

abbrev restrictOpen {X : TopCat} {C : Type*} [Category C] [ConcreteCategory C] {F : X.Presheaf C}
    {V : Opens X} (x : F.obj (op V)) (U : Opens X)
    (e : U ≤ V := by restrict_tac) :
    F.obj (op U) :=
  x |_ₗ U ⟪e⟫

scoped[AlgebraicGeometry] infixl:80 " |_ " => TopCat.Presheaf.restrictOpen

theorem restrict_restrict {X : TopCat} {C : Type*} [Category C] [ConcreteCategory C]
    {F : X.Presheaf C} {U V W : Opens X} (e₁ : U ≤ V) (e₂ : V ≤ W) (x : F.obj (op W)) :
    x |_ V |_ U = x |_ U := by
  delta restrictOpen restrict
  rw [← comp_apply, ← Functor.map_comp]
  rfl

theorem map_restrict {X : TopCat} {C : Type*} [Category C] [ConcreteCategory C]
    {F G : X.Presheaf C} (e : F ⟶ G) {U V : Opens X} (h : U ≤ V) (x : F.obj (op V)) :
    e.app _ (x |_ U) = e.app _ x |_ U := by
  delta restrictOpen restrict
  rw [← comp_apply, NatTrans.naturality, comp_apply]

open CategoryTheory.Limits

variable (C)

@[simps!]
def pushforward {X Y : TopCat.{w}} (f : X ⟶ Y) : X.Presheaf C ⥤ Y.Presheaf C :=
  (whiskeringLeft _ _ _).obj (Opens.map f).op

scoped[AlgebraicGeometry] notation f:80 " _* " P:81 =>

  Prefunctor.obj (Functor.toPrefunctor (TopCat.Presheaf.pushforward _ f)) P

@[simp]
theorem pushforward_map_app' {X Y : TopCat.{w}} (f : X ⟶ Y) {ℱ 𝒢 : X.Presheaf C} (α : ℱ ⟶ 𝒢)
    {U : (Opens Y)ᵒᵖ} : ((pushforward C f).map α).app U = α.app (op <| (Opens.map f).obj U.unop) :=
  rfl

lemma id_pushforward (X : TopCat.{w}) : pushforward C (𝟙 X) = 𝟭 (X.Presheaf C) := rfl

variable {C}

namespace Pushforward

def id {X : TopCat.{w}} (ℱ : X.Presheaf C) : 𝟙 X _* ℱ ≅ ℱ := Iso.refl _

@[simp]
theorem id_hom_app {X : TopCat.{w}} (ℱ : X.Presheaf C) (U) : (id ℱ).hom.app U = 𝟙 _ := rfl

@[simp]
theorem id_inv_app {X : TopCat.{w}} (ℱ : X.Presheaf C) (U) :
    (id ℱ).inv.app U = 𝟙 _ := rfl

theorem id_eq {X : TopCat.{w}} (ℱ : X.Presheaf C) : 𝟙 X _* ℱ = ℱ := rfl

def comp {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf C) :
    (f ≫ g) _* ℱ ≅ g _* (f _* ℱ) := Iso.refl _

theorem comp_eq {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf C) :
    (f ≫ g) _* ℱ = g _* (f _* ℱ) :=
  rfl

@[simp]
theorem comp_hom_app {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf C) (U) :
    (comp f g ℱ).hom.app U = 𝟙 _ := rfl

@[simp]
theorem comp_inv_app {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf C) (U) :
    (comp f g ℱ).inv.app U = 𝟙 _ := rfl

end Pushforward

def pushforwardEq {X Y : TopCat.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.Presheaf C) :
    f _* ℱ ≅ g _* ℱ :=
  isoWhiskerRight (NatIso.op (Opens.mapIso f g h).symm) ℱ

theorem pushforward_eq' {X Y : TopCat.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.Presheaf C) :
    f _* ℱ = g _* ℱ := by rw [h]

@[simp]
theorem pushforwardEq_hom_app {X Y : TopCat.{w}} {f g : X ⟶ Y}
    (h : f = g) (ℱ : X.Presheaf C) (U) :
    (pushforwardEq h ℱ).hom.app U = ℱ.map (eqToHom (by aesop_cat)) := by
  simp [pushforwardEq]

variable (C)

section Iso

@[simps!]
def presheafEquivOfIso {X Y : TopCat} (H : X ≅ Y) : X.Presheaf C ≌ Y.Presheaf C :=
  Equivalence.congrLeft (Opens.mapMapIso H).symm.op

variable {C}

def toPushforwardOfIso {X Y : TopCat} (H : X ≅ Y) {ℱ : X.Presheaf C} {𝒢 : Y.Presheaf C}
    (α : H.hom _* ℱ ⟶ 𝒢) : ℱ ⟶ H.inv _* 𝒢 :=
  (presheafEquivOfIso _ H).toAdjunction.homEquiv ℱ 𝒢 α

@[simp]
theorem toPushforwardOfIso_app {X Y : TopCat} (H₁ : X ≅ Y) {ℱ : X.Presheaf C} {𝒢 : Y.Presheaf C}
    (H₂ : H₁.hom _* ℱ ⟶ 𝒢) (U : (Opens X)ᵒᵖ) :
    (toPushforwardOfIso H₁ H₂).app U =
      ℱ.map (eqToHom (by simp [Opens.map, Set.preimage_preimage])) ≫
        H₂.app (op ((Opens.map H₁.inv).obj (unop U))) := by
  simp [toPushforwardOfIso, Adjunction.homEquiv_unit]

def pushforwardToOfIso {X Y : TopCat} (H₁ : X ≅ Y) {ℱ : Y.Presheaf C} {𝒢 : X.Presheaf C}
    (H₂ : ℱ ⟶ H₁.hom _* 𝒢) : H₁.inv _* ℱ ⟶ 𝒢 :=
  ((presheafEquivOfIso _ H₁.symm).toAdjunction.homEquiv ℱ 𝒢).symm H₂

@[simp]
theorem pushforwardToOfIso_app {X Y : TopCat} (H₁ : X ≅ Y) {ℱ : Y.Presheaf C} {𝒢 : X.Presheaf C}
    (H₂ : ℱ ⟶ H₁.hom _* 𝒢) (U : (Opens X)ᵒᵖ) :
    (pushforwardToOfIso H₁ H₂).app U =
      H₂.app (op ((Opens.map H₁.inv).obj (unop U))) ≫
        𝒢.map (eqToHom (by simp [Opens.map, Set.preimage_preimage])) := by
  simp [pushforwardToOfIso, Equivalence.toAdjunction, Adjunction.homEquiv_counit]

end Iso

variable [HasColimits C]

noncomputable section

def pullback {X Y : TopCat.{v}} (f : X ⟶ Y) : Y.Presheaf C ⥤ X.Presheaf C :=
  (Opens.map f).op.lan

def pushforwardPullbackAdjunction {X Y : TopCat.{v}} (f : X ⟶ Y) :
    pullback C f ⊣ pushforward C f :=
  Functor.lanAdjunction _ _

def pullbackHomIsoPushforwardInv {X Y : TopCat.{v}} (H : X ≅ Y) :
    pullback C H.hom ≅ pushforward C H.inv :=
  Adjunction.leftAdjointUniq (pushforwardPullbackAdjunction C H.hom)
    (presheafEquivOfIso C H.symm).toAdjunction

def pullbackInvIsoPushforwardHom {X Y : TopCat.{v}} (H : X ≅ Y) :
    pullback C H.inv ≅ pushforward C H.hom :=
  Adjunction.leftAdjointUniq (pushforwardPullbackAdjunction C H.inv)
    (presheafEquivOfIso C H).toAdjunction

variable {C}

def pullbackObjObjOfImageOpen {X Y : TopCat.{v}} (f : X ⟶ Y) (ℱ : Y.Presheaf C) (U : Opens X)
    (H : IsOpen (f '' SetLike.coe U)) : ((pullback C f).obj ℱ).obj (op U) ≅ ℱ.obj (op ⟨_, H⟩) := by
  let x : CostructuredArrow (Opens.map f).op (op U) := CostructuredArrow.mk
    (@homOfLE _ _ _ ((Opens.map f).obj ⟨_, H⟩) (Set.image_preimage.le_u_l _)).op
  have hx : IsTerminal x :=
    { lift := fun s ↦ by
        fapply CostructuredArrow.homMk
        · change op (unop _) ⟶ op (⟨_, H⟩ : Opens _)
          refine (homOfLE ?_).op
          apply (Set.image_subset f s.pt.hom.unop.le).trans
          exact Set.image_preimage.l_u_le (SetLike.coe s.pt.left.unop)
        · simp [eq_iff_true_of_subsingleton] }
  exact IsColimit.coconePointUniqueUpToIso
    ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit ℱ (op U))
    (colimitOfDiagramTerminal hx _)

end

end Presheaf

end TopCat
