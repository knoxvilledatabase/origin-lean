/-
Extracted from CategoryTheory/IsConnected.lean
Genuine: 53 | Conflates: 0 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core
import Mathlib.Data.List.Chain
import Mathlib.CategoryTheory.PUnit
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Category.ULift

noncomputable section

/-!
# Connected category

Define a connected category as a _nonempty_ category for which every functor
to a discrete category is isomorphic to the constant functor.

NB. Some authors include the empty category as connected, we do not.
We instead are interested in categories with exactly one 'connected
component'.

We give some equivalent definitions:
- A nonempty category for which every functor to a discrete category is
  constant on objects.
  See `any_functor_const_on_obj` and `Connected.of_any_functor_const_on_obj`.
- A nonempty category for which every function `F` for which the presence of a
  morphism `f : j₁ ⟶ j₂` implies `F j₁ = F j₂` must be constant everywhere.
  See `constant_of_preserves_morphisms` and `Connected.of_constant_of_preserves_morphisms`.
- A nonempty category for which any subset of its elements containing the
  default and closed under morphisms is everything.
  See `induct_on_objects` and `Connected.of_induct`.
- A nonempty category for which every object is related under the reflexive
  transitive closure of the relation "there is a morphism in some direction
  from `j₁` to `j₂`".
  See `connected_zigzag` and `zigzag_connected`.
- A nonempty category for which for any two objects there is a sequence of
  morphisms (some reversed) from one to the other.
  See `exists_zigzag'` and `connected_of_zigzag`.

We also prove the result that the functor given by `(X × -)` preserves any
connected limit. That is, any limit of shape `J` where `J` is a connected
category is preserved by the functor `(X × -)`. This appears in `CategoryTheory.Limits.Connected`.
-/

universe w₁ w₂ v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory.Category

open Opposite

namespace CategoryTheory

class IsPreconnected (J : Type u₁) [Category.{v₁} J] : Prop where
  iso_constant :
    ∀ {α : Type u₁} (F : J ⥤ Discrete α) (j : J), Nonempty (F ≅ (Functor.const J).obj (F.obj j))

attribute [inherit_doc IsPreconnected] IsPreconnected.iso_constant

class IsConnected (J : Type u₁) [Category.{v₁} J] extends IsPreconnected J : Prop where
  [is_nonempty : Nonempty J]

attribute [instance 100] IsConnected.is_nonempty

variable {J : Type u₁} [Category.{v₁} J]

variable {K : Type u₂} [Category.{v₂} K]

namespace IsPreconnected.IsoConstantAux

private def liftToDiscrete {α : Type u₂} (F : J ⥤ Discrete α) : J ⥤ Discrete J where
  obj j := have := Nonempty.intro j
    Discrete.mk (Function.invFun F.obj (F.obj j))
  map {j _} f := have := Nonempty.intro j
    ⟨⟨congr_arg (Function.invFun F.obj) (Discrete.ext (Discrete.eq_of_hom (F.map f)))⟩⟩

private def factorThroughDiscrete {α : Type u₂} (F : J ⥤ Discrete α) :
    liftToDiscrete F ⋙ Discrete.functor F.obj ≅ F :=
  NatIso.ofComponents (fun _ => eqToIso Function.apply_invFun_apply) (by aesop_cat)

end IsPreconnected.IsoConstantAux

def isoConstant [IsPreconnected J] {α : Type u₂} (F : J ⥤ Discrete α) (j : J) :
    F ≅ (Functor.const J).obj (F.obj j) :=
  (IsPreconnected.IsoConstantAux.factorThroughDiscrete F).symm
    ≪≫ isoWhiskerRight (IsPreconnected.iso_constant _ j).some _
    ≪≫ NatIso.ofComponents (fun _ => eqToIso Function.apply_invFun_apply) (by aesop_cat)

theorem any_functor_const_on_obj [IsPreconnected J] {α : Type u₂} (F : J ⥤ Discrete α) (j j' : J) :
    F.obj j = F.obj j' := by
  ext; exact ((isoConstant F j').hom.app j).down.1

theorem IsPreconnected.of_any_functor_const_on_obj
    (h : ∀ {α : Type u₁} (F : J ⥤ Discrete α), ∀ j j' : J, F.obj j = F.obj j') :
    IsPreconnected J where
  iso_constant := fun F j' => ⟨NatIso.ofComponents fun j => eqToIso (h F j j')⟩

theorem IsConnected.of_any_functor_const_on_obj [Nonempty J]
    (h : ∀ {α : Type u₁} (F : J ⥤ Discrete α), ∀ j j' : J, F.obj j = F.obj j') : IsConnected J :=
  { IsPreconnected.of_any_functor_const_on_obj h with }

theorem constant_of_preserves_morphisms [IsPreconnected J] {α : Type u₂} (F : J → α)
    (h : ∀ (j₁ j₂ : J) (_ : j₁ ⟶ j₂), F j₁ = F j₂) (j j' : J) : F j = F j' := by
  simpa using
    any_functor_const_on_obj
      { obj := Discrete.mk ∘ F
        map := fun f => eqToHom (by ext; exact h _ _ f) }
      j j'

theorem IsPreconnected.of_constant_of_preserves_morphisms
    (h : ∀ {α : Type u₁} (F : J → α),
      (∀ {j₁ j₂ : J} (_ : j₁ ⟶ j₂), F j₁ = F j₂) → ∀ j j' : J, F j = F j') :
    IsPreconnected J :=
  IsPreconnected.of_any_functor_const_on_obj fun F =>
    h F.obj fun f => by ext; exact Discrete.eq_of_hom (F.map f)

theorem IsConnected.of_constant_of_preserves_morphisms [Nonempty J]
    (h : ∀ {α : Type u₁} (F : J → α),
      (∀ {j₁ j₂ : J} (_ : j₁ ⟶ j₂), F j₁ = F j₂) → ∀ j j' : J, F j = F j') :
    IsConnected J :=
  { IsPreconnected.of_constant_of_preserves_morphisms h with }

theorem induct_on_objects [IsPreconnected J] (p : Set J) {j₀ : J} (h0 : j₀ ∈ p)
    (h1 : ∀ {j₁ j₂ : J} (_ : j₁ ⟶ j₂), j₁ ∈ p ↔ j₂ ∈ p) (j : J) : j ∈ p := by
  let aux (j₁ j₂ : J) (f : j₁ ⟶ j₂) := congrArg ULift.up <| (h1 f).eq
  injection constant_of_preserves_morphisms (fun k => ULift.up.{u₁} (k ∈ p)) aux j j₀ with i
  rwa [i]

theorem IsConnected.of_induct {j₀ : J}
    (h : ∀ p : Set J, j₀ ∈ p → (∀ {j₁ j₂ : J} (_ : j₁ ⟶ j₂), j₁ ∈ p ↔ j₂ ∈ p) → ∀ j : J, j ∈ p) :
    IsConnected J :=
  have := Nonempty.intro j₀
  IsConnected.of_constant_of_preserves_morphisms fun {α} F a => by
    have w := h { j | F j = F j₀ } rfl (fun {j₁} {j₂} f => by
      change F j₁ = F j₀ ↔ F j₂ = F j₀
      simp [a f])
    intro j j'
    rw [w j, w j']

instance [hc : IsConnected J] : IsConnected (ULiftHom.{v₂} (ULift.{u₂} J)) := by
  apply IsConnected.of_induct
  · rintro p hj₀ h ⟨j⟩
    let p' : Set J := {j : J | p ⟨j⟩}
    have hj₀' : Classical.choice hc.is_nonempty ∈ p' := by
      simp only [p', (eq_self p')]
      exact hj₀
    apply induct_on_objects p' hj₀' fun f => h ((ULiftHomULiftCategory.equiv J).functor.map f)

theorem isPreconnected_induction [IsPreconnected J] (Z : J → Sort*)
    (h₁ : ∀ {j₁ j₂ : J} (_ : j₁ ⟶ j₂), Z j₁ → Z j₂) (h₂ : ∀ {j₁ j₂ : J} (_ : j₁ ⟶ j₂), Z j₂ → Z j₁)
    {j₀ : J} (x : Z j₀) (j : J) : Nonempty (Z j) :=
  (induct_on_objects { j | Nonempty (Z j) } ⟨x⟩
      (fun f => ⟨by rintro ⟨y⟩; exact ⟨h₁ f y⟩, by rintro ⟨y⟩; exact ⟨h₂ f y⟩⟩)
      j : _)

theorem isPreconnected_of_equivalent {K : Type u₂} [Category.{v₂} K] [IsPreconnected J]
    (e : J ≌ K) : IsPreconnected K where
  iso_constant F k :=
    ⟨calc
        F ≅ e.inverse ⋙ e.functor ⋙ F := (e.invFunIdAssoc F).symm
        _ ≅ e.inverse ⋙ (Functor.const J).obj ((e.functor ⋙ F).obj (e.inverse.obj k)) :=
          isoWhiskerLeft e.inverse (isoConstant (e.functor ⋙ F) (e.inverse.obj k))
        _ ≅ e.inverse ⋙ (Functor.const J).obj (F.obj k) :=
          isoWhiskerLeft _ ((F ⋙ Functor.const J).mapIso (e.counitIso.app k))
        _ ≅ (Functor.const K).obj (F.obj k) := NatIso.ofComponents fun _ => Iso.refl _⟩

lemma isPreconnected_iff_of_equivalence {K : Type u₂} [Category.{v₂} K] (e : J ≌ K) :
    IsPreconnected J ↔ IsPreconnected K :=
  ⟨fun _ => isPreconnected_of_equivalent e, fun _ => isPreconnected_of_equivalent e.symm⟩

theorem isConnected_of_equivalent {K : Type u₂} [Category.{v₂} K] (e : J ≌ K) [IsConnected J] :
    IsConnected K :=
  { is_nonempty := Nonempty.map e.functor.obj (by infer_instance)
    toIsPreconnected := isPreconnected_of_equivalent e }

lemma isConnected_iff_of_equivalence {K : Type u₂} [Category.{v₂} K] (e : J ≌ K) :
    IsConnected J ↔ IsConnected K :=
  ⟨fun _ => isConnected_of_equivalent e, fun _ => isConnected_of_equivalent e.symm⟩

instance isPreconnected_op [IsPreconnected J] : IsPreconnected Jᵒᵖ where
  iso_constant := fun {α} F X =>
    ⟨NatIso.ofComponents fun Y =>
      eqToIso (Discrete.ext (Discrete.eq_of_hom ((Nonempty.some
        (IsPreconnected.iso_constant (F.rightOp ⋙ (Discrete.opposite α).functor) (unop X))).app
          (unop Y)).hom))⟩

instance isConnected_op [IsConnected J] : IsConnected Jᵒᵖ where
  is_nonempty := Nonempty.intro (op (Classical.arbitrary J))

theorem isPreconnected_of_isPreconnected_op [IsPreconnected Jᵒᵖ] : IsPreconnected J :=
  isPreconnected_of_equivalent (opOpEquivalence J)

theorem isConnected_of_isConnected_op [IsConnected Jᵒᵖ] : IsConnected J :=
  isConnected_of_equivalent (opOpEquivalence J)

def Zag (j₁ j₂ : J) : Prop :=
  Nonempty (j₁ ⟶ j₂) ∨ Nonempty (j₂ ⟶ j₁)

@[refl] theorem Zag.refl (X : J) : Zag X X := Or.inl ⟨𝟙 _⟩

theorem zag_symmetric : Symmetric (@Zag J _) := fun _ _ h => h.symm

@[symm] theorem Zag.symm {j₁ j₂ : J} (h : Zag j₁ j₂) : Zag j₂ j₁ := zag_symmetric h

theorem Zag.of_hom {j₁ j₂ : J} (f : j₁ ⟶ j₂) : Zag j₁ j₂ := Or.inl ⟨f⟩

theorem Zag.of_inv {j₁ j₂ : J} (f : j₂ ⟶ j₁) : Zag j₁ j₂ := Or.inr ⟨f⟩

def Zigzag : J → J → Prop :=
  Relation.ReflTransGen Zag

theorem zigzag_symmetric : Symmetric (@Zigzag J _) :=
  Relation.ReflTransGen.symmetric zag_symmetric

theorem zigzag_equivalence : _root_.Equivalence (@Zigzag J _) :=
  _root_.Equivalence.mk Relation.reflexive_reflTransGen (fun h => zigzag_symmetric h)
  (fun h g => Relation.transitive_reflTransGen h g)

@[refl] theorem Zigzag.refl (X : J) : Zigzag X X := zigzag_equivalence.refl _

@[symm] theorem Zigzag.symm {j₁ j₂ : J} (h : Zigzag j₁ j₂) : Zigzag j₂ j₁ := zigzag_symmetric h

@[trans] theorem Zigzag.trans {j₁ j₂ j₃ : J} (h₁ : Zigzag j₁ j₂) (h₂ : Zigzag j₂ j₃) :
    Zigzag j₁ j₃ :=
  zigzag_equivalence.trans h₁ h₂

theorem Zigzag.of_zag {j₁ j₂ : J} (h : Zag j₁ j₂) : Zigzag j₁ j₂ :=
  Relation.ReflTransGen.single h

theorem Zigzag.of_hom {j₁ j₂ : J} (f : j₁ ⟶ j₂) : Zigzag j₁ j₂ :=
  of_zag (Zag.of_hom f)

theorem Zigzag.of_inv {j₁ j₂ : J} (f : j₂ ⟶ j₁) : Zigzag j₁ j₂ :=
  of_zag (Zag.of_inv f)

theorem Zigzag.of_zag_trans {j₁ j₂ j₃ : J} (h₁ : Zag j₁ j₂) (h₂ : Zag j₂ j₃) : Zigzag j₁ j₃ :=
  trans (of_zag h₁) (of_zag h₂)

theorem Zigzag.of_hom_hom {j₁ j₂ j₃ : J} (f₁₂ : j₁ ⟶ j₂) (f₂₃ : j₂ ⟶ j₃) : Zigzag j₁ j₃ :=
  (of_hom f₁₂).trans (of_hom f₂₃)

theorem Zigzag.of_hom_inv {j₁ j₂ j₃ : J} (f₁₂ : j₁ ⟶ j₂) (f₃₂ : j₃ ⟶ j₂) : Zigzag j₁ j₃ :=
  (of_hom f₁₂).trans (of_inv f₃₂)

theorem Zigzag.of_inv_hom {j₁ j₂ j₃ : J} (f₂₁ : j₂ ⟶ j₁) (f₂₃ : j₂ ⟶ j₃) : Zigzag j₁ j₃ :=
  (of_inv f₂₁).trans (of_hom f₂₃)

theorem Zigzag.of_inv_inv {j₁ j₂ j₃ : J} (f₂₁ : j₂ ⟶ j₁) (f₃₂ : j₃ ⟶ j₂) : Zigzag j₁ j₃ :=
  (of_inv f₂₁).trans (of_inv f₃₂)

def Zigzag.setoid (J : Type u₂) [Category.{v₁} J] : Setoid J where
  r := Zigzag
  iseqv := zigzag_equivalence

theorem zigzag_prefunctor_obj_of_zigzag (F : J ⥤q K) {j₁ j₂ : J} (h : Zigzag j₁ j₂) :
    Zigzag (F.obj j₁) (F.obj j₂) :=
  h.lift _ fun _ _ => Or.imp (Nonempty.map fun f => F.map f) (Nonempty.map fun f => F.map f)

theorem zigzag_obj_of_zigzag (F : J ⥤ K) {j₁ j₂ : J} (h : Zigzag j₁ j₂) :
    Zigzag (F.obj j₁) (F.obj j₂) :=
  zigzag_prefunctor_obj_of_zigzag F.toPrefunctor h

lemma eq_of_zag (X) {a b : Discrete X} (h : Zag a b) : a.as = b.as :=
  h.elim (fun ⟨f⟩ ↦ Discrete.eq_of_hom f) (fun ⟨f⟩ ↦ (Discrete.eq_of_hom f).symm)

lemma eq_of_zigzag (X) {a b : Discrete X} (h : Zigzag a b) : a.as = b.as := by
  induction h with
  | refl => rfl
  | tail _ h eq  => exact eq.trans (eq_of_zag _ h)

theorem zag_of_zag_obj (F : J ⥤ K) [F.Full] {j₁ j₂ : J} (h : Zag (F.obj j₁) (F.obj j₂)) :
    Zag j₁ j₂ :=
  Or.imp (Nonempty.map F.preimage) (Nonempty.map F.preimage) h

theorem equiv_relation [IsPreconnected J] (r : J → J → Prop) (hr : _root_.Equivalence r)
    (h : ∀ {j₁ j₂ : J} (_ : j₁ ⟶ j₂), r j₁ j₂) : ∀ j₁ j₂ : J, r j₁ j₂ := by
  intros j₁ j₂
  have z : ∀ j : J, r j₁ j :=
    induct_on_objects {k | r j₁ k} (hr.1 j₁)
      fun f => ⟨fun t => hr.3 t (h f), fun t => hr.3 t (hr.2 (h f))⟩
  exact z j₂

theorem isPreconnected_zigzag [IsPreconnected J] (j₁ j₂ : J) : Zigzag j₁ j₂ :=
  equiv_relation _ zigzag_equivalence
    (fun f => Relation.ReflTransGen.single (Or.inl (Nonempty.intro f))) _ _

theorem zigzag_isPreconnected (h : ∀ j₁ j₂ : J, Zigzag j₁ j₂) : IsPreconnected J := by
  apply IsPreconnected.of_constant_of_preserves_morphisms
  intro α F hF j j'
  specialize h j j'
  induction' h with j₁ j₂ _ hj ih
  · rfl
  · rw [ih]
    rcases hj with (⟨⟨hj⟩⟩|⟨⟨hj⟩⟩)
    exacts [hF hj, (hF hj).symm]

theorem zigzag_isConnected [Nonempty J] (h : ∀ j₁ j₂ : J, Zigzag j₁ j₂) : IsConnected J :=
  { zigzag_isPreconnected h with }

theorem exists_zigzag' [IsConnected J] (j₁ j₂ : J) :
    ∃ l, List.Chain Zag j₁ l ∧ List.getLast (j₁ :: l) (List.cons_ne_nil _ _) = j₂ :=
  List.exists_chain_of_relationReflTransGen (isPreconnected_zigzag _ _)

theorem isPreconnected_of_zigzag (h : ∀ j₁ j₂ : J, ∃ l,
    List.Chain Zag j₁ l ∧ List.getLast (j₁ :: l) (List.cons_ne_nil _ _) = j₂) :
    IsPreconnected J := by
  apply zigzag_isPreconnected
  intro j₁ j₂
  rcases h j₁ j₂ with ⟨l, hl₁, hl₂⟩
  apply List.relationReflTransGen_of_exists_chain l hl₁ hl₂

theorem isConnected_of_zigzag [Nonempty J] (h : ∀ j₁ j₂ : J, ∃ l,
    List.Chain Zag j₁ l ∧ List.getLast (j₁ :: l) (List.cons_ne_nil _ _) = j₂) :
    IsConnected J :=
  { isPreconnected_of_zigzag h with }

def discreteIsConnectedEquivPUnit {α : Type u₁} [IsConnected (Discrete α)] : α ≃ PUnit :=
  Discrete.equivOfEquivalence.{u₁, u₁}
    { functor := Functor.star (Discrete α)
      inverse := Discrete.functor fun _ => Classical.arbitrary _
      unitIso := isoConstant _ (Classical.arbitrary _)
      counitIso := Functor.punitExt _ _ }

variable {C : Type w₂} [Category.{w₁} C]

theorem nat_trans_from_is_connected [IsPreconnected J] {X Y : C}
    (α : (Functor.const J).obj X ⟶ (Functor.const J).obj Y) :
    ∀ j j' : J, α.app j = (α.app j' : X ⟶ Y) :=
  @constant_of_preserves_morphisms _ _ _ (X ⟶ Y) (fun j => α.app j) fun _ _ f => by
    have := α.naturality f
    erw [id_comp, comp_id] at this
    exact this.symm

instance [IsConnected J] : (Functor.const J : C ⥤ J ⥤ C).Full where
  map_surjective f := ⟨f.app (Classical.arbitrary J), by
    ext j
    apply nat_trans_from_is_connected f (Classical.arbitrary J) j⟩

theorem nonempty_hom_of_preconnected_groupoid {G} [Groupoid G] [IsPreconnected G] :
    ∀ x y : G, Nonempty (x ⟶ y) := by
  refine equiv_relation _ ?_ fun {j₁ j₂} => Nonempty.intro
  exact
    ⟨fun j => ⟨𝟙 _⟩,
     fun {j₁ j₂} => Nonempty.map fun f => inv f,
     fun {_ _ _} => Nonempty.map2 (· ≫ ·)⟩

attribute [instance] nonempty_hom_of_preconnected_groupoid

alias nonempty_hom_of_connected_groupoid := nonempty_hom_of_preconnected_groupoid

end CategoryTheory
