/-
Extracted from CategoryTheory/Sites/LocallySurjective.lean
Genuine: 27 | Conflates: 0 | Dissolved: 0 | Infrastructure: 16
-/
import Origin.Core
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Sites.LocallyInjective

/-!

# Locally surjective morphisms

## Main definitions

- `IsLocallySurjective` : A morphism of presheaves valued in a concrete category is locally
  surjective with respect to a Grothendieck topology if every section in the target is locally
  in the set-theoretic image, i.e. the image sheaf coincides with the target.

## Main results

- `Presheaf.isLocallySurjective_toSheafify`: `toSheafify` is locally surjective.
- `Sheaf.isLocallySurjective_iff_epi`: a morphism of sheaves of types is locally
  surjective iff it is epi

-/

universe v u w v' u' w'

open Opposite CategoryTheory CategoryTheory.GrothendieckTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike

variable {A : Type u'} [Category.{v'} A] [ConcreteCategory.{w'} A]

namespace Presheaf

@[simps (config := .lemmasOnly)]
def imageSieve {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : G.obj (op U)) : Sieve U where
  arrows V i := ∃ t : F.obj (op V), f.app _ t = G.map i.op s
  downward_closed := by
    rintro V W i ⟨t, ht⟩ j
    refine ⟨F.map j.op t, ?_⟩
    rw [op_comp, G.map_comp, comp_apply, ← ht, elementwise_of% f.naturality]

theorem imageSieve_eq_sieveOfSection {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : G.obj (op U)) :
    imageSieve f s = (imagePresheaf (whiskerRight f (forget A))).sieveOfSection s :=
  rfl

theorem imageSieve_whisker_forget {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : G.obj (op U)) :
    imageSieve (whiskerRight f (forget A)) s = imageSieve f s :=
  rfl

theorem imageSieve_app {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : F.obj (op U)) :
    imageSieve f (f.app _ s) = ⊤ := by
  ext V i
  simp only [Sieve.top_apply, iff_true, imageSieve_apply]
  have := elementwise_of% (f.naturality i.op)
  exact ⟨F.map i.op s, this s⟩

noncomputable def localPreimage {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : Cᵒᵖ} (s : G.obj U)
    {V : C} (g : V ⟶ U.unop) (hg : imageSieve f s g) :
    F.obj (op V) :=
  hg.choose

@[simp]
lemma app_localPreimage {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : Cᵒᵖ} (s : G.obj U)
    {V : C} (g : V ⟶ U.unop) (hg : imageSieve f s g) :
    f.app _ (localPreimage f s g hg) = G.map g.op s :=
  hg.choose_spec

class IsLocallySurjective {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) : Prop where
  imageSieve_mem {U : C} (s : G.obj (op U)) : imageSieve f s ∈ J U

lemma imageSieve_mem {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) [IsLocallySurjective J f] {U : Cᵒᵖ}
    (s : G.obj U) : imageSieve f s ∈ J U.unop :=
  IsLocallySurjective.imageSieve_mem _

instance {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) [IsLocallySurjective J f] :
    IsLocallySurjective J (whiskerRight f (forget A)) where
  imageSieve_mem s := imageSieve_mem J f s

theorem isLocallySurjective_iff_imagePresheaf_sheafify_eq_top {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) :
    IsLocallySurjective J f ↔ (imagePresheaf (whiskerRight f (forget A))).sheafify J = ⊤ := by
  simp only [Subpresheaf.ext_iff, funext_iff, Set.ext_iff, top_subpresheaf_obj,
    Set.top_eq_univ, Set.mem_univ, iff_true]
  exact ⟨fun H _ => H.imageSieve_mem, fun H => ⟨H _⟩⟩

theorem isLocallySurjective_iff_imagePresheaf_sheafify_eq_top' {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G) :
    IsLocallySurjective J f ↔ (imagePresheaf f).sheafify J = ⊤ := by
  apply isLocallySurjective_iff_imagePresheaf_sheafify_eq_top

theorem isLocallySurjective_iff_whisker_forget {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) :
    IsLocallySurjective J f ↔ IsLocallySurjective J (whiskerRight f (forget A)) := by
  simp only [isLocallySurjective_iff_imagePresheaf_sheafify_eq_top]
  rfl

theorem isLocallySurjective_of_surjective {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G)
    (H : ∀ U, Function.Surjective (f.app U)) : IsLocallySurjective J f where
  imageSieve_mem {U} s := by
    obtain ⟨t, rfl⟩ := H _ s
    rw [imageSieve_app]
    exact J.top_mem _

instance isLocallySurjective_of_iso {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) [IsIso f] :
    IsLocallySurjective J f := by
  apply isLocallySurjective_of_surjective
  intro U
  apply Function.Bijective.surjective
  rw [← isIso_iff_bijective, ← forget_map_eq_coe]
  infer_instance

instance isLocallySurjective_comp {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
    [IsLocallySurjective J f₁] [IsLocallySurjective J f₂] :
    IsLocallySurjective J (f₁ ≫ f₂) where
  imageSieve_mem s := by
    have : (Sieve.bind (imageSieve f₂ s) fun _ _ h => imageSieve f₁ h.choose) ≤
        imageSieve (f₁ ≫ f₂) s := by
      rintro V i ⟨W, i, j, H, ⟨t', ht'⟩, rfl⟩
      refine ⟨t', ?_⟩
      rw [op_comp, F₃.map_comp, NatTrans.comp_app, comp_apply, comp_apply, ht',
        elementwise_of% f₂.naturality, H.choose_spec]
    apply J.superset_covering this
    apply J.bind_covering
    · apply imageSieve_mem
    · intros; apply imageSieve_mem

lemma isLocallySurjective_of_isLocallySurjective
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
    [IsLocallySurjective J (f₁ ≫ f₂)] :
    IsLocallySurjective J f₂ where
  imageSieve_mem {X} x := by
    refine J.superset_covering ?_ (imageSieve_mem J (f₁ ≫ f₂) x)
    intro Y g hg
    exact ⟨f₁.app _ (localPreimage (f₁ ≫ f₂) x g hg),
      by simpa using app_localPreimage (f₁ ≫ f₂) x g hg⟩

lemma isLocallySurjective_of_isLocallySurjective_fac
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} {f₁ : F₁ ⟶ F₂} {f₂ : F₂ ⟶ F₃} {f₃ : F₁ ⟶ F₃} (fac : f₁ ≫ f₂ = f₃)
    [IsLocallySurjective J f₃] : IsLocallySurjective J f₂ := by
  subst fac
  exact isLocallySurjective_of_isLocallySurjective J f₁ f₂

lemma isLocallySurjective_iff_of_fac
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} {f₁ : F₁ ⟶ F₂} {f₂ : F₂ ⟶ F₃} {f₃ : F₁ ⟶ F₃} (fac : f₁ ≫ f₂ = f₃)
    [IsLocallySurjective J f₁] :
    IsLocallySurjective J f₃ ↔ IsLocallySurjective J f₂ := by
  constructor
  · intro
    exact isLocallySurjective_of_isLocallySurjective_fac J fac
  · intro
    rw [← fac]
    infer_instance

lemma comp_isLocallySurjective_iff
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
    [IsLocallySurjective J f₁] :
    IsLocallySurjective J (f₁ ≫ f₂) ↔ IsLocallySurjective J f₂ :=
  isLocallySurjective_iff_of_fac J rfl

variable {J} in

lemma isLocallySurjective_of_le {K : GrothendieckTopology C} (hJK : J ≤ K) {F G : Cᵒᵖ ⥤ A}
    (f : F ⟶ G) (h : IsLocallySurjective J f) : IsLocallySurjective K f where
  imageSieve_mem s := by apply hJK; exact h.1 _

lemma isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
    [IsLocallyInjective J (f₁ ≫ f₂)] [IsLocallySurjective J f₁] :
    IsLocallyInjective J f₂ where
  equalizerSieve_mem {X} x₁ x₂ h := by
    let S := imageSieve f₁ x₁ ⊓ imageSieve f₁ x₂
    have hS : S ∈ J X.unop := by
      apply J.intersection_covering
      all_goals apply imageSieve_mem
    let T : ∀ ⦃Y : C⦄ (f : Y ⟶ X.unop) (_ : S f), Sieve Y := fun Y f hf =>
      equalizerSieve (localPreimage f₁ x₁ f hf.1) (localPreimage f₁ x₂ f hf.2)
    refine J.superset_covering ?_ (J.transitive hS (Sieve.bind S.1 T) ?_)
    · rintro Y f ⟨Z, a, g, hg, ha, rfl⟩
      simpa using congr_arg (f₁.app _) ha
    · intro Y f hf
      apply J.superset_covering (Sieve.le_pullback_bind _ _ _ hf)
      apply equalizerSieve_mem J (f₁ ≫ f₂)
      dsimp
      rw [comp_apply, comp_apply, app_localPreimage, app_localPreimage,
        NatTrans.naturality_apply, NatTrans.naturality_apply, h]

lemma isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} {f₁ : F₁ ⟶ F₂} {f₂ : F₂ ⟶ F₃} (f₃ : F₁ ⟶ F₃) (fac : f₁ ≫ f₂ = f₃)
    [IsLocallyInjective J f₃] [IsLocallySurjective J f₁] :
    IsLocallyInjective J f₂ := by
  subst fac
  exact isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective J f₁ f₂

lemma isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
    [IsLocallySurjective J (f₁ ≫ f₂)] [IsLocallyInjective J f₂] :
    IsLocallySurjective J f₁ where
  imageSieve_mem {X} x := by
    let S := imageSieve (f₁ ≫ f₂) (f₂.app _ x)
    let T : ∀ ⦃Y : C⦄ (f : Y ⟶ X) (_ : S f), Sieve Y := fun Y f hf =>
      equalizerSieve (f₁.app _ (localPreimage (f₁ ≫ f₂) (f₂.app _ x) f hf)) (F₂.map f.op x)
    refine J.superset_covering ?_ (J.transitive (imageSieve_mem J (f₁ ≫ f₂) (f₂.app _ x))
      (Sieve.bind S.1 T) ?_)
    · rintro Y _ ⟨Z, a, g, hg, ha, rfl⟩
      exact ⟨F₁.map a.op (localPreimage (f₁ ≫ f₂) _ _ hg), by simpa using ha⟩
    · intro Y f hf
      apply J.superset_covering (Sieve.le_pullback_bind _ _ _ hf)
      apply equalizerSieve_mem J f₂
      rw [NatTrans.naturality_apply, ← app_localPreimage (f₁ ≫ f₂) _ _ hf,
        NatTrans.comp_app, comp_apply]

lemma isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective_fac
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} {f₁ : F₁ ⟶ F₂} {f₂ : F₂ ⟶ F₃} (f₃ : F₁ ⟶ F₃) (fac : f₁ ≫ f₂ = f₃)
    [IsLocallySurjective J f₃] [IsLocallyInjective J f₂] :
    IsLocallySurjective J f₁ := by
  subst fac
  exact isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective J f₁ f₂

lemma comp_isLocallyInjective_iff
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
    [IsLocallyInjective J f₁] [IsLocallySurjective J f₁] :
    IsLocallyInjective J (f₁ ≫ f₂) ↔ IsLocallyInjective J f₂ := by
  constructor
  · intro
    exact isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective J f₁ f₂
  · intro
    infer_instance

lemma isLocallySurjective_comp_iff
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
    [IsLocallyInjective J f₂] [IsLocallySurjective J f₂] :
    IsLocallySurjective J (f₁ ≫ f₂) ↔ IsLocallySurjective J f₁ := by
  constructor
  · intro
    exact isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective J f₁ f₂
  · intro
    infer_instance

instance {F₁ F₂ : Cᵒᵖ ⥤ Type w} (f : F₁ ⟶ F₂) :
    IsLocallySurjective J (toImagePresheafSheafify J f) where
  imageSieve_mem {X} := by
    rintro ⟨s, hs⟩
    refine J.superset_covering ?_ hs
    rintro Y g ⟨t, ht⟩
    exact ⟨t, Subtype.ext ht⟩

noncomputable def sheafificationIsoImagePresheaf (F : Cᵒᵖ ⥤ Type max u v) :
    J.sheafify F ≅ ((imagePresheaf (J.toSheafify F)).sheafify J).toPresheaf where
  hom :=
    J.sheafifyLift (toImagePresheafSheafify J _)
      ((isSheaf_iff_isSheaf_of_type J _).mpr <|
        Subpresheaf.sheafify_isSheaf _ <|
          (isSheaf_iff_isSheaf_of_type J _).mp <| GrothendieckTopology.sheafify_isSheaf J _)
  inv := Subpresheaf.ι _
  hom_inv_id :=
    J.sheafify_hom_ext _ _ (J.sheafify_isSheaf _) (by simp [toImagePresheafSheafify])
  inv_hom_id := by
    rw [← cancel_mono (Subpresheaf.ι _), Category.id_comp, Category.assoc]
    refine Eq.trans ?_ (Category.comp_id _)
    congr 1
    exact J.sheafify_hom_ext _ _ (J.sheafify_isSheaf _) (by simp [toImagePresheafSheafify])

section

open GrothendieckTopology.Plus

instance isLocallySurjective_toPlus (P : Cᵒᵖ ⥤ Type max u v) :
    IsLocallySurjective J (J.toPlus P) where
  imageSieve_mem x := by
    obtain ⟨S, x, rfl⟩ := exists_rep x
    refine J.superset_covering (fun Y f hf => ⟨x.1 ⟨Y, f, hf⟩, ?_⟩) S.2
    dsimp
    rw [toPlus_eq_mk, res_mk_eq_mk_pullback, eq_mk_iff_exists]
    refine ⟨S.pullback f, homOfLE le_top, 𝟙 _, ?_⟩
    ext ⟨Z, g, hg⟩
    simpa using x.2 (Cover.Relation.mk { hf := hf }
        { hf := S.1.downward_closed hf g } { g₁ := g, g₂ := 𝟙 Z })

instance isLocallySurjective_toSheafify (P : Cᵒᵖ ⥤ Type max u v) :
    IsLocallySurjective J (J.toSheafify P) := by
  dsimp [GrothendieckTopology.toSheafify]
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

instance isLocallySurjective_toSheafify' {D : Type*} [Category D]
    [ConcreteCategory.{max u v} D]
    (P : Cᵒᵖ ⥤ D) [HasWeakSheafify J D] [J.HasSheafCompose (forget D)]
    [J.PreservesSheafification (forget D)] :
    IsLocallySurjective J (toSheafify J P) := by
  rw [isLocallySurjective_iff_whisker_forget,
    ← sheafComposeIso_hom_fac, ← toSheafify_plusPlusIsoSheafify_hom]
  infer_instance

end

end Presheaf

namespace Sheaf

variable {J}

variable {F₁ F₂ F₃ : Sheaf J A} (φ : F₁ ⟶ F₂) (ψ : F₂ ⟶ F₃)

abbrev IsLocallySurjective := Presheaf.IsLocallySurjective J φ.val

lemma isLocallySurjective_sheafToPresheaf_map_iff :
    Presheaf.IsLocallySurjective J ((sheafToPresheaf J A).map φ) ↔ IsLocallySurjective φ := by rfl

instance isLocallySurjective_comp [IsLocallySurjective φ] [IsLocallySurjective ψ] :
    IsLocallySurjective (φ ≫ ψ) :=
  Presheaf.isLocallySurjective_comp J φ.val ψ.val

instance isLocallySurjective_of_iso [IsIso φ] : IsLocallySurjective φ := by
  have : IsIso φ.val := (inferInstance : IsIso ((sheafToPresheaf J A).map φ))
  infer_instance

instance {F G : Sheaf J (Type w)} (f : F ⟶ G) :
    IsLocallySurjective (toImageSheaf f) := by
  dsimp [toImageSheaf]
  infer_instance

variable [J.HasSheafCompose (forget A)]

instance [IsLocallySurjective φ] :
    IsLocallySurjective ((sheafCompose J (forget A)).map φ) :=
  (Presheaf.isLocallySurjective_iff_whisker_forget J φ.val).1 inferInstance

theorem isLocallySurjective_iff_isIso {F G : Sheaf J (Type w)} (f : F ⟶ G) :
    IsLocallySurjective f ↔ IsIso (imageSheafι f) := by
  dsimp only [IsLocallySurjective]
  rw [imageSheafι, Presheaf.isLocallySurjective_iff_imagePresheaf_sheafify_eq_top',
    Subpresheaf.eq_top_iff_isIso]
  exact isIso_iff_of_reflects_iso (f := imageSheafι f) (F := sheafToPresheaf J (Type w))

instance epi_of_isLocallySurjective' {F₁ F₂ : Sheaf J (Type w)} (φ : F₁ ⟶ F₂)
    [IsLocallySurjective φ] : Epi φ where
  left_cancellation {Z} f₁ f₂ h := by
    ext X x
    apply (Presieve.isSeparated_of_isSheaf J Z.1 ((isSheaf_iff_isSheaf_of_type _ _).1 Z.2) _
      (Presheaf.imageSieve_mem J φ.val x)).ext
    rintro Y f ⟨s : F₁.val.obj (op Y), hs : φ.val.app _ s = F₂.val.map f.op x⟩
    dsimp
    have h₁ := congr_fun (f₁.val.naturality f.op) x
    have h₂ := congr_fun (f₂.val.naturality f.op) x
    dsimp at h₁ h₂
    rw [← h₁, ← h₂, ← hs]
    exact congr_fun (congr_app ((sheafToPresheaf J _).congr_map h) (op Y)) s

instance epi_of_isLocallySurjective [IsLocallySurjective φ] : Epi φ :=
  (sheafCompose J (forget A)).epi_of_epi_map inferInstance

lemma isLocallySurjective_iff_epi {F G : Sheaf J (Type w)} (φ : F ⟶ G)
    [HasSheafify J (Type w)] :
    IsLocallySurjective φ ↔ Epi φ := by
  constructor
  · intro
    infer_instance
  · intro
    have := epi_of_epi_fac (toImageSheaf_ι φ)
    rw [isLocallySurjective_iff_isIso φ]
    apply isIso_of_mono_of_epi

end Sheaf

namespace Presieve.FamilyOfElements

variable {R R' : Cᵒᵖ ⥤ Type w} (φ : R ⟶ R') {X : Cᵒᵖ} (r' : R'.obj X)

noncomputable def localPreimage :
    FamilyOfElements R (Presheaf.imageSieve φ r').arrows :=
  fun _ f hf => Presheaf.localPreimage φ r' f hf

lemma isAmalgamation_map_localPreimage :
    ((localPreimage φ r').map φ).IsAmalgamation r' :=
  fun _ f hf => (Presheaf.app_localPreimage φ r' f hf).symm

end Presieve.FamilyOfElements

end CategoryTheory
