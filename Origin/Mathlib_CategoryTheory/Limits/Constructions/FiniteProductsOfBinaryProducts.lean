/-
Extracted from CategoryTheory/Limits/Constructions/FiniteProductsOfBinaryProducts.lean
Genuine: 14 of 14 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Constructing finite products from binary products and terminal.

If a category has binary products and a terminal object then it has finite products.
If a functor preserves binary products and the terminal object then it preserves finite products.

## TODO

Provide the dual results.
Show the analogous results for functors which reflect or create (co)limits.
-/

universe v v' u u'

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace CategoryTheory

variable {J : Type v} [SmallCategory J]

variable {C : Type u} [Category.{v} C]

variable {D : Type u'} [Category.{v'} D]

@[simps!] -- Porting note: removed semi-reducible config
def extendFan {n : ℕ} {f : Fin (n + 1) → C} (c₁ : Fan fun i : Fin n => f i.succ)
    (c₂ : BinaryFan (f 0) c₁.pt) : Fan f :=
  Fan.mk c₂.pt
    (by
      refine Fin.cases ?_ ?_
      · apply c₂.fst
      · intro i
        apply c₂.snd ≫ c₁.π.app ⟨i⟩)

def extendFanIsLimit {n : ℕ} (f : Fin (n + 1) → C) {c₁ : Fan fun i : Fin n => f i.succ}
    {c₂ : BinaryFan (f 0) c₁.pt} (t₁ : IsLimit c₁) (t₂ : IsLimit c₂) :
    IsLimit (extendFan c₁ c₂) where
  lift s := by
    apply (BinaryFan.IsLimit.lift' t₂ (s.π.app ⟨0⟩) _).1
    apply t₁.lift ⟨_, Discrete.natTrans fun ⟨i⟩ => s.π.app ⟨i.succ⟩⟩
  fac := fun s ⟨j⟩ => by
    refine Fin.inductionOn j ?_ ?_
    · apply (BinaryFan.IsLimit.lift' t₂ _ _).2.1
    · rintro i -
      dsimp only [extendFan_π_app]
      rw [Fin.cases_succ, ← assoc, (BinaryFan.IsLimit.lift' t₂ _ _).2.2, t₁.fac]
      rfl
  uniq s m w := by
    apply BinaryFan.IsLimit.hom_ext t₂
    · rw [(BinaryFan.IsLimit.lift' t₂ _ _).2.1]
      apply w ⟨0⟩
    · rw [(BinaryFan.IsLimit.lift' t₂ _ _).2.2]
      apply t₁.uniq ⟨_, _⟩
      rintro ⟨j⟩
      rw [assoc]
      dsimp only [Discrete.natTrans_app]
      rw [← w ⟨j.succ⟩]
      dsimp only [extendFan_π_app]
      rw [Fin.cases_succ]

section

variable [HasBinaryProducts C] [HasTerminal C]

private theorem hasProduct_fin : ∀ (n : ℕ) (f : Fin n → C), HasProduct f
  | 0 => fun _ =>
    letI : HasLimitsOfShape (Discrete (Fin 0)) C :=
      hasLimitsOfShape_of_equivalence (Discrete.equivalence.{0} finZeroEquiv'.symm)
    inferInstance
  | n + 1 => fun f =>
    haveI := hasProduct_fin n
    HasLimit.mk ⟨_, extendFanIsLimit f (limit.isLimit _) (limit.isLimit _)⟩

theorem hasFiniteProducts_of_has_binary_and_terminal : HasFiniteProducts C :=
  ⟨fun n => ⟨fun K =>
    let this := hasProduct_fin n fun n => K.obj ⟨n⟩
    let that : (Discrete.functor fun n => K.obj ⟨n⟩) ≅ K := Discrete.natIso fun ⟨_⟩ => Iso.refl _
    @hasLimitOfIso _ _ _ _ _ _ this that⟩⟩

end

section Preserves

variable (F : C ⥤ D)

variable [PreservesLimitsOfShape (Discrete WalkingPair) F]

variable [PreservesLimitsOfShape (Discrete.{0} PEmpty) F]

variable [HasFiniteProducts.{v} C]

lemma preservesFinOfPreservesBinaryAndTerminal :
    ∀ (n : ℕ) (f : Fin n → C), PreservesLimit (Discrete.functor f) F
  | 0 => fun f => by
    letI : PreservesLimitsOfShape (Discrete (Fin 0)) F :=
      preservesLimitsOfShape_of_equiv.{0, 0} (Discrete.equivalence finZeroEquiv'.symm) _
    infer_instance
  | n + 1 => by
    haveI := preservesFinOfPreservesBinaryAndTerminal n
    intro f
    apply
      preservesLimit_of_preserves_limit_cone
        (extendFanIsLimit f (limit.isLimit _) (limit.isLimit _)) _
    apply (isLimitMapConeFanMkEquiv _ _ _).symm _
    let this :=
      extendFanIsLimit (fun i => F.obj (f i)) (isLimitOfHasProductOfPreservesLimit F _)
        (isLimitOfHasBinaryProductOfPreservesLimit F _ _)
    refine IsLimit.ofIsoLimit this ?_
    apply Cones.ext _ _
    · apply Iso.refl _
    rintro ⟨j⟩
    refine Fin.inductionOn j ?_ ?_
    · apply (Category.id_comp _).symm
    · rintro i _
      dsimp [extendFan_π_app, Iso.refl_hom, Fan.mk_π_app]
      change F.map _ ≫ _ = 𝟙 _ ≫ _
      simp only [id_comp, ← F.map_comp]
      rfl

lemma preservesShape_fin_of_preserves_binary_and_terminal (n : ℕ) :
    PreservesLimitsOfShape (Discrete (Fin n)) F where
  preservesLimit {K} := by
    let that : (Discrete.functor fun n => K.obj ⟨n⟩) ≅ K := Discrete.natIso fun ⟨i⟩ => Iso.refl _
    haveI := preservesFinOfPreservesBinaryAndTerminal F n fun n => K.obj ⟨n⟩
    apply preservesLimit_of_iso_diagram F that

lemma preservesFiniteProducts_of_preserves_binary_and_terminal (J : Type*) [Fintype J] :
    PreservesLimitsOfShape (Discrete J) F := by
  classical
    let e := Fintype.equivFin J
    haveI := preservesShape_fin_of_preserves_binary_and_terminal F (Fintype.card J)
    apply preservesLimitsOfShape_of_equiv (Discrete.equivalence e).symm

end Preserves

@[simps!] -- Porting note: removed semireducible config
def extendCofan {n : ℕ} {f : Fin (n + 1) → C} (c₁ : Cofan fun i : Fin n => f i.succ)
    (c₂ : BinaryCofan (f 0) c₁.pt) : Cofan f :=
  Cofan.mk c₂.pt
    (by
      refine Fin.cases ?_ ?_
      · apply c₂.inl
      · intro i
        apply c₁.ι.app ⟨i⟩ ≫ c₂.inr)

def extendCofanIsColimit {n : ℕ} (f : Fin (n + 1) → C) {c₁ : Cofan fun i : Fin n => f i.succ}
    {c₂ : BinaryCofan (f 0) c₁.pt} (t₁ : IsColimit c₁) (t₂ : IsColimit c₂) :
    IsColimit (extendCofan c₁ c₂) where
  desc s := by
    apply (BinaryCofan.IsColimit.desc' t₂ (s.ι.app ⟨0⟩) _).1
    apply t₁.desc ⟨_, Discrete.natTrans fun i => s.ι.app ⟨i.as.succ⟩⟩
  fac s := by
    rintro ⟨j⟩
    refine Fin.inductionOn j ?_ ?_
    · apply (BinaryCofan.IsColimit.desc' t₂ _ _).2.1
    · rintro i -
      dsimp only [extendCofan_ι_app]
      rw [Fin.cases_succ, assoc, (BinaryCofan.IsColimit.desc' t₂ _ _).2.2, t₁.fac]
      rfl
  uniq s m w := by
    apply BinaryCofan.IsColimit.hom_ext t₂
    · rw [(BinaryCofan.IsColimit.desc' t₂ _ _).2.1]
      apply w ⟨0⟩
    · rw [(BinaryCofan.IsColimit.desc' t₂ _ _).2.2]
      apply t₁.uniq ⟨_, _⟩
      rintro ⟨j⟩
      dsimp only [Discrete.natTrans_app]
      rw [← w ⟨j.succ⟩]
      dsimp only [extendCofan_ι_app]
      rw [Fin.cases_succ, assoc]

section

variable [HasBinaryCoproducts C] [HasInitial C]

private theorem hasCoproduct_fin : ∀ (n : ℕ) (f : Fin n → C), HasCoproduct f
  | 0 => fun _ =>
    letI : HasColimitsOfShape (Discrete (Fin 0)) C :=
      hasColimitsOfShape_of_equivalence (Discrete.equivalence.{0} finZeroEquiv'.symm)
    inferInstance
  | n + 1 => fun f =>
    haveI := hasCoproduct_fin n
    HasColimit.mk ⟨_, extendCofanIsColimit f (colimit.isColimit _) (colimit.isColimit _)⟩

theorem hasFiniteCoproducts_of_has_binary_and_initial : HasFiniteCoproducts C :=
  ⟨fun n => ⟨fun K =>
    letI := hasCoproduct_fin n fun n => K.obj ⟨n⟩
    let that : K ≅ Discrete.functor fun n => K.obj ⟨n⟩ := Discrete.natIso fun ⟨_⟩ => Iso.refl _
    @hasColimitOfIso _ _ _ _ _ _ this that⟩⟩

end

section Preserves

variable (F : C ⥤ D)

variable [PreservesColimitsOfShape (Discrete WalkingPair) F]

variable [PreservesColimitsOfShape (Discrete.{0} PEmpty) F]

variable [HasFiniteCoproducts.{v} C]

lemma preserves_fin_of_preserves_binary_and_initial :
    ∀ (n : ℕ) (f : Fin n → C), PreservesColimit (Discrete.functor f) F
  | 0 => fun f => by
    letI : PreservesColimitsOfShape (Discrete (Fin 0)) F :=
      preservesColimitsOfShape_of_equiv.{0, 0} (Discrete.equivalence finZeroEquiv'.symm) _
    infer_instance
  | n + 1 => by
    haveI := preserves_fin_of_preserves_binary_and_initial n
    intro f
    apply
      preservesColimit_of_preserves_colimit_cocone
        (extendCofanIsColimit f (colimit.isColimit _) (colimit.isColimit _)) _
    apply (isColimitMapCoconeCofanMkEquiv _ _ _).symm _
    let this :=
      extendCofanIsColimit (fun i => F.obj (f i))
        (isColimitOfHasCoproductOfPreservesColimit F _)
        (isColimitOfHasBinaryCoproductOfPreservesColimit F _ _)
    refine IsColimit.ofIsoColimit this ?_
    apply Cocones.ext _ _
    · apply Iso.refl _
    rintro ⟨j⟩
    refine Fin.inductionOn j ?_ ?_
    · apply Category.comp_id
    · rintro i _
      dsimp [extendCofan_ι_app, Iso.refl_hom, Cofan.mk_ι_app]
      rw [comp_id, ← F.map_comp]

lemma preservesShape_fin_of_preserves_binary_and_initial (n : ℕ) :
    PreservesColimitsOfShape (Discrete (Fin n)) F where
  preservesColimit {K} := by
    let that : (Discrete.functor fun n => K.obj ⟨n⟩) ≅ K := Discrete.natIso fun ⟨i⟩ => Iso.refl _
    haveI := preserves_fin_of_preserves_binary_and_initial F n fun n => K.obj ⟨n⟩
    apply preservesColimit_of_iso_diagram F that

lemma preservesFiniteCoproductsOfPreservesBinaryAndInitial (J : Type*) [Fintype J] :
    PreservesColimitsOfShape (Discrete J) F := by
  classical
    let e := Fintype.equivFin J
    haveI := preservesShape_fin_of_preserves_binary_and_initial F (Fintype.card J)
    apply preservesColimitsOfShape_of_equiv (Discrete.equivalence e).symm

end Preserves

end CategoryTheory
