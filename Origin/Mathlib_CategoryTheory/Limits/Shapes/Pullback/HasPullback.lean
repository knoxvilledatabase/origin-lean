/-
Extracted from CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean
Genuine: 66 of 74 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone

/-!
# HasPullback
`HasPullback f g` and `pullback f g` provides API for `HasLimit` and `limit` in the case of
pullacks.

# Main definitions

* `HasPullback f g`: this is an abbreviation for `HasLimit (cospan f g)`, and is a typeclass used to
  express the fact that a given pair of morphisms has a pullback.

* `HasPullbacks`: expresses the fact that `C` admits all pullbacks, it is implemented as an
  abbreviation for `HasLimitsOfShape WalkingCospan C`

* `pullback f g`: Given a `HasPullback f g` instance, this function returns the choice of a limit
  object corresponding to the pullback of `f` and `g`. It fits into the following diagram:
```
  pullback f g ---pullback.snd f g---> Y
      |                                |
      |                                |
pullback.snd f g                       g
      |                                |
      v                                v
      X --------------f--------------> Z
```

* `HasPushout f g`: this is an abbreviation for `HasColimit (span f g)`, and is a typeclass used to
  express the fact that a given pair of morphisms has a pushout.
* `HasPushouts`: expresses the fact that `C` admits all pushouts, it is implemented as an
abbreviation for `HasColimitsOfShape WalkingSpan C`
* `pushout f g`: Given a `HasPushout f g` instance, this function returns the choice of a colimit
  object corresponding to the pushout of `f` and `g`. It fits into the following diagram:
```
      X --------------f--------------> Y
      |                                |
      g                          pushout.inr f g
      |                                |
      v                                v
      Z ---pushout.inl f g---> pushout f g
```

# Main results & API
* The following API is available for using the universal property of `pullback f g`:
`lift`, `lift_fst`, `lift_snd`, `lift'`, `hom_ext` (for uniqueness).

* `pullback.map` is the induced map between pullbacks `W ×ₛ X ⟶ Y ×ₜ Z` given pointwise
(compatible) maps `W ⟶ Y`, `X ⟶ Z` and `S ⟶ T`.

* `pullbackComparison`: Given a functor `G`, this is the natural morphism
`G.obj (pullback f g) ⟶ pullback (G.map f) (G.map g)`

* `pullbackSymmetry` provides the natural isomorphism `pullback f g ≅ pullback g f`

(The dual results for pushouts are also available)

## References
* [Stacks: Fibre products](https://stacks.math.columbia.edu/tag/001U)
* [Stacks: Pushouts](https://stacks.math.columbia.edu/tag/0025)
-/

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

open WalkingSpan.Hom WalkingCospan.Hom WidePullbackShape.Hom WidePushoutShape.Hom

variable {C : Type u} [Category.{v} C] {W X Y Z : C}

abbrev HasPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :=
  HasLimit (cospan f g)

abbrev HasPushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :=
  HasColimit (span f g)

abbrev pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :=
  limit (cospan f g)

abbrev pullback.cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : PullbackCone f g :=
  limit.cone (cospan f g)

abbrev pushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :=
  colimit (span f g)

abbrev pushout.cocone {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : PushoutCocone f g :=
  colimit.cocone (span f g)

abbrev pullback.fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : pullback f g ⟶ X :=
  limit.π (cospan f g) WalkingCospan.left

abbrev pullback.snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : pullback f g ⟶ Y :=
  limit.π (cospan f g) WalkingCospan.right

abbrev pushout.inl {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : Y ⟶ pushout f g :=
  colimit.ι (span f g) WalkingSpan.left

abbrev pushout.inr {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : Z ⟶ pushout f g :=
  colimit.ι (span f g) WalkingSpan.right

abbrev pullback.lift {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : W ⟶ pullback f g :=
  limit.lift _ (PullbackCone.mk h k w)

abbrev pushout.desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : pushout f g ⟶ W :=
  colimit.desc _ (PushoutCocone.mk h k w)

abbrev pullback.isLimit {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    IsLimit (pullback.cone f g) :=
  limit.isLimit (cospan f g)

abbrev pushout.isColimit {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :
    IsColimit (pushout.cocone f g) :=
  colimit.isColimit (span f g)

@[simp]
theorem PullbackCone.fst_limit_cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasLimit (cospan f g)] :
    PullbackCone.fst (limit.cone (cospan f g)) = pullback.fst f g := rfl

@[simp]
theorem PullbackCone.snd_limit_cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasLimit (cospan f g)] :
    PullbackCone.snd (limit.cone (cospan f g)) = pullback.snd f g := rfl

theorem PushoutCocone.inl_colimit_cocone {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y)
    [HasColimit (span f g)] : PushoutCocone.inl (colimit.cocone (span f g)) = pushout.inl _ _ := rfl

theorem PushoutCocone.inr_colimit_cocone {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y)
    [HasColimit (span f g)] : PushoutCocone.inr (colimit.cocone (span f g)) = pushout.inr _ _ := rfl

@[reassoc]
theorem pullback.lift_fst {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : pullback.lift h k w ≫ pullback.fst f g = h :=
  limit.lift_π _ _

@[reassoc]
theorem pullback.lift_snd {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : pullback.lift h k w ≫ pullback.snd f g = k :=
  limit.lift_π _ _

@[reassoc]
theorem pushout.inl_desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W)
    (k : Z ⟶ W) (w : f ≫ h = g ≫ k) : pushout.inl _ _ ≫ pushout.desc h k w = h :=
  colimit.ι_desc _ _

@[reassoc]
theorem pushout.inr_desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W)
    (k : Z ⟶ W) (w : f ≫ h = g ≫ k) : pushout.inr _ _ ≫ pushout.desc h k w = k :=
  colimit.ι_desc _ _

def pullback.lift' {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) :
      { l : W ⟶ pullback f g // l ≫ pullback.fst f g = h ∧ l ≫ pullback.snd f g = k } :=
  ⟨pullback.lift h k w, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

def pullback.desc' {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) :
      { l : pushout f g ⟶ W // pushout.inl _ _ ≫ l = h ∧ pushout.inr _ _ ≫ l = k } :=
  ⟨pushout.desc h k w, pushout.inl_desc _ _ _, pushout.inr_desc _ _ _⟩

@[reassoc]
theorem pullback.condition {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] :
    pullback.fst f g ≫ f = pullback.snd f g ≫ g :=
  PullbackCone.condition _

@[reassoc]
theorem pushout.condition {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] :
    f ≫ (pushout.inl f g) = g ≫ pushout.inr _ _ :=
  PushoutCocone.condition _

@[ext 1100]
theorem pullback.hom_ext {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] {W : C}
    {k l : W ⟶ pullback f g} (h₀ : k ≫ pullback.fst f g = l ≫ pullback.fst f g)
    (h₁ : k ≫ pullback.snd f g = l ≫ pullback.snd f g) : k = l :=
  limit.hom_ext <| PullbackCone.equalizer_ext _ h₀ h₁

def pullbackIsPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    IsLimit (PullbackCone.mk (pullback.fst f g) (pullback.snd f g) pullback.condition) :=
  PullbackCone.mkSelfIsLimit <| pullback.isLimit f g

@[ext 1100]
theorem pushout.hom_ext {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] {W : C}
    {k l : pushout f g ⟶ W} (h₀ : pushout.inl _ _ ≫ k = pushout.inl _ _ ≫ l)
    (h₁ : pushout.inr _ _ ≫ k = pushout.inr _ _ ≫ l) : k = l :=
  colimit.hom_ext <| PushoutCocone.coequalizer_ext _ h₀ h₁

def pushoutIsPushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :
    IsColimit (PushoutCocone.mk (pushout.inl f g) (pushout.inr _ _) pushout.condition) :=
  PushoutCocone.IsColimit.mk _ (fun s => pushout.desc s.inl s.inr s.condition) (by simp) (by simp)
    (by aesop_cat)

abbrev pullback.map {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂] (g₁ : Y ⟶ T)
    (g₂ : Z ⟶ T) [HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) : pullback f₁ f₂ ⟶ pullback g₁ g₂ :=
  pullback.lift (pullback.fst f₁ f₂ ≫ i₁) (pullback.snd f₁ f₂ ≫ i₂)
    (by simp only [Category.assoc, ← eq₁, ← eq₂, pullback.condition_assoc])

abbrev pullback.mapDesc {X Y S T : C} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [HasPullback f g]
    [HasPullback (f ≫ i) (g ≫ i)] : pullback f g ⟶ pullback (f ≫ i) (g ≫ i) :=
  pullback.map f g (f ≫ i) (g ≫ i) (𝟙 _) (𝟙 _) i (Category.id_comp _).symm (Category.id_comp _).symm

@[reassoc]
lemma pullback.map_comp {X Y Z X' Y' Z' X'' Y'' Z'' : C}
    {f : X ⟶ Z} {g : Y ⟶ Z} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'} {f'' : X'' ⟶ Z''} {g'' : Y'' ⟶ Z''}
    (i₁ : X ⟶ X') (j₁ : X' ⟶ X'') (i₂ : Y ⟶ Y') (j₂ : Y' ⟶ Y'') (i₃ : Z ⟶ Z') (j₃ : Z' ⟶ Z'')
    [HasPullback f g] [HasPullback f' g'] [HasPullback f'' g'']
    (e₁ e₂ e₃ e₄) :
    pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂ ≫ pullback.map f' g' f'' g'' j₁ j₂ j₃ e₃ e₄ =
      pullback.map f g f'' g'' (i₁ ≫ j₁) (i₂ ≫ j₂) (i₃ ≫ j₃)
        (by rw [reassoc_of% e₁, e₃, Category.assoc])
        (by rw [reassoc_of% e₂, e₄, Category.assoc]) := by ext <;> simp

@[simp]
lemma pullback.map_id {X Y Z : C}
    {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] :
    pullback.map f g f g (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by ext <;> simp

abbrev pushout.map {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂] (g₁ : T ⟶ Y)
    (g₂ : T ⟶ Z) [HasPushout g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₁ = i₃ ≫ g₁)
    (eq₂ : f₂ ≫ i₂ = i₃ ≫ g₂) : pushout f₁ f₂ ⟶ pushout g₁ g₂ :=
  pushout.desc (i₁ ≫ pushout.inl _ _) (i₂ ≫ pushout.inr _ _)
    (by simp only [reassoc_of% eq₁, reassoc_of% eq₂, condition])

abbrev pushout.mapLift {X Y S T : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T) [HasPushout f g]
    [HasPushout (i ≫ f) (i ≫ g)] : pushout (i ≫ f) (i ≫ g) ⟶ pushout f g :=
  pushout.map (i ≫ f) (i ≫ g) f g (𝟙 _) (𝟙 _) i (Category.comp_id _) (Category.comp_id _)

@[reassoc]
lemma pushout.map_comp {X Y Z X' Y' Z' X'' Y'' Z'' : C}
    {f : X ⟶ Y} {g : X ⟶ Z} {f' : X' ⟶ Y'} {g' : X' ⟶ Z'} {f'' : X'' ⟶ Y''} {g'' : X'' ⟶ Z''}
    (i₁ : X ⟶ X') (j₁ : X' ⟶ X'') (i₂ : Y ⟶ Y') (j₂ : Y' ⟶ Y'') (i₃ : Z ⟶ Z') (j₃ : Z' ⟶ Z'')
    [HasPushout f g] [HasPushout f' g'] [HasPushout f'' g'']
    (e₁ e₂ e₃ e₄) :
    pushout.map f g f' g' i₂ i₃ i₁ e₁ e₂ ≫ pushout.map f' g' f'' g'' j₂ j₃ j₁ e₃ e₄ =
      pushout.map f g f'' g'' (i₂ ≫ j₂) (i₃ ≫ j₃) (i₁ ≫ j₁)
        (by rw [reassoc_of% e₁, e₃, Category.assoc])
        (by rw [reassoc_of% e₂, e₄, Category.assoc]) := by ext <;> simp

@[simp]
lemma pushout.map_id {X Y Z : C}
    {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] :
    pushout.map f g f g (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by ext <;> simp

instance pullback.map_isIso {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
    (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) [IsIso i₁] [IsIso i₂] [IsIso i₃] :
    IsIso (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) := by
  refine ⟨⟨pullback.map _ _ _ _ (inv i₁) (inv i₂) (inv i₃) ?_ ?_, ?_, ?_⟩⟩
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₁, IsIso.inv_hom_id_assoc]
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₂, IsIso.inv_hom_id_assoc]
  · aesop_cat
  · aesop_cat

@[simps! hom]
def pullback.congrHom {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : f₁ = f₂) (h₂ : g₁ = g₂)
    [HasPullback f₁ g₁] [HasPullback f₂ g₂] : pullback f₁ g₁ ≅ pullback f₂ g₂ :=
  asIso <| pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂])

@[simp]
theorem pullback.congrHom_inv {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : f₁ = f₂)
    (h₂ : g₁ = g₂) [HasPullback f₁ g₁] [HasPullback f₂ g₂] :
    (pullback.congrHom h₁ h₂).inv =
      pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂]) := by
  ext <;> simp [Iso.inv_comp_eq]

instance pushout.map_isIso {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂]
    (g₁ : T ⟶ Y) (g₂ : T ⟶ Z) [HasPushout g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₁ = i₃ ≫ g₁) (eq₂ : f₂ ≫ i₂ = i₃ ≫ g₂) [IsIso i₁] [IsIso i₂] [IsIso i₃] :
    IsIso (pushout.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) := by
  refine ⟨⟨pushout.map _ _ _ _ (inv i₁) (inv i₂) (inv i₃) ?_ ?_, ?_, ?_⟩⟩
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₁, IsIso.inv_hom_id_assoc]
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₂, IsIso.inv_hom_id_assoc]
  · aesop_cat
  · aesop_cat

theorem pullback.mapDesc_comp {X Y S T S' : C} (f : X ⟶ T) (g : Y ⟶ T) (i : T ⟶ S) (i' : S ⟶ S')
    [HasPullback f g] [HasPullback (f ≫ i) (g ≫ i)] [HasPullback (f ≫ i ≫ i') (g ≫ i ≫ i')]
    [HasPullback ((f ≫ i) ≫ i') ((g ≫ i) ≫ i')] :
    pullback.mapDesc f g (i ≫ i') = pullback.mapDesc f g i ≫ pullback.mapDesc _ _ i' ≫
    (pullback.congrHom (Category.assoc _ _ _) (Category.assoc _ _ _)).hom := by
  aesop_cat

@[simps! hom]
def pushout.congrHom {X Y Z : C} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z} (h₁ : f₁ = f₂) (h₂ : g₁ = g₂)
    [HasPushout f₁ g₁] [HasPushout f₂ g₂] : pushout f₁ g₁ ≅ pushout f₂ g₂ :=
  asIso <| pushout.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂])

@[simp]
theorem pushout.congrHom_inv {X Y Z : C} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z} (h₁ : f₁ = f₂)
    (h₂ : g₁ = g₂) [HasPushout f₁ g₁] [HasPushout f₂ g₂] :
    (pushout.congrHom h₁ h₂).inv =
      pushout.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂]) := by
  ext <;> simp [Iso.comp_inv_eq]

theorem pushout.mapLift_comp {X Y S T S' : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T) (i' : S' ⟶ S)
    [HasPushout f g] [HasPushout (i ≫ f) (i ≫ g)] [HasPushout (i' ≫ i ≫ f) (i' ≫ i ≫ g)]
    [HasPushout ((i' ≫ i) ≫ f) ((i' ≫ i) ≫ g)] :
    pushout.mapLift f g (i' ≫ i) =
      (pushout.congrHom (Category.assoc _ _ _) (Category.assoc _ _ _)).hom ≫
        pushout.mapLift _ _ i' ≫ pushout.mapLift f g i := by
  aesop_cat

section

variable {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)

def pullbackComparison (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [HasPullback (G.map f) (G.map g)] :
    G.obj (pullback f g) ⟶ pullback (G.map f) (G.map g) :=
  pullback.lift (G.map (pullback.fst f g)) (G.map (pullback.snd f g))
    (by simp only [← G.map_comp, pullback.condition])

@[reassoc (attr := simp)]
theorem pullbackComparison_comp_fst (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPullback (G.map f) (G.map g)] :
    pullbackComparison G f g ≫ pullback.fst _ _ = G.map (pullback.fst f g) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pullbackComparison_comp_snd (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPullback (G.map f) (G.map g)] :
    pullbackComparison G f g ≫ pullback.snd _ _ = G.map (pullback.snd f g):=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem map_lift_pullbackComparison (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPullback (G.map f) (G.map g)] {W : C} {h : W ⟶ X} {k : W ⟶ Y} (w : h ≫ f = k ≫ g) :
    G.map (pullback.lift _ _ w) ≫ pullbackComparison G f g =
      pullback.lift (G.map h) (G.map k) (by simp only [← G.map_comp, w]) := by
  ext <;> simp [← G.map_comp]

def pushoutComparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] [HasPushout (G.map f) (G.map g)] :
    pushout (G.map f) (G.map g) ⟶ G.obj (pushout f g) :=
  pushout.desc (G.map (pushout.inl _ _)) (G.map (pushout.inr _ _))
    (by simp only [← G.map_comp, pushout.condition])

@[reassoc (attr := simp)]
theorem inl_comp_pushoutComparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    [HasPushout (G.map f) (G.map g)] : pushout.inl _ _ ≫ pushoutComparison G f g =
      G.map (pushout.inl _ _) :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem inr_comp_pushoutComparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    [HasPushout (G.map f) (G.map g)] : pushout.inr _ _ ≫ pushoutComparison G f g =
      G.map (pushout.inr _ _) :=
  pushout.inr_desc _ _ _

@[reassoc (attr := simp)]
theorem pushoutComparison_map_desc (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    [HasPushout (G.map f) (G.map g)] {W : C} {h : Y ⟶ W} {k : Z ⟶ W} (w : f ≫ h = g ≫ k) :
    pushoutComparison G f g ≫ G.map (pushout.desc _ _ w) =
      pushout.desc (G.map h) (G.map k) (by simp only [← G.map_comp, w]) := by
  ext <;> simp [← G.map_comp]

end

section PullbackSymmetry

open WalkingCospan

variable (f : X ⟶ Z) (g : Y ⟶ Z)

theorem hasPullback_symmetry [HasPullback f g] : HasPullback g f :=
  ⟨⟨⟨_, PullbackCone.flipIsLimit (pullbackIsPullback f g)⟩⟩⟩

attribute [local instance] hasPullback_symmetry

def pullbackSymmetry [HasPullback f g] : pullback f g ≅ pullback g f :=
  IsLimit.conePointUniqueUpToIso
    (PullbackCone.flipIsLimit (pullbackIsPullback f g)) (limit.isLimit _)

@[reassoc (attr := simp)]
theorem pullbackSymmetry_hom_comp_fst [HasPullback f g] :
    (pullbackSymmetry f g).hom ≫ pullback.fst g f = pullback.snd f g := by simp [pullbackSymmetry]

@[reassoc (attr := simp)]
theorem pullbackSymmetry_hom_comp_snd [HasPullback f g] :
    (pullbackSymmetry f g).hom ≫ pullback.snd g f = pullback.fst f g := by simp [pullbackSymmetry]

@[reassoc (attr := simp)]
theorem pullbackSymmetry_inv_comp_fst [HasPullback f g] :
    (pullbackSymmetry f g).inv ≫ pullback.fst f g = pullback.snd g f := by simp [Iso.inv_comp_eq]

@[reassoc (attr := simp)]
theorem pullbackSymmetry_inv_comp_snd [HasPullback f g] :
    (pullbackSymmetry f g).inv ≫ pullback.snd f g = pullback.fst g f := by simp [Iso.inv_comp_eq]

end PullbackSymmetry

section PushoutSymmetry

open WalkingCospan

variable (f : X ⟶ Y) (g : X ⟶ Z)

theorem hasPushout_symmetry [HasPushout f g] : HasPushout g f :=
  ⟨⟨⟨_, PushoutCocone.flipIsColimit (pushoutIsPushout f g)⟩⟩⟩

attribute [local instance] hasPushout_symmetry

def pushoutSymmetry [HasPushout f g] : pushout f g ≅ pushout g f :=
  IsColimit.coconePointUniqueUpToIso
    (PushoutCocone.flipIsColimit (pushoutIsPushout f g)) (colimit.isColimit _)

@[reassoc (attr := simp)]
theorem inl_comp_pushoutSymmetry_hom [HasPushout f g] :
    pushout.inl _ _ ≫ (pushoutSymmetry f g).hom = pushout.inr _ _ :=
  (colimit.isColimit (span f g)).comp_coconePointUniqueUpToIso_hom
    (PushoutCocone.flipIsColimit (pushoutIsPushout g f)) _

@[reassoc (attr := simp)]
theorem inr_comp_pushoutSymmetry_hom [HasPushout f g] :
    pushout.inr _ _ ≫ (pushoutSymmetry f g).hom = pushout.inl _ _ :=
  (colimit.isColimit (span f g)).comp_coconePointUniqueUpToIso_hom
    (PushoutCocone.flipIsColimit (pushoutIsPushout g f)) _

@[reassoc (attr := simp)]
theorem inl_comp_pushoutSymmetry_inv [HasPushout f g] :
    pushout.inl _ _ ≫ (pushoutSymmetry f g).inv = pushout.inr _ _ := by simp [Iso.comp_inv_eq]

@[reassoc (attr := simp)]
theorem inr_comp_pushoutSymmetry_inv [HasPushout f g] :
    pushout.inr _ _ ≫ (pushoutSymmetry f g).inv = pushout.inl _ _ := by simp [Iso.comp_inv_eq]

end PushoutSymmetry

variable (C)

abbrev HasPullbacks :=
  HasLimitsOfShape WalkingCospan C

abbrev HasPushouts :=
  HasColimitsOfShape WalkingSpan C

theorem hasPullbacks_of_hasLimit_cospan
    [∀ {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}, HasLimit (cospan f g)] : HasPullbacks C :=
  { has_limit := fun F => hasLimitOfIso (diagramIsoCospan F).symm }

theorem hasPushouts_of_hasColimit_span
    [∀ {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}, HasColimit (span f g)] : HasPushouts C :=
  { has_colimit := fun F => hasColimitOfIso (diagramIsoSpan F) }

@[simps!]
def walkingSpanOpEquiv : WalkingSpanᵒᵖ ≌ WalkingCospan :=
  widePushoutShapeOpEquiv _

@[simps!]
def walkingCospanOpEquiv : WalkingCospanᵒᵖ ≌ WalkingSpan :=
  widePullbackShapeOpEquiv _

instance (priority := 100) hasPullbacks_of_hasWidePullbacks (D : Type u) [Category.{v} D]
    [HasWidePullbacks.{w} D] : HasPullbacks.{v,u} D :=
  hasWidePullbacks_shrink WalkingPair

instance (priority := 100) hasPushouts_of_hasWidePushouts (D : Type u) [Category.{v} D]
    [HasWidePushouts.{w} D] : HasPushouts.{v,u} D :=
  hasWidePushouts_shrink WalkingPair

end CategoryTheory.Limits
