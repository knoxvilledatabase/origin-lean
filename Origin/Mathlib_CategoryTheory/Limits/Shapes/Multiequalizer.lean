/-
Extracted from CategoryTheory/Limits/Shapes/Multiequalizer.lean
Genuine: 73 of 106 | Dissolved: 0 | Infrastructure: 33
-/
import Origin.Core
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.ConeCategory

/-!

# Multi-(co)equalizers

A *multiequalizer* is an equalizer of two morphisms between two products.
Since both products and equalizers are limits, such an object is again a limit.
This file provides the diagram whose limit is indeed such an object.
In fact, it is well-known that any limit can be obtained as a multiequalizer.
The dual construction (multicoequalizers) is also provided.

## Projects

Prove that a multiequalizer can be identified with
an equalizer between products (and analogously for multicoequalizers).

Prove that the limit of any diagram is a multiequalizer (and similarly for colimits).

-/

namespace CategoryTheory.Limits

open CategoryTheory

universe w w' v u

inductive WalkingMulticospan {L : Type w} {R : Type w'} (fst snd : R → L) : Type max w w'
  | left : L → WalkingMulticospan fst snd
  | right : R → WalkingMulticospan fst snd

inductive WalkingMultispan {L : Type w} {R : Type w'} (fst snd : L → R) : Type max w w'
  | left : L → WalkingMultispan fst snd
  | right : R → WalkingMultispan fst snd

namespace WalkingMulticospan

variable {L : Type w} {R : Type w'} {fst snd : R → L}

instance [Inhabited L] : Inhabited (WalkingMulticospan fst snd) :=
  ⟨left default⟩

inductive Hom : ∀ _ _ : WalkingMulticospan fst snd, Type max w w'
  | id (A) : Hom A A
  | fst (b) : Hom (left (fst b)) (right b)
  | snd (b) : Hom (left (snd b)) (right b)

attribute [-simp, nolint simpNF] WalkingMulticospan.Hom.id.sizeOf_spec

instance {a : WalkingMulticospan fst snd} : Inhabited (Hom a a) :=
  ⟨Hom.id _⟩

def Hom.comp : ∀ {A B C : WalkingMulticospan fst snd} (_ : Hom A B) (_ : Hom B C), Hom A C
  | _, _, _, Hom.id X, f => f
  | _, _, _, Hom.fst b, Hom.id _ => Hom.fst b
  | _, _, _, Hom.snd b, Hom.id _ => Hom.snd b

instance : SmallCategory (WalkingMulticospan fst snd) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    rintro (_ | _) (_ | _) (_ | _ | _) <;> rfl
  comp_id := by
    rintro (_ | _) (_ | _) (_ | _ | _) <;> rfl
  assoc := by
    rintro (_ | _) (_ | _) (_ | _) (_ | _) (_ | _ | _) (_ | _ | _) (_ | _ | _) <;> rfl

@[simp]
lemma Hom.id_eq_id (X : WalkingMulticospan fst snd) :
    Hom.id X = 𝟙 X := rfl

@[simp]
lemma Hom.comp_eq_comp {X Y Z : WalkingMulticospan fst snd}
    (f : X ⟶ Y) (g : Y ⟶ Z) : Hom.comp f g = f ≫ g := rfl

end WalkingMulticospan

namespace WalkingMultispan

variable {L : Type w} {R : Type w'} {fst snd : L → R}

instance [Inhabited L] : Inhabited (WalkingMultispan fst snd) :=
  ⟨left default⟩

inductive Hom : ∀ _ _ : WalkingMultispan fst snd, Type max w w'
  | id (A) : Hom A A
  | fst (a) : Hom (left a) (right (fst a))
  | snd (a) : Hom (left a) (right (snd a))

attribute [-simp, nolint simpNF] WalkingMultispan.Hom.id.sizeOf_spec

instance {a : WalkingMultispan fst snd} : Inhabited (Hom a a) :=
  ⟨Hom.id _⟩

def Hom.comp : ∀ {A B C : WalkingMultispan fst snd} (_ : Hom A B) (_ : Hom B C), Hom A C
  | _, _, _, Hom.id X, f => f
  | _, _, _, Hom.fst a, Hom.id _ => Hom.fst a
  | _, _, _, Hom.snd a, Hom.id _ => Hom.snd a

instance : SmallCategory (WalkingMultispan fst snd) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    rintro (_ | _) (_ | _) (_ | _ | _) <;> rfl
  comp_id := by
    rintro (_ | _) (_ | _) (_ | _ | _) <;> rfl
  assoc := by
    rintro (_ | _) (_ | _) (_ | _) (_ | _) (_ | _ | _) (_ | _ | _) (_ | _ | _) <;> rfl

@[simp]
lemma Hom.id_eq_id (X : WalkingMultispan fst snd) : Hom.id X = 𝟙 X := rfl

@[simp]
lemma Hom.comp_eq_comp {X Y Z : WalkingMultispan fst snd}
    (f : X ⟶ Y) (g : Y ⟶ Z) : Hom.comp f g = f ≫ g := rfl

end WalkingMultispan

@[nolint checkUnivs]
structure MulticospanIndex (C : Type u) [Category.{v} C] where
  (L : Type w)
  (R : Type w')
  (fstTo sndTo : R → L)
  left : L → C
  right : R → C
  fst : ∀ b, left (fstTo b) ⟶ right b
  snd : ∀ b, left (sndTo b) ⟶ right b

@[nolint checkUnivs]
structure MultispanIndex (C : Type u) [Category.{v} C] where
  (L : Type w)
  (R : Type w')
  (fstFrom sndFrom : L → R)
  left : L → C
  right : R → C
  fst : ∀ a, left a ⟶ right (fstFrom a)
  snd : ∀ a, left a ⟶ right (sndFrom a)

namespace MulticospanIndex

variable {C : Type u} [Category.{v} C] (I : MulticospanIndex.{w, w'} C)

@[simps]
def multicospan : WalkingMulticospan I.fstTo I.sndTo ⥤ C where
  obj x :=
    match x with
    | WalkingMulticospan.left a => I.left a
    | WalkingMulticospan.right b => I.right b
  map {x y} f :=
    match x, y, f with
    | _, _, WalkingMulticospan.Hom.id x => 𝟙 _
    | _, _, WalkingMulticospan.Hom.fst b => I.fst _
    | _, _, WalkingMulticospan.Hom.snd b => I.snd _
  map_id := by
    rintro (_ | _) <;> rfl
  map_comp := by
    rintro (_ | _) (_ | _) (_ | _) (_ | _ | _) (_ | _ | _) <;> aesop_cat

variable [HasProduct I.left] [HasProduct I.right]

noncomputable def fstPiMap : ∏ᶜ I.left ⟶ ∏ᶜ I.right :=
  Pi.lift fun b => Pi.π I.left (I.fstTo b) ≫ I.fst b

noncomputable def sndPiMap : ∏ᶜ I.left ⟶ ∏ᶜ I.right :=
  Pi.lift fun b => Pi.π I.left (I.sndTo b) ≫ I.snd b

@[reassoc (attr := simp)]
theorem fstPiMap_π (b) : I.fstPiMap ≫ Pi.π I.right b = Pi.π I.left _ ≫ I.fst b := by
  simp [fstPiMap]

@[reassoc (attr := simp)]
theorem sndPiMap_π (b) : I.sndPiMap ≫ Pi.π I.right b = Pi.π I.left _ ≫ I.snd b := by
  simp [sndPiMap]

@[simps!]
protected noncomputable def parallelPairDiagram :=
  parallelPair I.fstPiMap I.sndPiMap

end MulticospanIndex

namespace MultispanIndex

variable {C : Type u} [Category.{v} C] (I : MultispanIndex.{w, w'} C)

def multispan : WalkingMultispan I.fstFrom I.sndFrom ⥤ C where
  obj x :=
    match x with
    | WalkingMultispan.left a => I.left a
    | WalkingMultispan.right b => I.right b
  map {x y} f :=
    match x, y, f with
    | _, _, WalkingMultispan.Hom.id x => 𝟙 _
    | _, _, WalkingMultispan.Hom.fst b => I.fst _
    | _, _, WalkingMultispan.Hom.snd b => I.snd _
  map_id := by
    rintro (_ | _) <;> rfl
  map_comp := by
    rintro (_ | _) (_ | _) (_ | _) (_ | _ | _) (_ | _ | _) <;> aesop_cat

@[simp]
theorem multispan_obj_left (a) : I.multispan.obj (WalkingMultispan.left a) = I.left a :=
  rfl

@[simp]
theorem multispan_obj_right (b) : I.multispan.obj (WalkingMultispan.right b) = I.right b :=
  rfl

@[simp]
theorem multispan_map_fst (a) : I.multispan.map (WalkingMultispan.Hom.fst a) = I.fst a :=
  rfl

@[simp]
theorem multispan_map_snd (a) : I.multispan.map (WalkingMultispan.Hom.snd a) = I.snd a :=
  rfl

variable [HasCoproduct I.left] [HasCoproduct I.right]

noncomputable def fstSigmaMap : ∐ I.left ⟶ ∐ I.right :=
  Sigma.desc fun b => I.fst b ≫ Sigma.ι _ (I.fstFrom b)

noncomputable def sndSigmaMap : ∐ I.left ⟶ ∐ I.right :=
  Sigma.desc fun b => I.snd b ≫ Sigma.ι _ (I.sndFrom b)

@[reassoc (attr := simp)]
theorem ι_fstSigmaMap (b) : Sigma.ι I.left b ≫ I.fstSigmaMap = I.fst b ≫ Sigma.ι I.right _ := by
  simp [fstSigmaMap]

@[reassoc (attr := simp)]
theorem ι_sndSigmaMap (b) : Sigma.ι I.left b ≫ I.sndSigmaMap = I.snd b ≫ Sigma.ι I.right _ := by
  simp [sndSigmaMap]

protected noncomputable abbrev parallelPairDiagram :=
  parallelPair I.fstSigmaMap I.sndSigmaMap

end MultispanIndex

variable {C : Type u} [Category.{v} C]

abbrev Multifork (I : MulticospanIndex.{w, w'} C) :=
  Cone I.multicospan

abbrev Multicofork (I : MultispanIndex.{w, w'} C) :=
  Cocone I.multispan

namespace Multifork

variable {I : MulticospanIndex.{w, w'} C} (K : Multifork I)

def ι (a : I.L) : K.pt ⟶ I.left a :=
  K.π.app (WalkingMulticospan.left _)

@[simp]
theorem app_left_eq_ι (a) : K.π.app (WalkingMulticospan.left a) = K.ι a :=
  rfl

@[simp]
theorem app_right_eq_ι_comp_fst (b) :
    K.π.app (WalkingMulticospan.right b) = K.ι (I.fstTo b) ≫ I.fst b := by
  rw [← K.w (WalkingMulticospan.Hom.fst b)]
  rfl

@[reassoc]
theorem app_right_eq_ι_comp_snd (b) :
    K.π.app (WalkingMulticospan.right b) = K.ι (I.sndTo b) ≫ I.snd b := by
  rw [← K.w (WalkingMulticospan.Hom.snd b)]
  rfl

@[reassoc (attr := simp)]
theorem hom_comp_ι (K₁ K₂ : Multifork I) (f : K₁ ⟶ K₂) (j : I.L) : f.hom ≫ K₂.ι j = K₁.ι j :=
  f.w _

@[simps]
def ofι (I : MulticospanIndex.{w, w'} C) (P : C) (ι : ∀ a, P ⟶ I.left a)
    (w : ∀ b, ι (I.fstTo b) ≫ I.fst b = ι (I.sndTo b) ≫ I.snd b) : Multifork I where
  pt := P
  π :=
    { app := fun x =>
        match x with
        | WalkingMulticospan.left _ => ι _
        | WalkingMulticospan.right b => ι (I.fstTo b) ≫ I.fst b
      naturality := by
        rintro (_ | _) (_ | _) (_ | _ | _) <;>
          dsimp <;> simp only [Category.id_comp, Category.comp_id]
        apply w }

@[reassoc (attr := simp)]
theorem condition (b) : K.ι (I.fstTo b) ≫ I.fst b = K.ι (I.sndTo b) ≫ I.snd b := by
  rw [← app_right_eq_ι_comp_fst, ← app_right_eq_ι_comp_snd]

@[simps]
def IsLimit.mk (lift : ∀ E : Multifork I, E.pt ⟶ K.pt)
    (fac : ∀ (E : Multifork I) (i : I.L), lift E ≫ K.ι i = E.ι i)
    (uniq : ∀ (E : Multifork I) (m : E.pt ⟶ K.pt), (∀ i : I.L, m ≫ K.ι i = E.ι i) → m = lift E) :
    IsLimit K :=
  { lift
    fac := by
      rintro E (a | b)
      · apply fac
      · rw [← E.w (WalkingMulticospan.Hom.fst b), ← K.w (WalkingMulticospan.Hom.fst b), ←
          Category.assoc]
        congr 1
        apply fac
    uniq := by
      rintro E m hm
      apply uniq
      intro i
      apply hm }

variable {K}

lemma IsLimit.hom_ext (hK : IsLimit K) {T : C} {f g : T ⟶ K.pt}
    (h : ∀ a, f ≫ K.ι a = g ≫ K.ι a) : f = g := by
  apply hK.hom_ext
  rintro (_|b)
  · apply h
  · dsimp
    rw [app_right_eq_ι_comp_fst, reassoc_of% h]

def IsLimit.lift (hK : IsLimit K) {T : C} (k : ∀ a, T ⟶ I.left a)
    (hk : ∀ b, k (I.fstTo b) ≫ I.fst b = k (I.sndTo b) ≫ I.snd b) :
    T ⟶ K.pt :=
  hK.lift (Multifork.ofι _ _ k hk)

@[reassoc (attr := simp)]
lemma IsLimit.fac (hK : IsLimit K) {T : C} (k : ∀ a, T ⟶ I.left a)
    (hk : ∀ b, k (I.fstTo b) ≫ I.fst b = k (I.sndTo b) ≫ I.snd b) (a : I.L) :
    IsLimit.lift hK k hk ≫ K.ι a = k a :=
  hK.fac _ _

variable (K)

variable [HasProduct I.left] [HasProduct I.right]

@[reassoc (attr := simp)]
theorem pi_condition : Pi.lift K.ι ≫ I.fstPiMap = Pi.lift K.ι ≫ I.sndPiMap := by
  ext
  simp

@[simps pt]
noncomputable def toPiFork (K : Multifork I) : Fork I.fstPiMap I.sndPiMap where
  pt := K.pt
  π :=
    { app := fun x =>
        match x with
        | WalkingParallelPair.zero => Pi.lift K.ι
        | WalkingParallelPair.one => Pi.lift K.ι ≫ I.fstPiMap
      naturality := by
        rintro (_ | _) (_ | _) (_ | _ | _) <;>
          dsimp <;>
          simp only [Category.id_comp, Functor.map_id, parallelPair_obj_zero, Category.comp_id,
            pi_condition, parallelPair_obj_one] }

@[simp]
theorem toPiFork_π_app_zero : K.toPiFork.ι = Pi.lift K.ι :=
  rfl

@[simp]
theorem toPiFork_π_app_one : K.toPiFork.π.app WalkingParallelPair.one = Pi.lift K.ι ≫ I.fstPiMap :=
  rfl

variable (I)

@[simps pt]
noncomputable def ofPiFork (c : Fork I.fstPiMap I.sndPiMap) : Multifork I where
  pt := c.pt
  π :=
    { app := fun x =>
        match x with
        | WalkingMulticospan.left _ => c.ι ≫ Pi.π _ _
        | WalkingMulticospan.right _ => c.ι ≫ I.fstPiMap ≫ Pi.π _ _
      naturality := by
        rintro (_ | _) (_ | _) (_ | _ | _)
        · simp
        · simp
        · dsimp; rw [c.condition_assoc]; simp
        · simp }

@[simp]
theorem ofPiFork_π_app_left (c : Fork I.fstPiMap I.sndPiMap) (a) :
    (ofPiFork I c).ι a = c.ι ≫ Pi.π _ _ :=
  rfl

@[simp]
theorem ofPiFork_π_app_right (c : Fork I.fstPiMap I.sndPiMap) (a) :
    (ofPiFork I c).π.app (WalkingMulticospan.right a) = c.ι ≫ I.fstPiMap ≫ Pi.π _ _ :=
  rfl

end Multifork

namespace MulticospanIndex

variable (I : MulticospanIndex.{w, w'} C) [HasProduct I.left] [HasProduct I.right]

@[simps]
noncomputable def toPiForkFunctor : Multifork I ⥤ Fork I.fstPiMap I.sndPiMap where
  obj := Multifork.toPiFork
  map {K₁ K₂} f :=
    { hom := f.hom
      w := by
        rintro (_ | _)
        · apply limit.hom_ext
          simp
        · apply limit.hom_ext
          intros j
          simp only [Multifork.toPiFork_π_app_one, Multifork.pi_condition, Category.assoc]
          dsimp [sndPiMap]
          simp }

@[simps]
noncomputable def ofPiForkFunctor : Fork I.fstPiMap I.sndPiMap ⥤ Multifork I where
  obj := Multifork.ofPiFork I
  map {K₁ K₂} f :=
    { hom := f.hom
      w := by rintro (_ | _) <;> simp }

@[simps]
noncomputable def multiforkEquivPiFork : Multifork I ≌ Fork I.fstPiMap I.sndPiMap where
  functor := toPiForkFunctor I
  inverse := ofPiForkFunctor I
  unitIso :=
    NatIso.ofComponents fun K =>
      Cones.ext (Iso.refl _) (by
        rintro (_ | _) <;> simp [← Fork.app_one_eq_ι_comp_left])
  counitIso :=
    NatIso.ofComponents fun K => Fork.ext (Iso.refl _)

end MulticospanIndex

namespace Multicofork

variable {I : MultispanIndex.{w, w'} C} (K : Multicofork I)

def π (b : I.R) : I.right b ⟶ K.pt :=
  K.ι.app (WalkingMultispan.right _)

@[simp]
theorem π_eq_app_right (b) : K.ι.app (WalkingMultispan.right _) = K.π b :=
  rfl

@[simp]
theorem fst_app_right (a) : K.ι.app (WalkingMultispan.left a) = I.fst a ≫ K.π _ := by
  rw [← K.w (WalkingMultispan.Hom.fst a)]
  rfl

@[reassoc]
theorem snd_app_right (a) : K.ι.app (WalkingMultispan.left a) = I.snd a ≫ K.π _ := by
  rw [← K.w (WalkingMultispan.Hom.snd a)]
  rfl

@[reassoc (attr := simp)]
lemma π_comp_hom (K₁ K₂ : Multicofork I) (f : K₁ ⟶ K₂) (b : I.R) : K₁.π b ≫ f.hom = K₂.π b :=
  f.w _

@[simps]
def ofπ (I : MultispanIndex.{w, w'} C) (P : C) (π : ∀ b, I.right b ⟶ P)
    (w : ∀ a, I.fst a ≫ π (I.fstFrom a) = I.snd a ≫ π (I.sndFrom a)) : Multicofork I where
  pt := P
  ι :=
    { app := fun x =>
        match x with
        | WalkingMultispan.left a => I.fst a ≫ π _
        | WalkingMultispan.right _ => π _
      naturality := by
        rintro (_ | _) (_ | _) (_ | _ | _) <;> dsimp <;>
          simp only [Functor.map_id, MultispanIndex.multispan_obj_left,
            Category.id_comp, Category.comp_id, MultispanIndex.multispan_obj_right]
        symm
        apply w }

@[reassoc (attr := simp)]
theorem condition (a) : I.fst a ≫ K.π (I.fstFrom a) = I.snd a ≫ K.π (I.sndFrom a) := by
  rw [← K.snd_app_right, ← K.fst_app_right]

@[simps]
def IsColimit.mk (desc : ∀ E : Multicofork I, K.pt ⟶ E.pt)
    (fac : ∀ (E : Multicofork I) (i : I.R), K.π i ≫ desc E = E.π i)
    (uniq : ∀ (E : Multicofork I) (m : K.pt ⟶ E.pt), (∀ i : I.R, K.π i ≫ m = E.π i) → m = desc E) :
    IsColimit K :=
  { desc
    fac := by
      rintro S (a | b)
      · rw [← K.w (WalkingMultispan.Hom.fst a), ← S.w (WalkingMultispan.Hom.fst a),
          Category.assoc]
        congr 1
        apply fac
      · apply fac
    uniq := by
      intro S m hm
      apply uniq
      intro i
      apply hm }

variable [HasCoproduct I.left] [HasCoproduct I.right]

@[reassoc (attr := simp)]
theorem sigma_condition : I.fstSigmaMap ≫ Sigma.desc K.π = I.sndSigmaMap ≫ Sigma.desc K.π := by
  ext
  simp

@[simps pt]
noncomputable def toSigmaCofork (K : Multicofork I) : Cofork I.fstSigmaMap I.sndSigmaMap where
  pt := K.pt
  ι :=
    { app := fun x =>
        match x with
        | WalkingParallelPair.zero => I.fstSigmaMap ≫ Sigma.desc K.π
        | WalkingParallelPair.one => Sigma.desc K.π
      naturality := by
        rintro (_ | _) (_ | _) (_ | _ | _) <;> dsimp <;>
          simp only [Functor.map_id, parallelPair_obj_zero,
            parallelPair_obj_one, sigma_condition, Category.id_comp, Category.comp_id] }

@[simp]
theorem toSigmaCofork_π : K.toSigmaCofork.π = Sigma.desc K.π :=
  rfl

variable (I)

@[simps pt]
noncomputable def ofSigmaCofork (c : Cofork I.fstSigmaMap I.sndSigmaMap) : Multicofork I where
  pt := c.pt
  ι :=
    { app := fun x =>
        match x with
        | WalkingMultispan.left a => (Sigma.ι I.left a : _) ≫ I.fstSigmaMap ≫ c.π
        | WalkingMultispan.right b => (Sigma.ι I.right b : _) ≫ c.π
      naturality := by
        rintro (_ | _) (_ | _) (_ | _ | _)
        · simp
        · simp
        · simp [c.condition]
        · simp }

@[simp]
theorem ofSigmaCofork_ι_app_left (c : Cofork I.fstSigmaMap I.sndSigmaMap) (a) :
    (ofSigmaCofork I c).ι.app (WalkingMultispan.left a) =
      (Sigma.ι I.left a : _) ≫ I.fstSigmaMap ≫ c.π :=
  rfl

theorem ofSigmaCofork_ι_app_right (c : Cofork I.fstSigmaMap I.sndSigmaMap) (b) :
    (ofSigmaCofork I c).ι.app (WalkingMultispan.right b) = (Sigma.ι I.right b : _) ≫ c.π :=
  rfl

@[simp]
theorem ofSigmaCofork_ι_app_right' (c : Cofork I.fstSigmaMap I.sndSigmaMap) (b) :
    π (ofSigmaCofork I c) b = (Sigma.ι I.right b : _) ≫ c.π :=
  rfl

end Multicofork

namespace MultispanIndex

variable (I : MultispanIndex.{w, w'} C) [HasCoproduct I.left] [HasCoproduct I.right]

@[simps]
noncomputable def toSigmaCoforkFunctor : Multicofork I ⥤ Cofork I.fstSigmaMap I.sndSigmaMap where
  obj := Multicofork.toSigmaCofork
  map {K₁ K₂} f :=
  { hom := f.hom
    w := by
      rintro (_|_)
      all_goals {
        apply colimit.hom_ext
        rintro ⟨j⟩
        simp } }

@[simps]
noncomputable def ofSigmaCoforkFunctor : Cofork I.fstSigmaMap I.sndSigmaMap ⥤ Multicofork I where
  obj := Multicofork.ofSigmaCofork I
  map {K₁ K₂} f :=
    { hom := f.hom
      w := by --sorry --by rintro (_ | _) <;> simp
        rintro (_ | _)
        -- porting note; in mathlib3, `simp` worked. What seems to be happening is that
        -- the `simp` set is not confluent, and mathlib3 found
        -- `Multicofork.ofSigmaCofork_ι_app_left` before `Multicofork.fst_app_right`,
        -- but mathlib4 finds `Multicofork.fst_app_right` first.
        { simp [-Multicofork.fst_app_right] }
        -- Porting note: similarly here, the `simp` set seems to be non-confluent
        { simp [-Multicofork.ofSigmaCofork_pt] } }

@[simps]
noncomputable def multicoforkEquivSigmaCofork :
    Multicofork I ≌ Cofork I.fstSigmaMap I.sndSigmaMap where
  functor := toSigmaCoforkFunctor I
  inverse := ofSigmaCoforkFunctor I
  unitIso := NatIso.ofComponents fun K => Cocones.ext (Iso.refl _) (by
      rintro (_ | _) <;> simp)
  counitIso := NatIso.ofComponents fun K =>
    Cofork.ext (Iso.refl _)
      (by
        -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): in mathlib3 this was just `ext` and I don't know why it's not here
        apply Limits.colimit.hom_ext
        rintro ⟨j⟩
        dsimp
        simp only [Category.comp_id, colimit.ι_desc, Cofan.mk_ι_app]
        rfl)

end MultispanIndex

abbrev HasMultiequalizer (I : MulticospanIndex.{w, w'} C) :=
  HasLimit I.multicospan

noncomputable section

abbrev multiequalizer (I : MulticospanIndex.{w, w'} C) [HasMultiequalizer I] : C :=
  limit I.multicospan

abbrev HasMulticoequalizer (I : MultispanIndex.{w, w'} C) :=
  HasColimit I.multispan

abbrev multicoequalizer (I : MultispanIndex.{w, w'} C) [HasMulticoequalizer I] : C :=
  colimit I.multispan

namespace Multiequalizer

variable (I : MulticospanIndex.{w, w'} C) [HasMultiequalizer I]

abbrev ι (a : I.L) : multiequalizer I ⟶ I.left a :=
  limit.π _ (WalkingMulticospan.left a)

abbrev multifork : Multifork I :=
  limit.cone _

@[simp]
theorem multifork_ι (a) : (Multiequalizer.multifork I).ι a = Multiequalizer.ι I a :=
  rfl

@[simp]
theorem multifork_π_app_left (a) :
    (Multiequalizer.multifork I).π.app (WalkingMulticospan.left a) = Multiequalizer.ι I a :=
  rfl

@[reassoc]
theorem condition (b) :
    Multiequalizer.ι I (I.fstTo b) ≫ I.fst b = Multiequalizer.ι I (I.sndTo b) ≫ I.snd b :=
  Multifork.condition _ _

abbrev lift (W : C) (k : ∀ a, W ⟶ I.left a)
    (h : ∀ b, k (I.fstTo b) ≫ I.fst b = k (I.sndTo b) ≫ I.snd b) : W ⟶ multiequalizer I :=
  limit.lift _ (Multifork.ofι I _ k h)

@[reassoc]
theorem lift_ι (W : C) (k : ∀ a, W ⟶ I.left a)
    (h : ∀ b, k (I.fstTo b) ≫ I.fst b = k (I.sndTo b) ≫ I.snd b) (a) :
    Multiequalizer.lift I _ k h ≫ Multiequalizer.ι I a = k _ :=
  limit.lift_π _ _

@[ext]
theorem hom_ext {W : C} (i j : W ⟶ multiequalizer I)
    (h : ∀ a, i ≫ Multiequalizer.ι I a = j ≫ Multiequalizer.ι I a) : i = j :=
  Multifork.IsLimit.hom_ext (limit.isLimit _) h

variable [HasProduct I.left] [HasProduct I.right]

instance : HasEqualizer I.fstPiMap I.sndPiMap :=
  ⟨⟨⟨_, IsLimit.ofPreservesConeTerminal I.multiforkEquivPiFork.functor (limit.isLimit _)⟩⟩⟩

def isoEqualizer : multiequalizer I ≅ equalizer I.fstPiMap I.sndPiMap :=
  limit.isoLimitCone
    ⟨_, IsLimit.ofPreservesConeTerminal I.multiforkEquivPiFork.inverse (limit.isLimit _)⟩

def ιPi : multiequalizer I ⟶ ∏ᶜ I.left :=
  (isoEqualizer I).hom ≫ equalizer.ι I.fstPiMap I.sndPiMap

@[reassoc (attr := simp)]
theorem ιPi_π (a) : ιPi I ≫ Pi.π I.left a = ι I a := by
  rw [ιPi, Category.assoc, ← Iso.eq_inv_comp, isoEqualizer]
  simp

instance : Mono (ιPi I) := mono_comp _ _

end Multiequalizer

namespace Multicoequalizer

variable (I : MultispanIndex.{w, w'} C) [HasMulticoequalizer I]

abbrev π (b : I.R) : I.right b ⟶ multicoequalizer I :=
  colimit.ι I.multispan (WalkingMultispan.right _)

abbrev multicofork : Multicofork I :=
  colimit.cocone _

@[simp]
theorem multicofork_π (b) : (Multicoequalizer.multicofork I).π b = Multicoequalizer.π I b :=
  rfl

theorem multicofork_ι_app_right (b) :
    (Multicoequalizer.multicofork I).ι.app (WalkingMultispan.right b) = Multicoequalizer.π I b :=
  rfl

@[simp]
theorem multicofork_ι_app_right' (b) :
    colimit.ι (MultispanIndex.multispan I) (WalkingMultispan.right b) = π I b :=
  rfl

@[reassoc]
theorem condition (a) :
    I.fst a ≫ Multicoequalizer.π I (I.fstFrom a) = I.snd a ≫ Multicoequalizer.π I (I.sndFrom a) :=
  Multicofork.condition _ _

abbrev desc (W : C) (k : ∀ b, I.right b ⟶ W)
    (h : ∀ a, I.fst a ≫ k (I.fstFrom a) = I.snd a ≫ k (I.sndFrom a)) : multicoequalizer I ⟶ W :=
  colimit.desc _ (Multicofork.ofπ I _ k h)

@[reassoc]
theorem π_desc (W : C) (k : ∀ b, I.right b ⟶ W)
    (h : ∀ a, I.fst a ≫ k (I.fstFrom a) = I.snd a ≫ k (I.sndFrom a)) (b) :
    Multicoequalizer.π I b ≫ Multicoequalizer.desc I _ k h = k _ :=
  colimit.ι_desc _ _

@[ext]
theorem hom_ext {W : C} (i j : multicoequalizer I ⟶ W)
    (h : ∀ b, Multicoequalizer.π I b ≫ i = Multicoequalizer.π I b ≫ j) : i = j :=
  colimit.hom_ext
    (by
      rintro (a | b)
      · simp_rw [← colimit.w I.multispan (WalkingMultispan.Hom.fst a), Category.assoc, h]
      · apply h)

variable [HasCoproduct I.left] [HasCoproduct I.right]

instance : HasCoequalizer I.fstSigmaMap I.sndSigmaMap :=
  ⟨⟨⟨_,
      IsColimit.ofPreservesCoconeInitial
        I.multicoforkEquivSigmaCofork.functor (colimit.isColimit _)⟩⟩⟩

def isoCoequalizer : multicoequalizer I ≅ coequalizer I.fstSigmaMap I.sndSigmaMap :=
  colimit.isoColimitCocone
    ⟨_,
      IsColimit.ofPreservesCoconeInitial I.multicoforkEquivSigmaCofork.inverse
        (colimit.isColimit _)⟩

def sigmaπ : ∐ I.right ⟶ multicoequalizer I :=
  coequalizer.π I.fstSigmaMap I.sndSigmaMap ≫ (isoCoequalizer I).inv

@[reassoc (attr := simp)]
theorem ι_sigmaπ (b) : Sigma.ι I.right b ≫ sigmaπ I = π I b := by
  rw [sigmaπ, ← Category.assoc, Iso.comp_inv_eq, isoCoequalizer]
  simp only [MultispanIndex.multicoforkEquivSigmaCofork_inverse,
    MultispanIndex.ofSigmaCoforkFunctor_obj, colimit.isoColimitCocone_ι_hom,
    Multicofork.ofSigmaCofork_pt, colimit.cocone_x, Multicofork.π_eq_app_right]
  rfl

instance : Epi (sigmaπ I) := epi_comp _ _

end Multicoequalizer

end

end CategoryTheory.Limits
