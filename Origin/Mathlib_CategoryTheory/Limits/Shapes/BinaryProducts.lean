/-
Extracted from CategoryTheory/Limits/Shapes/BinaryProducts.lean
Genuine: 126 | Conflates: 0 | Dissolved: 0 | Infrastructure: 53
-/
import Origin.Core
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

noncomputable section

/-!
# Binary (co)products

We define a category `WalkingPair`, which is the index category
for a binary (co)product diagram. A convenience method `pair X Y`
constructs the functor from the walking pair, hitting the given objects.

We define `prod X Y` and `coprod X Y` as limits and colimits of such functors.

Typeclasses `HasBinaryProducts` and `HasBinaryCoproducts` assert the existence
of (co)limits shaped as walking pairs.

We include lemmas for simplifying equations involving projections and coprojections, and define
braiding and associating isomorphisms, and the product comparison morphism.

## References
* [Stacks: Products of pairs](https://stacks.math.columbia.edu/tag/001R)
* [Stacks: coproducts of pairs](https://stacks.math.columbia.edu/tag/04AN)
-/

universe v v₁ u u₁ u₂

open CategoryTheory

namespace CategoryTheory.Limits

inductive WalkingPair : Type
  | left
  | right
  deriving DecidableEq, Inhabited

open WalkingPair

def WalkingPair.swap : WalkingPair ≃ WalkingPair where
  toFun j := match j with
    | left => right
    | right => left
  invFun j := match j with
    | left => right
    | right => left
  left_inv j := by cases j; repeat rfl
  right_inv j := by cases j; repeat rfl

def WalkingPair.equivBool : WalkingPair ≃ Bool where
  toFun j := match j with
    | left => true
    | right => false
  -- to match equiv.sum_equiv_sigma_bool
  invFun b := Bool.recOn b right left
  left_inv j := by cases j; repeat rfl
  right_inv b := by cases b; repeat rfl

variable {C : Type u}

def pairFunction (X Y : C) : WalkingPair → C := fun j => WalkingPair.casesOn j X Y

variable [Category.{v} C]

def pair (X Y : C) : Discrete WalkingPair ⥤ C :=
  Discrete.functor fun j => WalkingPair.casesOn j X Y

section

variable {F G : Discrete WalkingPair ⥤ C} (f : F.obj ⟨left⟩ ⟶ G.obj ⟨left⟩)
  (g : F.obj ⟨right⟩ ⟶ G.obj ⟨right⟩)

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases

def mapPair : F ⟶ G where
  app j := match j with
    | ⟨left⟩ => f
    | ⟨right⟩ => g
  naturality := fun ⟨X⟩ ⟨Y⟩ ⟨⟨u⟩⟩ => by aesop_cat

@[simps!]
def mapPairIso (f : F.obj ⟨left⟩ ≅ G.obj ⟨left⟩) (g : F.obj ⟨right⟩ ≅ G.obj ⟨right⟩) : F ≅ G :=
  NatIso.ofComponents (fun j ↦ match j with
    | ⟨left⟩ => f
    | ⟨right⟩ => g)
    (fun ⟨⟨u⟩⟩ => by aesop_cat)

end

@[simps!]
def diagramIsoPair (F : Discrete WalkingPair ⥤ C) :
    F ≅ pair (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩) :=
  mapPairIso (Iso.refl _) (Iso.refl _)

section

variable {D : Type u₁} [Category.{v₁} D]

def pairComp (X Y : C) (F : C ⥤ D) : pair X Y ⋙ F ≅ pair (F.obj X) (F.obj Y) :=
  diagramIsoPair _

end

abbrev BinaryFan (X Y : C) :=
  Cone (pair X Y)

abbrev BinaryFan.fst {X Y : C} (s : BinaryFan X Y) :=
  s.π.app ⟨WalkingPair.left⟩

abbrev BinaryFan.snd {X Y : C} (s : BinaryFan X Y) :=
  s.π.app ⟨WalkingPair.right⟩

@[simp]
theorem BinaryFan.π_app_left {X Y : C} (s : BinaryFan X Y) : s.π.app ⟨WalkingPair.left⟩ = s.fst :=
  rfl

@[simp]
theorem BinaryFan.π_app_right {X Y : C} (s : BinaryFan X Y) : s.π.app ⟨WalkingPair.right⟩ = s.snd :=
  rfl

def BinaryFan.ext {A B : C} {c c' : BinaryFan A B} (e : c.pt ≅ c'.pt)
    (h₁ : c.fst = e.hom ≫ c'.fst) (h₂ : c.snd = e.hom ≫ c'.snd) : c ≅ c' :=
  Cones.ext e (fun j => by rcases j with ⟨⟨⟩⟩ <;> assumption)

def BinaryFan.IsLimit.mk {X Y : C} (s : BinaryFan X Y)
    (lift : ∀ {T : C} (_ : T ⟶ X) (_ : T ⟶ Y), T ⟶ s.pt)
    (hl₁ : ∀ {T : C} (f : T ⟶ X) (g : T ⟶ Y), lift f g ≫ s.fst = f)
    (hl₂ : ∀ {T : C} (f : T ⟶ X) (g : T ⟶ Y), lift f g ≫ s.snd = g)
    (uniq :
      ∀ {T : C} (f : T ⟶ X) (g : T ⟶ Y) (m : T ⟶ s.pt) (_ : m ≫ s.fst = f) (_ : m ≫ s.snd = g),
        m = lift f g) :
    IsLimit s :=
  Limits.IsLimit.mk (fun t => lift (BinaryFan.fst t) (BinaryFan.snd t))
    (by
      rintro t (rfl | rfl)
      · exact hl₁ _ _
      · exact hl₂ _ _)
    fun _ _ h => uniq _ _ _ (h ⟨WalkingPair.left⟩) (h ⟨WalkingPair.right⟩)

theorem BinaryFan.IsLimit.hom_ext {W X Y : C} {s : BinaryFan X Y} (h : IsLimit s) {f g : W ⟶ s.pt}
    (h₁ : f ≫ s.fst = g ≫ s.fst) (h₂ : f ≫ s.snd = g ≫ s.snd) : f = g :=
  h.hom_ext fun j => Discrete.recOn j fun j => WalkingPair.casesOn j h₁ h₂

abbrev BinaryCofan (X Y : C) := Cocone (pair X Y)

abbrev BinaryCofan.inl {X Y : C} (s : BinaryCofan X Y) := s.ι.app ⟨WalkingPair.left⟩

abbrev BinaryCofan.inr {X Y : C} (s : BinaryCofan X Y) := s.ι.app ⟨WalkingPair.right⟩

def BinaryCofan.ext {A B : C} {c c' : BinaryCofan A B} (e : c.pt ≅ c'.pt)
    (h₁ : c.inl ≫ e.hom = c'.inl) (h₂ : c.inr ≫ e.hom = c'.inr) : c ≅ c' :=
  Cocones.ext e (fun j => by rcases j with ⟨⟨⟩⟩ <;> assumption)

@[simp]
theorem BinaryCofan.ι_app_left {X Y : C} (s : BinaryCofan X Y) :
    s.ι.app ⟨WalkingPair.left⟩ = s.inl := rfl

@[simp]
theorem BinaryCofan.ι_app_right {X Y : C} (s : BinaryCofan X Y) :
    s.ι.app ⟨WalkingPair.right⟩ = s.inr := rfl

def BinaryCofan.IsColimit.mk {X Y : C} (s : BinaryCofan X Y)
    (desc : ∀ {T : C} (_ : X ⟶ T) (_ : Y ⟶ T), s.pt ⟶ T)
    (hd₁ : ∀ {T : C} (f : X ⟶ T) (g : Y ⟶ T), s.inl ≫ desc f g = f)
    (hd₂ : ∀ {T : C} (f : X ⟶ T) (g : Y ⟶ T), s.inr ≫ desc f g = g)
    (uniq :
      ∀ {T : C} (f : X ⟶ T) (g : Y ⟶ T) (m : s.pt ⟶ T) (_ : s.inl ≫ m = f) (_ : s.inr ≫ m = g),
        m = desc f g) :
    IsColimit s :=
  Limits.IsColimit.mk (fun t => desc (BinaryCofan.inl t) (BinaryCofan.inr t))
    (by
      rintro t (rfl | rfl)
      · exact hd₁ _ _
      · exact hd₂ _ _)
    fun _ _ h => uniq _ _ _ (h ⟨WalkingPair.left⟩) (h ⟨WalkingPair.right⟩)

theorem BinaryCofan.IsColimit.hom_ext {W X Y : C} {s : BinaryCofan X Y} (h : IsColimit s)
    {f g : s.pt ⟶ W} (h₁ : s.inl ≫ f = s.inl ≫ g) (h₂ : s.inr ≫ f = s.inr ≫ g) : f = g :=
  h.hom_ext fun j => Discrete.recOn j fun j => WalkingPair.casesOn j h₁ h₂

variable {X Y : C}

section

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases

attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Eq

@[simps pt]
def BinaryFan.mk {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : BinaryFan X Y where
  pt := P
  π := { app := fun | { as := j } => match j with | left => π₁ | right => π₂ }

@[simps pt]
def BinaryCofan.mk {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : BinaryCofan X Y where
  pt := P
  ι := { app := fun | { as := j } => match j with | left => ι₁ | right => ι₂ }

end

@[simp]
theorem BinaryFan.mk_fst {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : (BinaryFan.mk π₁ π₂).fst = π₁ :=
  rfl

@[simp]
theorem BinaryFan.mk_snd {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : (BinaryFan.mk π₁ π₂).snd = π₂ :=
  rfl

@[simp]
theorem BinaryCofan.mk_inl {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : (BinaryCofan.mk ι₁ ι₂).inl = ι₁ :=
  rfl

@[simp]
theorem BinaryCofan.mk_inr {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : (BinaryCofan.mk ι₁ ι₂).inr = ι₂ :=
  rfl

def isoBinaryFanMk {X Y : C} (c : BinaryFan X Y) : c ≅ BinaryFan.mk c.fst c.snd :=
    Cones.ext (Iso.refl _) fun j => by cases' j with l; cases l; repeat simp

def isoBinaryCofanMk {X Y : C} (c : BinaryCofan X Y) : c ≅ BinaryCofan.mk c.inl c.inr :=
    Cocones.ext (Iso.refl _) fun j => by cases' j with l; cases l; repeat simp

def BinaryFan.isLimitMk {W : C} {fst : W ⟶ X} {snd : W ⟶ Y} (lift : ∀ s : BinaryFan X Y, s.pt ⟶ W)
    (fac_left : ∀ s : BinaryFan X Y, lift s ≫ fst = s.fst)
    (fac_right : ∀ s : BinaryFan X Y, lift s ≫ snd = s.snd)
    (uniq :
      ∀ (s : BinaryFan X Y) (m : s.pt ⟶ W) (_ : m ≫ fst = s.fst) (_ : m ≫ snd = s.snd),
        m = lift s) :
    IsLimit (BinaryFan.mk fst snd) :=
  { lift := lift
    fac := fun s j => by
      rcases j with ⟨⟨⟩⟩
      exacts [fac_left s, fac_right s]
    uniq := fun s m w => uniq s m (w ⟨WalkingPair.left⟩) (w ⟨WalkingPair.right⟩) }

def BinaryCofan.isColimitMk {W : C} {inl : X ⟶ W} {inr : Y ⟶ W}
    (desc : ∀ s : BinaryCofan X Y, W ⟶ s.pt)
    (fac_left : ∀ s : BinaryCofan X Y, inl ≫ desc s = s.inl)
    (fac_right : ∀ s : BinaryCofan X Y, inr ≫ desc s = s.inr)
    (uniq :
      ∀ (s : BinaryCofan X Y) (m : W ⟶ s.pt) (_ : inl ≫ m = s.inl) (_ : inr ≫ m = s.inr),
        m = desc s) :
    IsColimit (BinaryCofan.mk inl inr) :=
  { desc := desc
    fac := fun s j => by
      rcases j with ⟨⟨⟩⟩
      exacts [fac_left s, fac_right s]
    uniq := fun s m w => uniq s m (w ⟨WalkingPair.left⟩) (w ⟨WalkingPair.right⟩) }

@[simps]
def BinaryFan.IsLimit.lift' {W X Y : C} {s : BinaryFan X Y} (h : IsLimit s) (f : W ⟶ X)
    (g : W ⟶ Y) : { l : W ⟶ s.pt // l ≫ s.fst = f ∧ l ≫ s.snd = g } :=
  ⟨h.lift <| BinaryFan.mk f g, h.fac _ _, h.fac _ _⟩

@[simps]
def BinaryCofan.IsColimit.desc' {W X Y : C} {s : BinaryCofan X Y} (h : IsColimit s) (f : X ⟶ W)
    (g : Y ⟶ W) : { l : s.pt ⟶ W // s.inl ≫ l = f ∧ s.inr ≫ l = g } :=
  ⟨h.desc <| BinaryCofan.mk f g, h.fac _ _, h.fac _ _⟩

def BinaryFan.isLimitFlip {X Y : C} {c : BinaryFan X Y} (hc : IsLimit c) :
    IsLimit (BinaryFan.mk c.snd c.fst) :=
  BinaryFan.isLimitMk (fun s => hc.lift (BinaryFan.mk s.snd s.fst)) (fun _ => hc.fac _ _)
    (fun _ => hc.fac _ _) fun s _ e₁ e₂ =>
    BinaryFan.IsLimit.hom_ext hc
      (e₂.trans (hc.fac (BinaryFan.mk s.snd s.fst) ⟨WalkingPair.left⟩).symm)
      (e₁.trans (hc.fac (BinaryFan.mk s.snd s.fst) ⟨WalkingPair.right⟩).symm)

theorem BinaryFan.isLimit_iff_isIso_fst {X Y : C} (h : IsTerminal Y) (c : BinaryFan X Y) :
    Nonempty (IsLimit c) ↔ IsIso c.fst := by
  constructor
  · rintro ⟨H⟩
    obtain ⟨l, hl, -⟩ := BinaryFan.IsLimit.lift' H (𝟙 X) (h.from X)
    exact
      ⟨⟨l,
          BinaryFan.IsLimit.hom_ext H (by simpa [hl, -Category.comp_id] using Category.comp_id _)
            (h.hom_ext _ _),
          hl⟩⟩
  · intro
    exact
      ⟨BinaryFan.IsLimit.mk _ (fun f _ => f ≫ inv c.fst) (fun _ _ => by simp)
          (fun _ _ => h.hom_ext _ _) fun _ _ _ e _ => by simp [← e]⟩

theorem BinaryFan.isLimit_iff_isIso_snd {X Y : C} (h : IsTerminal X) (c : BinaryFan X Y) :
    Nonempty (IsLimit c) ↔ IsIso c.snd := by
  refine Iff.trans ?_ (BinaryFan.isLimit_iff_isIso_fst h (BinaryFan.mk c.snd c.fst))
  exact
    ⟨fun h => ⟨BinaryFan.isLimitFlip h.some⟩, fun h =>
      ⟨(BinaryFan.isLimitFlip h.some).ofIsoLimit (isoBinaryFanMk c).symm⟩⟩

noncomputable def BinaryFan.isLimitCompLeftIso {X Y X' : C} (c : BinaryFan X Y) (f : X ⟶ X')
    [IsIso f] (h : IsLimit c) : IsLimit (BinaryFan.mk (c.fst ≫ f) c.snd) := by
  fapply BinaryFan.isLimitMk
  · exact fun s => h.lift (BinaryFan.mk (s.fst ≫ inv f) s.snd)
  · intro s -- Porting note: simp timed out here
    simp only [Category.comp_id,BinaryFan.π_app_left,IsIso.inv_hom_id,
      BinaryFan.mk_fst,IsLimit.fac_assoc,eq_self_iff_true,Category.assoc]
  · intro s -- Porting note: simp timed out here
    simp only [BinaryFan.π_app_right,BinaryFan.mk_snd,eq_self_iff_true,IsLimit.fac]
  · intro s m e₁ e₂
     -- Porting note: simpa timed out here also
    apply BinaryFan.IsLimit.hom_ext h
    · simpa only
      [BinaryFan.π_app_left,BinaryFan.mk_fst,Category.assoc,IsLimit.fac,IsIso.eq_comp_inv]
    · simpa only [BinaryFan.π_app_right,BinaryFan.mk_snd,IsLimit.fac]

noncomputable def BinaryFan.isLimitCompRightIso {X Y Y' : C} (c : BinaryFan X Y) (f : Y ⟶ Y')
    [IsIso f] (h : IsLimit c) : IsLimit (BinaryFan.mk c.fst (c.snd ≫ f)) :=
  BinaryFan.isLimitFlip <| BinaryFan.isLimitCompLeftIso _ f (BinaryFan.isLimitFlip h)

def BinaryCofan.isColimitFlip {X Y : C} {c : BinaryCofan X Y} (hc : IsColimit c) :
    IsColimit (BinaryCofan.mk c.inr c.inl) :=
  BinaryCofan.isColimitMk (fun s => hc.desc (BinaryCofan.mk s.inr s.inl)) (fun _ => hc.fac _ _)
    (fun _ => hc.fac _ _) fun s _ e₁ e₂ =>
    BinaryCofan.IsColimit.hom_ext hc
      (e₂.trans (hc.fac (BinaryCofan.mk s.inr s.inl) ⟨WalkingPair.left⟩).symm)
      (e₁.trans (hc.fac (BinaryCofan.mk s.inr s.inl) ⟨WalkingPair.right⟩).symm)

theorem BinaryCofan.isColimit_iff_isIso_inl {X Y : C} (h : IsInitial Y) (c : BinaryCofan X Y) :
    Nonempty (IsColimit c) ↔ IsIso c.inl := by
  constructor
  · rintro ⟨H⟩
    obtain ⟨l, hl, -⟩ := BinaryCofan.IsColimit.desc' H (𝟙 X) (h.to X)
    refine ⟨⟨l, hl, BinaryCofan.IsColimit.hom_ext H (?_) (h.hom_ext _ _)⟩⟩
    rw [Category.comp_id]
    have e : (inl c ≫ l) ≫ inl c = 𝟙 X ≫ inl c := congrArg (·≫inl c) hl
    rwa [Category.assoc,Category.id_comp] at e
  · intro
    exact
      ⟨BinaryCofan.IsColimit.mk _ (fun f _ => inv c.inl ≫ f)
          (fun _ _ => IsIso.hom_inv_id_assoc _ _) (fun _ _ => h.hom_ext _ _) fun _ _ _ e _ =>
          (IsIso.eq_inv_comp _).mpr e⟩

theorem BinaryCofan.isColimit_iff_isIso_inr {X Y : C} (h : IsInitial X) (c : BinaryCofan X Y) :
    Nonempty (IsColimit c) ↔ IsIso c.inr := by
  refine Iff.trans ?_ (BinaryCofan.isColimit_iff_isIso_inl h (BinaryCofan.mk c.inr c.inl))
  exact
    ⟨fun h => ⟨BinaryCofan.isColimitFlip h.some⟩, fun h =>
      ⟨(BinaryCofan.isColimitFlip h.some).ofIsoColimit (isoBinaryCofanMk c).symm⟩⟩

noncomputable def BinaryCofan.isColimitCompLeftIso {X Y X' : C} (c : BinaryCofan X Y) (f : X' ⟶ X)
    [IsIso f] (h : IsColimit c) : IsColimit (BinaryCofan.mk (f ≫ c.inl) c.inr) := by
  fapply BinaryCofan.isColimitMk
  · exact fun s => h.desc (BinaryCofan.mk (inv f ≫ s.inl) s.inr)
  · intro s
    -- Porting note: simp timed out here too
    simp only [IsColimit.fac,BinaryCofan.ι_app_left,eq_self_iff_true,
      Category.assoc,BinaryCofan.mk_inl,IsIso.hom_inv_id_assoc]
  · intro s
    -- Porting note: simp timed out here too
    simp only [IsColimit.fac,BinaryCofan.ι_app_right,eq_self_iff_true,BinaryCofan.mk_inr]
  · intro s m e₁ e₂
    apply BinaryCofan.IsColimit.hom_ext h
    · rw [← cancel_epi f]
    -- Porting note: simp timed out here too
      simpa only [IsColimit.fac,BinaryCofan.ι_app_left,eq_self_iff_true,
      Category.assoc,BinaryCofan.mk_inl,IsIso.hom_inv_id_assoc] using e₁
    -- Porting note: simp timed out here too
    · simpa only [IsColimit.fac,BinaryCofan.ι_app_right,eq_self_iff_true,BinaryCofan.mk_inr]

noncomputable def BinaryCofan.isColimitCompRightIso {X Y Y' : C} (c : BinaryCofan X Y) (f : Y' ⟶ Y)
    [IsIso f] (h : IsColimit c) : IsColimit (BinaryCofan.mk c.inl (f ≫ c.inr)) :=
  BinaryCofan.isColimitFlip <| BinaryCofan.isColimitCompLeftIso _ f (BinaryCofan.isColimitFlip h)

abbrev HasBinaryProduct (X Y : C) :=
  HasLimit (pair X Y)

abbrev HasBinaryCoproduct (X Y : C) :=
  HasColimit (pair X Y)

noncomputable abbrev prod (X Y : C) [HasBinaryProduct X Y] :=
  limit (pair X Y)

noncomputable abbrev coprod (X Y : C) [HasBinaryCoproduct X Y] :=
  colimit (pair X Y)

notation:20 X " ⨯ " Y:20 => prod X Y

notation:20 X " ⨿ " Y:20 => coprod X Y

noncomputable abbrev prod.fst {X Y : C} [HasBinaryProduct X Y] : X ⨯ Y ⟶ X :=
  limit.π (pair X Y) ⟨WalkingPair.left⟩

noncomputable abbrev prod.snd {X Y : C} [HasBinaryProduct X Y] : X ⨯ Y ⟶ Y :=
  limit.π (pair X Y) ⟨WalkingPair.right⟩

noncomputable abbrev coprod.inl {X Y : C} [HasBinaryCoproduct X Y] : X ⟶ X ⨿ Y :=
  colimit.ι (pair X Y) ⟨WalkingPair.left⟩

noncomputable abbrev coprod.inr {X Y : C} [HasBinaryCoproduct X Y] : Y ⟶ X ⨿ Y :=
  colimit.ι (pair X Y) ⟨WalkingPair.right⟩

noncomputable def prodIsProd (X Y : C) [HasBinaryProduct X Y] :
    IsLimit (BinaryFan.mk (prod.fst : X ⨯ Y ⟶ X) prod.snd) :=
  (limit.isLimit _).ofIsoLimit (Cones.ext (Iso.refl _) (fun ⟨u⟩ => by
    cases u
    · dsimp; simp only [Category.id_comp]; rfl
    · dsimp; simp only [Category.id_comp]; rfl
  ))

noncomputable def coprodIsCoprod (X Y : C) [HasBinaryCoproduct X Y] :
    IsColimit (BinaryCofan.mk (coprod.inl : X ⟶ X ⨿ Y) coprod.inr) :=
  (colimit.isColimit _).ofIsoColimit (Cocones.ext (Iso.refl _) (fun ⟨u⟩ => by
    cases u
    · dsimp; simp only [Category.comp_id]
    · dsimp; simp only [Category.comp_id]
  ))

@[ext 1100]
theorem prod.hom_ext {W X Y : C} [HasBinaryProduct X Y] {f g : W ⟶ X ⨯ Y}
    (h₁ : f ≫ prod.fst = g ≫ prod.fst) (h₂ : f ≫ prod.snd = g ≫ prod.snd) : f = g :=
  BinaryFan.IsLimit.hom_ext (limit.isLimit _) h₁ h₂

@[ext 1100]
theorem coprod.hom_ext {W X Y : C} [HasBinaryCoproduct X Y] {f g : X ⨿ Y ⟶ W}
    (h₁ : coprod.inl ≫ f = coprod.inl ≫ g) (h₂ : coprod.inr ≫ f = coprod.inr ≫ g) : f = g :=
  BinaryCofan.IsColimit.hom_ext (colimit.isColimit _) h₁ h₂

noncomputable abbrev prod.lift {W X Y : C} [HasBinaryProduct X Y]
    (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ X ⨯ Y :=
  limit.lift _ (BinaryFan.mk f g)

noncomputable abbrev diag (X : C) [HasBinaryProduct X X] : X ⟶ X ⨯ X :=
  prod.lift (𝟙 _) (𝟙 _)

noncomputable abbrev coprod.desc {W X Y : C} [HasBinaryCoproduct X Y]
    (f : X ⟶ W) (g : Y ⟶ W) : X ⨿ Y ⟶ W :=
  colimit.desc _ (BinaryCofan.mk f g)

noncomputable abbrev codiag (X : C) [HasBinaryCoproduct X X] : X ⨿ X ⟶ X :=
  coprod.desc (𝟙 _) (𝟙 _)

@[reassoc]
theorem prod.lift_fst {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    prod.lift f g ≫ prod.fst = f :=
  limit.lift_π _ _

@[reassoc]
theorem prod.lift_snd {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    prod.lift f g ≫ prod.snd = g :=
  limit.lift_π _ _

@[reassoc]
theorem coprod.inl_desc {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    coprod.inl ≫ coprod.desc f g = f :=
  colimit.ι_desc _ _

@[reassoc]
theorem coprod.inr_desc {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    coprod.inr ≫ coprod.desc f g = g :=
  colimit.ι_desc _ _

instance prod.mono_lift_of_mono_left {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
    [Mono f] : Mono (prod.lift f g) :=
  mono_of_mono_fac <| prod.lift_fst _ _

instance prod.mono_lift_of_mono_right {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
    [Mono g] : Mono (prod.lift f g) :=
  mono_of_mono_fac <| prod.lift_snd _ _

instance coprod.epi_desc_of_epi_left {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
    [Epi f] : Epi (coprod.desc f g) :=
  epi_of_epi_fac <| coprod.inl_desc _ _

instance coprod.epi_desc_of_epi_right {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
    [Epi g] : Epi (coprod.desc f g) :=
  epi_of_epi_fac <| coprod.inr_desc _ _

noncomputable def prod.lift' {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    { l : W ⟶ X ⨯ Y // l ≫ prod.fst = f ∧ l ≫ prod.snd = g } :=
  ⟨prod.lift f g, prod.lift_fst _ _, prod.lift_snd _ _⟩

noncomputable def coprod.desc' {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    { l : X ⨿ Y ⟶ W // coprod.inl ≫ l = f ∧ coprod.inr ≫ l = g } :=
  ⟨coprod.desc f g, coprod.inl_desc _ _, coprod.inr_desc _ _⟩

noncomputable def prod.map {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z]
    (f : W ⟶ Y) (g : X ⟶ Z) : W ⨯ X ⟶ Y ⨯ Z :=
  limMap (mapPair f g)

noncomputable def coprod.map {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z]
    (f : W ⟶ Y) (g : X ⟶ Z) : W ⨿ X ⟶ Y ⨿ Z :=
  colimMap (mapPair f g)

noncomputable section ProdLemmas

@[reassoc, simp]
theorem prod.comp_lift {V W X Y : C} [HasBinaryProduct X Y] (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) :
    f ≫ prod.lift g h = prod.lift (f ≫ g) (f ≫ h) := by ext <;> simp

@[reassoc (attr := simp)]
theorem prod.map_fst {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : prod.map f g ≫ prod.fst = prod.fst ≫ f :=
  limMap_π _ _

@[reassoc (attr := simp)]
theorem prod.map_snd {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : prod.map f g ≫ prod.snd = prod.snd ≫ g :=
  limMap_π _ _

@[simp]
theorem prod.map_id_id {X Y : C} [HasBinaryProduct X Y] : prod.map (𝟙 X) (𝟙 Y) = 𝟙 _ := by
  ext <;> simp

@[simp]
theorem prod.lift_fst_snd {X Y : C} [HasBinaryProduct X Y] :
    prod.lift prod.fst prod.snd = 𝟙 (X ⨯ Y) := by ext <;> simp

@[reassoc (attr := simp)]
theorem prod.lift_map {V W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : V ⟶ W)
    (g : V ⟶ X) (h : W ⟶ Y) (k : X ⟶ Z) :
    prod.lift f g ≫ prod.map h k = prod.lift (f ≫ h) (g ≫ k) := by ext <;> simp

@[simp]
theorem prod.lift_fst_comp_snd_comp {W X Y Z : C} [HasBinaryProduct W Y] [HasBinaryProduct X Z]
    (g : W ⟶ X) (g' : Y ⟶ Z) : prod.lift (prod.fst ≫ g) (prod.snd ≫ g') = prod.map g g' := by
  rw [← prod.lift_map]
  simp

@[reassoc (attr := simp)]
theorem prod.map_map {A₁ A₂ A₃ B₁ B₂ B₃ : C} [HasBinaryProduct A₁ B₁] [HasBinaryProduct A₂ B₂]
    [HasBinaryProduct A₃ B₃] (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (h : A₂ ⟶ A₃) (k : B₂ ⟶ B₃) :
    prod.map f g ≫ prod.map h k = prod.map (f ≫ h) (g ≫ k) := by ext <;> simp

@[simps]
def prod.mapIso {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ≅ Y)
    (g : X ≅ Z) : W ⨯ X ≅ Y ⨯ Z where
  hom := prod.map f.hom g.hom
  inv := prod.map f.inv g.inv

instance isIso_prod {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) [IsIso f] [IsIso g] : IsIso (prod.map f g) :=
  (prod.mapIso (asIso f) (asIso g)).isIso_hom

instance prod.map_mono {C : Type*} [Category C] {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Mono f]
    [Mono g] [HasBinaryProduct W X] [HasBinaryProduct Y Z] : Mono (prod.map f g) :=
  ⟨fun i₁ i₂ h => by
    ext
    · rw [← cancel_mono f]
      simpa using congr_arg (fun f => f ≫ prod.fst) h
    · rw [← cancel_mono g]
      simpa using congr_arg (fun f => f ≫ prod.snd) h⟩

instance {X : C} [HasBinaryProduct X X] : IsSplitMono (diag X) :=
  IsSplitMono.mk' { retraction := prod.fst }

end ProdLemmas

noncomputable section CoprodLemmas

@[simp] -- Porting note: removing reassoc tag since result is not hygienic (two h's)
theorem coprod.desc_comp {V W X Y : C} [HasBinaryCoproduct X Y] (f : V ⟶ W) (g : X ⟶ V)
    (h : Y ⟶ V) : coprod.desc g h ≫ f = coprod.desc (g ≫ f) (h ≫ f) := by
  ext <;> simp

@[reassoc (attr := simp)]
theorem coprod.inl_map {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : coprod.inl ≫ coprod.map f g = f ≫ coprod.inl :=
  ι_colimMap _ _

@[reassoc (attr := simp)]
theorem coprod.inr_map {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : coprod.inr ≫ coprod.map f g = g ≫ coprod.inr :=
  ι_colimMap _ _

@[simp]
theorem coprod.map_id_id {X Y : C} [HasBinaryCoproduct X Y] : coprod.map (𝟙 X) (𝟙 Y) = 𝟙 _ := by
  ext <;> simp

@[simp]
theorem coprod.desc_inl_inr {X Y : C} [HasBinaryCoproduct X Y] :
    coprod.desc coprod.inl coprod.inr = 𝟙 (X ⨿ Y) := by ext <;> simp

@[reassoc, simp]
theorem coprod.map_desc {S T U V W : C} [HasBinaryCoproduct U W] [HasBinaryCoproduct T V]
    (f : U ⟶ S) (g : W ⟶ S) (h : T ⟶ U) (k : V ⟶ W) :
    coprod.map h k ≫ coprod.desc f g = coprod.desc (h ≫ f) (k ≫ g) := by
  ext <;> simp

@[simp]
theorem coprod.desc_comp_inl_comp_inr {W X Y Z : C} [HasBinaryCoproduct W Y]
    [HasBinaryCoproduct X Z] (g : W ⟶ X) (g' : Y ⟶ Z) :
    coprod.desc (g ≫ coprod.inl) (g' ≫ coprod.inr) = coprod.map g g' := by
  rw [← coprod.map_desc]; simp

@[reassoc (attr := simp)]
theorem coprod.map_map {A₁ A₂ A₃ B₁ B₂ B₃ : C} [HasBinaryCoproduct A₁ B₁] [HasBinaryCoproduct A₂ B₂]
    [HasBinaryCoproduct A₃ B₃] (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (h : A₂ ⟶ A₃) (k : B₂ ⟶ B₃) :
    coprod.map f g ≫ coprod.map h k = coprod.map (f ≫ h) (g ≫ k) := by
  ext <;> simp

@[simps]
def coprod.mapIso {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ≅ Y)
    (g : X ≅ Z) : W ⨿ X ≅ Y ⨿ Z where
  hom := coprod.map f.hom g.hom
  inv := coprod.map f.inv g.inv

instance isIso_coprod {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) [IsIso f] [IsIso g] : IsIso (coprod.map f g) :=
  (coprod.mapIso (asIso f) (asIso g)).isIso_hom

instance coprod.map_epi {C : Type*} [Category C] {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Epi f]
    [Epi g] [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] : Epi (coprod.map f g) :=
  ⟨fun i₁ i₂ h => by
    ext
    · rw [← cancel_epi f]
      simpa using congr_arg (fun f => coprod.inl ≫ f) h
    · rw [← cancel_epi g]
      simpa using congr_arg (fun f => coprod.inr ≫ f) h⟩

end CoprodLemmas

variable (C)

abbrev HasBinaryProducts :=
  HasLimitsOfShape (Discrete WalkingPair) C

abbrev HasBinaryCoproducts :=
  HasColimitsOfShape (Discrete WalkingPair) C

theorem hasBinaryProducts_of_hasLimit_pair [∀ {X Y : C}, HasLimit (pair X Y)] :
    HasBinaryProducts C :=
  { has_limit := fun F => hasLimitOfIso (diagramIsoPair F).symm }

theorem hasBinaryCoproducts_of_hasColimit_pair [∀ {X Y : C}, HasColimit (pair X Y)] :
    HasBinaryCoproducts C :=
  { has_colimit := fun F => hasColimitOfIso (diagramIsoPair F) }

noncomputable section

variable {C}

@[simps]
def prod.braiding (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P] : P ⨯ Q ≅ Q ⨯ P where
  hom := prod.lift prod.snd prod.fst
  inv := prod.lift prod.snd prod.fst

@[reassoc]
theorem prod.symmetry' (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P] :
    prod.lift prod.snd prod.fst ≫ prod.lift prod.snd prod.fst = 𝟙 (P ⨯ Q) :=
  (prod.braiding _ _).hom_inv_id

@[reassoc]
theorem prod.symmetry (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P] :
    (prod.braiding P Q).hom ≫ (prod.braiding Q P).hom = 𝟙 _ :=
  (prod.braiding _ _).hom_inv_id

@[simps]
def prod.associator [HasBinaryProducts C] (P Q R : C) : (P ⨯ Q) ⨯ R ≅ P ⨯ Q ⨯ R where
  hom := prod.lift (prod.fst ≫ prod.fst) (prod.lift (prod.fst ≫ prod.snd) prod.snd)
  inv := prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst)) (prod.snd ≫ prod.snd)

variable [HasTerminal C]

@[simps]
def prod.leftUnitor (P : C) [HasBinaryProduct (⊤_ C) P] : (⊤_ C) ⨯ P ≅ P where
  hom := prod.snd
  inv := prod.lift (terminal.from P) (𝟙 _)
  hom_inv_id := by apply prod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp

@[simps]
def prod.rightUnitor (P : C) [HasBinaryProduct P (⊤_ C)] : P ⨯ ⊤_ C ≅ P where
  hom := prod.fst
  inv := prod.lift (𝟙 _) (terminal.from P)
  hom_inv_id := by apply prod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp

@[reassoc]
theorem prod.leftUnitor_hom_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    prod.map (𝟙 _) f ≫ (prod.leftUnitor Y).hom = (prod.leftUnitor X).hom ≫ f :=
  prod.map_snd _ _

@[reassoc]
theorem prod.leftUnitor_inv_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    (prod.leftUnitor X).inv ≫ prod.map (𝟙 _) f = f ≫ (prod.leftUnitor Y).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, prod.leftUnitor_hom_naturality]

@[reassoc]
theorem prod.rightUnitor_hom_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    prod.map f (𝟙 _) ≫ (prod.rightUnitor Y).hom = (prod.rightUnitor X).hom ≫ f :=
  prod.map_fst _ _

@[reassoc]
theorem prod_rightUnitor_inv_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    (prod.rightUnitor X).inv ≫ prod.map f (𝟙 _) = f ≫ (prod.rightUnitor Y).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, prod.rightUnitor_hom_naturality]

theorem prod.triangle [HasBinaryProducts C] (X Y : C) :
    (prod.associator X (⊤_ C) Y).hom ≫ prod.map (𝟙 X) (prod.leftUnitor Y).hom =
      prod.map (prod.rightUnitor X).hom (𝟙 Y) := by
  ext <;> simp

end

noncomputable section

variable {C}

variable [HasBinaryCoproducts C]

@[simps]
def coprod.braiding (P Q : C) : P ⨿ Q ≅ Q ⨿ P where
  hom := coprod.desc coprod.inr coprod.inl
  inv := coprod.desc coprod.inr coprod.inl

@[reassoc]
theorem coprod.symmetry' (P Q : C) :
    coprod.desc coprod.inr coprod.inl ≫ coprod.desc coprod.inr coprod.inl = 𝟙 (P ⨿ Q) :=
  (coprod.braiding _ _).hom_inv_id

theorem coprod.symmetry (P Q : C) : (coprod.braiding P Q).hom ≫ (coprod.braiding Q P).hom = 𝟙 _ :=
  coprod.symmetry' _ _

@[simps]
def coprod.associator (P Q R : C) : (P ⨿ Q) ⨿ R ≅ P ⨿ Q ⨿ R where
  hom := coprod.desc (coprod.desc coprod.inl (coprod.inl ≫ coprod.inr)) (coprod.inr ≫ coprod.inr)
  inv := coprod.desc (coprod.inl ≫ coprod.inl) (coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr)

variable [HasInitial C]

@[simps]
def coprod.leftUnitor (P : C) : (⊥_ C) ⨿ P ≅ P where
  hom := coprod.desc (initial.to P) (𝟙 _)
  inv := coprod.inr
  hom_inv_id := by apply coprod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp

@[simps]
def coprod.rightUnitor (P : C) : P ⨿ ⊥_ C ≅ P where
  hom := coprod.desc (𝟙 _) (initial.to P)
  inv := coprod.inl
  hom_inv_id := by apply coprod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp

theorem coprod.triangle (X Y : C) :
    (coprod.associator X (⊥_ C) Y).hom ≫ coprod.map (𝟙 X) (coprod.leftUnitor Y).hom =
      coprod.map (coprod.rightUnitor X).hom (𝟙 Y) := by
  ext <;> simp

end

noncomputable section ProdFunctor

variable {C} [Category.{v} C] [HasBinaryProducts C]

@[simps]
def prod.functor : C ⥤ C ⥤ C where
  obj X :=
    { obj := fun Y => X ⨯ Y
      map := fun {_ _} => prod.map (𝟙 X) }
  map f :=
    { app := fun T => prod.map f (𝟙 T) }

def prod.functorLeftComp (X Y : C) :
    prod.functor.obj (X ⨯ Y) ≅ prod.functor.obj Y ⋙ prod.functor.obj X :=
  NatIso.ofComponents (prod.associator _ _)

end ProdFunctor

noncomputable section CoprodFunctor

variable {C} [Category.{v} C] [HasBinaryCoproducts C]

@[simps]
def coprod.functor : C ⥤ C ⥤ C where
  obj X :=
    { obj := fun Y => X ⨿ Y
      map := fun {_ _} => coprod.map (𝟙 X) }
  map f := { app := fun T => coprod.map f (𝟙 T) }

def coprod.functorLeftComp (X Y : C) :
    coprod.functor.obj (X ⨿ Y) ≅ coprod.functor.obj Y ⋙ coprod.functor.obj X :=
  NatIso.ofComponents (coprod.associator _ _)

end CoprodFunctor

noncomputable section ProdComparison

universe w w' u₃

variable {C} {D : Type u₂} [Category.{w} D] {E : Type u₃} [Category.{w'} E]

variable (F : C ⥤ D) (G : D ⥤ E) {A A' B B' : C}

variable [HasBinaryProduct A B] [HasBinaryProduct A' B']

variable [HasBinaryProduct (F.obj A) (F.obj B)]

variable [HasBinaryProduct (F.obj A') (F.obj B')]

variable [HasBinaryProduct (G.obj (F.obj A)) (G.obj (F.obj B))]

variable [HasBinaryProduct ((F ⋙ G).obj A) ((F ⋙ G).obj B)]

def prodComparison (F : C ⥤ D) (A B : C) [HasBinaryProduct A B]
    [HasBinaryProduct (F.obj A) (F.obj B)] : F.obj (A ⨯ B) ⟶ F.obj A ⨯ F.obj B :=
  prod.lift (F.map prod.fst) (F.map prod.snd)

variable (A B)

@[reassoc (attr := simp)]
theorem prodComparison_fst : prodComparison F A B ≫ prod.fst = F.map prod.fst :=
  prod.lift_fst _ _

@[reassoc (attr := simp)]
theorem prodComparison_snd : prodComparison F A B ≫ prod.snd = F.map prod.snd :=
  prod.lift_snd _ _

variable {A B}

@[reassoc]
theorem prodComparison_natural (f : A ⟶ A') (g : B ⟶ B') :
    F.map (prod.map f g) ≫ prodComparison F A' B' =
      prodComparison F A B ≫ prod.map (F.map f) (F.map g) := by
  rw [prodComparison, prodComparison, prod.lift_map, ← F.map_comp, ← F.map_comp, prod.comp_lift, ←
    F.map_comp, prod.map_fst, ← F.map_comp, prod.map_snd]

@[simps]
def prodComparisonNatTrans [HasBinaryProducts C] [HasBinaryProducts D] (F : C ⥤ D) (A : C) :
    prod.functor.obj A ⋙ F ⟶ F ⋙ prod.functor.obj (F.obj A) where
  app B := prodComparison F A B
  naturality f := by simp [prodComparison_natural]

@[reassoc]
theorem inv_prodComparison_map_fst [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map prod.fst = prod.fst := by simp [IsIso.inv_comp_eq]

@[reassoc]
theorem inv_prodComparison_map_snd [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map prod.snd = prod.snd := by simp [IsIso.inv_comp_eq]

@[reassoc]
theorem prodComparison_inv_natural (f : A ⟶ A') (g : B ⟶ B') [IsIso (prodComparison F A B)]
    [IsIso (prodComparison F A' B')] :
    inv (prodComparison F A B) ≫ F.map (prod.map f g) =
      prod.map (F.map f) (F.map g) ≫ inv (prodComparison F A' B') := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq, prodComparison_natural]

@[simps]
def prodComparisonNatIso [HasBinaryProducts C] [HasBinaryProducts D] (A : C)
    [∀ B, IsIso (prodComparison F A B)] :
    prod.functor.obj A ⋙ F ≅ F ⋙ prod.functor.obj (F.obj A) := by
  refine { @asIso _ _ _ _ _ (?_) with hom := prodComparisonNatTrans F A }
  apply NatIso.isIso_of_isIso_app

theorem prodComparison_comp :
    prodComparison (F ⋙ G) A B =
      G.map (prodComparison F A B) ≫ prodComparison G (F.obj A) (F.obj B) := by
  unfold prodComparison
  ext <;> simp <;> rw [← G.map_comp] <;> simp

end ProdComparison

noncomputable section CoprodComparison

universe w

variable {C} {D : Type u₂} [Category.{w} D]

variable (F : C ⥤ D) {A A' B B' : C}

variable [HasBinaryCoproduct A B] [HasBinaryCoproduct A' B']

variable [HasBinaryCoproduct (F.obj A) (F.obj B)] [HasBinaryCoproduct (F.obj A') (F.obj B')]

def coprodComparison (F : C ⥤ D) (A B : C) [HasBinaryCoproduct A B]
    [HasBinaryCoproduct (F.obj A) (F.obj B)] : F.obj A ⨿ F.obj B ⟶ F.obj (A ⨿ B) :=
  coprod.desc (F.map coprod.inl) (F.map coprod.inr)

@[reassoc (attr := simp)]
theorem coprodComparison_inl : coprod.inl ≫ coprodComparison F A B = F.map coprod.inl :=
  coprod.inl_desc _ _

@[reassoc (attr := simp)]
theorem coprodComparison_inr : coprod.inr ≫ coprodComparison F A B = F.map coprod.inr :=
  coprod.inr_desc _ _

@[reassoc]
theorem coprodComparison_natural (f : A ⟶ A') (g : B ⟶ B') :
    coprodComparison F A B ≫ F.map (coprod.map f g) =
      coprod.map (F.map f) (F.map g) ≫ coprodComparison F A' B' := by
  rw [coprodComparison, coprodComparison, coprod.map_desc, ← F.map_comp, ← F.map_comp,
    coprod.desc_comp, ← F.map_comp, coprod.inl_map, ← F.map_comp, coprod.inr_map]

@[simps]
def coprodComparisonNatTrans [HasBinaryCoproducts C] [HasBinaryCoproducts D] (F : C ⥤ D) (A : C) :
    F ⋙ coprod.functor.obj (F.obj A) ⟶ coprod.functor.obj A ⋙ F where
  app B := coprodComparison F A B
  naturality f := by simp [coprodComparison_natural]

@[reassoc]
theorem map_inl_inv_coprodComparison [IsIso (coprodComparison F A B)] :
    F.map coprod.inl ≫ inv (coprodComparison F A B) = coprod.inl := by simp [IsIso.inv_comp_eq]

@[reassoc]
theorem map_inr_inv_coprodComparison [IsIso (coprodComparison F A B)] :
    F.map coprod.inr ≫ inv (coprodComparison F A B) = coprod.inr := by simp [IsIso.inv_comp_eq]

@[reassoc]
theorem coprodComparison_inv_natural (f : A ⟶ A') (g : B ⟶ B') [IsIso (coprodComparison F A B)]
    [IsIso (coprodComparison F A' B')] :
    inv (coprodComparison F A B) ≫ coprod.map (F.map f) (F.map g) =
      F.map (coprod.map f g) ≫ inv (coprodComparison F A' B') := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq, coprodComparison_natural]

@[simps]
def coprodComparisonNatIso [HasBinaryCoproducts C] [HasBinaryCoproducts D] (A : C)
    [∀ B, IsIso (coprodComparison F A B)] :
    F ⋙ coprod.functor.obj (F.obj A) ≅ coprod.functor.obj A ⋙ F := by
  refine { @asIso _ _ _ _ _ (?_) with hom := coprodComparisonNatTrans F A }
  apply NatIso.isIso_of_isIso_app -- Porting note: this did not work inside { }

end CoprodComparison

end CategoryTheory.Limits

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

@[simps]
noncomputable def Over.coprodObj [HasBinaryCoproducts C] {A : C} :
    Over A → Over A ⥤ Over A :=
  fun f =>
  { obj := fun g => Over.mk (coprod.desc f.hom g.hom)
    map := fun k => Over.homMk (coprod.map (𝟙 _) k.left) }

@[simps]
noncomputable def Over.coprod [HasBinaryCoproducts C] {A : C} : Over A ⥤ Over A ⥤ Over A where
  obj f := Over.coprodObj f
  map k :=
    { app := fun g => Over.homMk (coprod.map k.left (𝟙 _)) (by
        dsimp; rw [coprod.map_desc, Category.id_comp, Over.w k])
      naturality := fun f g k => by
        ext
        dsimp; simp }
  map_id X := by
    ext
    dsimp; simp
  map_comp f g := by
    ext
    dsimp; simp

end CategoryTheory
