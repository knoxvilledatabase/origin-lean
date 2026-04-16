/-
Extracted from CategoryTheory/SmallObject/Iteration/Basic.lean
Genuine: 16 | Conflates: 0 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.SuccPred.Limit

noncomputable section

/-! # Transfinite iterations of a functor

In this file, given a functor `Φ : C ⥤ C` and a natural transformation
`ε : 𝟭 C ⟶ Φ`, we shall define the transfinite iterations of `Φ` (TODO).

Given `j : J` where `J` is a well ordered set, we first introduce
a category `Iteration ε j`. An object in this category consists of
a functor `F : Set.Iic j ⥤ C ⥤ C` equipped with the data
which makes it the `i`th-iteration of `Φ` for all `i` such that `i ≤ j`.
Under suitable assumptions on `C`, we shall show that this category
`Iteration ε j` is equivalent to the punctual category (TODO).
In this file, we show that the there is at most one morphism between
two objects. In `SmallObject.Iteration.UniqueHom`, we shall show
that there does always exist a unique morphism between
two objects (TODO). Then, we shall show the existence of
an object (TODO). In these proofs, which are all done using
transfinite induction, we have to treat three cases separately:
* the case `j = ⊥`;
* the case `j` is a successor;
* the case `j` is a limit element.

-/

universe u

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category C] {Φ : C ⥤ C} (ε : 𝟭 C ⟶ Φ) {J : Type u}

namespace Functor

namespace Iteration

variable [Preorder J] {j : J} (F : Set.Iic j ⥤ C)

noncomputable abbrev mapSucc' [SuccOrder J] (i : J) (hi : i < j) :
    F.obj ⟨i, hi.le⟩ ⟶ F.obj ⟨Order.succ i, Order.succ_le_of_lt hi⟩ :=
  F.map <| homOfLE <| Subtype.mk_le_mk.2 <| Order.le_succ i

variable {i : J} (hi : i ≤ j)

def restrictionLT : Set.Iio i ⥤ C :=
  (monotone_inclusion_lt_le_of_le hi).functor ⋙ F

@[simps]
def coconeOfLE : Cocone (restrictionLT F hi) where
  pt := F.obj ⟨i, hi⟩
  ι :=
    { app := fun ⟨k, hk⟩ => F.map (homOfLE (by simpa using hk.le))
      naturality := fun ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ _ => by
        simp [comp_id, ← Functor.map_comp, homOfLE_comp] }

def restrictionLE : Set.Iic i ⥤ C :=
  (monotone_inclusion_le_le_of_le hi).functor ⋙ F

end Iteration

structure Iteration [Preorder J] [OrderBot J] [SuccOrder J] (j : J) where
  /-- The data of all `i`th iterations for `i : J` such that `i ≤ j`. -/
  F : Set.Iic j ⥤ C ⥤ C
  /-- The zeroth iteration is the identity functor. -/
  isoZero : F.obj ⟨⊥, bot_le⟩ ≅ 𝟭 C
  /-- The iteration on a successor element is obtained by composition of
  the previous iteration with `Φ`. -/
  isoSucc (i : J) (hi : i < j) : F.obj ⟨Order.succ i, Order.succ_le_of_lt hi⟩ ≅ F.obj ⟨i, hi.le⟩ ⋙ Φ
  /-- The natural map from an iteration to its successor is induced by `ε`. -/
  mapSucc'_eq (i : J) (hi : i < j) :
    Iteration.mapSucc' F i hi = whiskerLeft _ ε ≫ (isoSucc i hi).inv
  /-- If `i` is a limit element, the `i`th iteration is the colimit
  of `k`th iterations for `k < i`. -/
  isColimit (i : J) (hi : Order.IsSuccLimit i) (hij : i ≤ j) :
    IsColimit (Iteration.coconeOfLE F hij)

namespace Iteration

variable {ε}

variable {j : J}

section

variable [Preorder J] [OrderBot J] [SuccOrder J] (iter : Φ.Iteration ε j)

noncomputable abbrev mapSucc (i : J) (hi : i < j) :
    iter.F.obj ⟨i, hi.le⟩ ⟶ iter.F.obj ⟨Order.succ i, Order.succ_le_of_lt hi⟩ :=
  mapSucc' iter.F i hi

lemma mapSucc_eq (i : J) (hi : i < j) :
    iter.mapSucc i hi = whiskerLeft _ ε ≫ (iter.isoSucc i hi).inv :=
  iter.mapSucc'_eq _ hi

end

section

variable [Preorder J] [OrderBot J] [SuccOrder J] (iter₁ iter₂ : Φ.Iteration ε j)

structure Hom where
  /-- A natural transformation `iter₁.F ⟶ iter₂.F` -/
  natTrans : iter₁.F ⟶ iter₂.F
  natTrans_app_zero :
    natTrans.app ⟨⊥, bot_le⟩ = iter₁.isoZero.hom ≫ iter₂.isoZero.inv := by aesop_cat
  natTrans_app_succ (i : J) (hi : i < j) :
    natTrans.app ⟨Order.succ i, Order.succ_le_of_lt hi⟩ = (iter₁.isoSucc i hi).hom ≫
      whiskerRight (natTrans.app ⟨i, hi.le⟩) _ ≫ (iter₂.isoSucc i hi).inv := by aesop_cat

namespace Hom

attribute [simp, reassoc] natTrans_app_zero

@[simps]
def id : Hom iter₁ iter₁ where
  natTrans := 𝟙 _

variable {iter₁ iter₂}

lemma ext' {f g : Hom iter₁ iter₂} (h : f.natTrans = g.natTrans) : f = g := by
  cases f
  cases g
  subst h
  rfl

attribute [local ext] ext'

@[simps]
def comp {iter₃ : Iteration ε j} (f : Hom iter₁ iter₂) (g : Hom iter₂ iter₃) :
    Hom iter₁ iter₃ where
  natTrans := f.natTrans ≫ g.natTrans
  natTrans_app_succ i hi := by simp [natTrans_app_succ _ _ hi]

instance : Category (Iteration ε j) where
  Hom := Hom
  id := id
  comp := comp

instance {J} {j : J} [PartialOrder J] [OrderBot J] [WellFoundedLT J] [SuccOrder J]
    {iter₁ iter₂ : Iteration ε j} :
    Subsingleton (iter₁ ⟶ iter₂) where
  allEq f g := by
    apply ext'
    suffices ∀ i hi, f.natTrans.app ⟨i, hi⟩ = g.natTrans.app ⟨i, hi⟩ by
      ext ⟨i, hi⟩ : 2
      apply this
    intro i
    induction i using SuccOrder.limitRecOn with
    | hm j H =>
      obtain rfl := H.eq_bot
      simp [natTrans_app_zero]
    | hs j H IH =>
      intro hj
      simp [Hom.natTrans_app_succ, IH, (Order.lt_succ_of_not_isMax H).trans_le hj]
    | hl j H IH =>
      refine fun hj ↦ (iter₁.isColimit j H hj).hom_ext ?_
      rintro ⟨k, hk⟩
      simp [IH k hk]

end Hom

variable {iter₁ iter₂}

@[reassoc]
lemma natTrans_naturality (φ : iter₁ ⟶ iter₂) (i₁ i₂ : J) (h : i₁ ≤ i₂) (h' : i₂ ≤ j) :
    iter₁.F.map (by exact homOfLE h) ≫ φ.natTrans.app ⟨i₂, h'⟩ =
      φ.natTrans.app ⟨i₁, h.trans h'⟩ ≫ iter₂.F.map (by exact homOfLE h) := by
  apply φ.natTrans.naturality

variable (ε) in

@[simps]
def eval {i : J} (hi : i ≤ j) : Iteration ε j ⥤ C ⥤ C where
  obj iter := iter.F.obj ⟨i, hi⟩
  map φ := φ.natTrans.app _

@[simps F isoZero isoSucc]
def trunc (iter : Iteration ε j) {i : J} (hi : i ≤ j) : Iteration ε i where
  F := restrictionLE iter.F hi
  isoZero := iter.isoZero
  isoSucc k hk := iter.isoSucc k (lt_of_lt_of_le hk hi)
  mapSucc'_eq k hk := iter.mapSucc'_eq k (lt_of_lt_of_le hk hi)
  isColimit k hk' hk := iter.isColimit k hk' (hk.trans hi)

variable (ε) in

@[simps obj]
def truncFunctor {i : J} (hi : i ≤ j) : Iteration ε j ⥤ Iteration ε i where
  obj iter := iter.trunc hi
  map {iter₁ iter₂} φ :=
    { natTrans := whiskerLeft _ φ.natTrans
      natTrans_app_succ := fun k hk => φ.natTrans_app_succ k (lt_of_lt_of_le hk hi) }

end

namespace Hom

variable [PartialOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {iter₁ iter₂ : Φ.Iteration ε j}

lemma congr_app (φ φ' : iter₁ ⟶ iter₂) (i : J) (hi : i ≤ j) :
    φ.natTrans.app ⟨i, hi⟩ = φ'.natTrans.app ⟨i, hi⟩ := by
  obtain rfl := Subsingleton.elim φ φ'
  rfl

end Hom

end Iteration

end Functor

end CategoryTheory
