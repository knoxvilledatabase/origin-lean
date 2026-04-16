/-
Extracted from CategoryTheory/SmallObject/Iteration/UniqueHom.lean
Genuine: 14 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.CategoryTheory.SmallObject.Iteration.Basic

noncomputable section

/-!
# Uniqueness of morphisms in the category of iterations of functors

Given a functor `Φ : C ⥤ C` and a natural transformation `ε : 𝟭 C ⟶ Φ`,
we show in this file that there exists a unique morphism
between two arbitrary objects in the category `Functor.Iteration ε j`
when `j : J` and `J` is a well orderered set.

-/

universe u

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category C] {Φ : C ⥤ C} {ε : 𝟭 C ⟶ Φ}
  {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J]

namespace Functor

namespace Iteration

namespace Hom

def mkOfBot (iter₁ iter₂ : Iteration ε (⊥ : J)) : iter₁ ⟶ iter₂ where
  natTrans :=
    { app := fun ⟨i, hi⟩ => eqToHom (by congr; simpa using hi) ≫ iter₁.isoZero.hom ≫
        iter₂.isoZero.inv ≫ eqToHom (by congr; symm; simpa using hi)
      naturality := fun ⟨i, hi⟩ ⟨k, hk⟩ φ => by
        obtain rfl : i = ⊥ := by simpa using hi
        obtain rfl : k = ⊥ := by simpa using hk
        obtain rfl : φ = 𝟙 _ := rfl
        simp }
  natTrans_app_succ i hi := by simp at hi

section

variable {i : J} {iter₁ iter₂ : Iteration ε (Order.succ i)}
  (hi : ¬IsMax i) (φ : iter₁.trunc (SuccOrder.le_succ i) ⟶ iter₂.trunc (SuccOrder.le_succ i))

noncomputable def mkOfSuccNatTransApp (k : J) (hk : k ≤ Order.succ i) :
    iter₁.F.obj ⟨k, hk⟩ ⟶ iter₂.F.obj ⟨k, hk⟩ :=
  if hk' : k = Order.succ i then
    eqToHom (by subst hk'; rfl) ≫ (iter₁.isoSucc i (Order.lt_succ_of_not_isMax hi)).hom ≫
      whiskerRight (φ.natTrans.app ⟨i, by simp⟩) _ ≫
      (iter₂.isoSucc i (Order.lt_succ_of_not_isMax hi)).inv ≫
      eqToHom (by subst hk'; rfl)
  else
    φ.natTrans.app ⟨k, Order.le_of_lt_succ (by
      obtain hk | rfl := hk.lt_or_eq
      · exact hk
      · tauto)⟩

lemma mkOfSuccNatTransApp_eq_of_le (k : J) (hk : k ≤ i) :
    mkOfSuccNatTransApp hi φ k (hk.trans (Order.le_succ i)) =
      φ.natTrans.app ⟨k, hk⟩ :=
  dif_neg (by rintro rfl; simpa using lt_of_le_of_lt hk (Order.lt_succ_of_not_isMax hi))

@[simp]
lemma mkOfSuccNatTransApp_succ_eq :
    mkOfSuccNatTransApp hi φ (Order.succ i) (by rfl) =
      (iter₁.isoSucc i (Order.lt_succ_of_not_isMax hi)).hom ≫
        whiskerRight (φ.natTrans.app ⟨i, by simp⟩) _ ≫
        (iter₂.isoSucc i (Order.lt_succ_of_not_isMax hi)).inv := by
  dsimp [mkOfSuccNatTransApp]
  rw [dif_pos rfl, comp_id, id_comp]

@[simps]
noncomputable def mkOfSuccNatTrans :
    iter₁.F ⟶ iter₂.F where
  app := fun ⟨k, hk⟩ => mkOfSuccNatTransApp hi φ k hk
  naturality := fun ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ f => by
    dsimp
    have hk : k₁ ≤ k₂ := leOfHom f
    obtain h₂ | rfl := hk₂.lt_or_eq
    · replace h₂ : k₂ ≤ i := Order.le_of_lt_succ h₂
      rw [mkOfSuccNatTransApp_eq_of_le hi φ k₂ h₂,
        mkOfSuccNatTransApp_eq_of_le hi φ k₁ (hk.trans h₂)]
      exact natTrans_naturality φ k₁ k₂ hk h₂
    · obtain h₁ | rfl := hk.lt_or_eq
      · have h₂ : k₁ ≤ i := Order.le_of_lt_succ h₁
        let f₁ : (⟨k₁, hk⟩ : { l | l ≤ Order.succ i}) ⟶
          ⟨i, Order.le_succ i⟩ := homOfLE h₂
        let f₂ : (⟨i, Order.le_succ i⟩ : Set.Iic (Order.succ i)) ⟶
          ⟨Order.succ i, by simp⟩ := homOfLE (Order.le_succ i)
        obtain rfl : f = f₁ ≫ f₂ := rfl
        rw [Functor.map_comp, Functor.map_comp, assoc,
          mkOfSuccNatTransApp_eq_of_le hi φ k₁ h₂]
        erw [← natTrans_naturality_assoc φ k₁ i h₂ (by rfl)]
        rw [mkOfSuccNatTransApp_succ_eq]
        dsimp
        have ha : iter₁.F.map f₂ = iter₁.mapSucc i (Order.lt_succ_of_not_isMax hi) := rfl
        have hb : iter₂.F.map f₂ = iter₂.mapSucc i (Order.lt_succ_of_not_isMax hi) := rfl
        rw [ha, hb]
        rw [iter₁.mapSucc_eq i, iter₂.mapSucc_eq i, assoc,
          Iso.inv_hom_id_assoc]
        ext X
        dsimp
        rw [← ε.naturality_assoc]
        rfl
      · obtain rfl : f = 𝟙 _ := rfl
        rw [Functor.map_id, Functor.map_id, id_comp, comp_id]

end

noncomputable def mkOfSucc
    {i : J} (iter₁ iter₂ : Iteration ε (Order.succ i)) (hi : ¬IsMax i)
    (φ : iter₁.trunc (SuccOrder.le_succ i) ⟶ iter₂.trunc (SuccOrder.le_succ i)) :
    iter₁ ⟶ iter₂ where
  natTrans := mkOfSuccNatTrans hi φ
  natTrans_app_zero := by
    dsimp
    rw [mkOfSuccNatTransApp_eq_of_le _ _ _ bot_le, φ.natTrans_app_zero]
    rfl
  natTrans_app_succ k hk := by
    obtain hk' | rfl := (Order.le_of_lt_succ hk).lt_or_eq
    · dsimp
      rw [mkOfSuccNatTransApp_eq_of_le hi φ k hk'.le,
        mkOfSuccNatTransApp_eq_of_le hi φ (Order.succ k) (Order.succ_le_of_lt hk'),
        φ.natTrans_app_succ _ hk']
      rfl
    · simp [mkOfSuccNatTransApp_eq_of_le hi φ k (by rfl)]

variable {j : J} {iter₁ iter₂ : Iteration ε j}

section

variable (φ : ∀ (i : J) (hi : i < j), iter₁.trunc hi.le ⟶ iter₂.trunc hi.le)
  [WellFoundedLT J] (hj : Order.IsSuccLimit j)

def mkOfLimitNatTransApp (i : J) (hi : i ≤ j) :
    iter₁.F.obj ⟨i, hi⟩ ⟶ iter₂.F.obj ⟨i, hi⟩ :=
  if h : i < j
    then
      (φ i h).natTrans.app ⟨i, by simp⟩
    else by
      obtain rfl : i = j := by
        obtain h' | rfl := hi.lt_or_eq
        · exfalso
          exact h h'
        · rfl
      exact (iter₁.isColimit i hj (by simp)).desc (Cocone.mk _
        { app := fun ⟨k, hk⟩ => (φ k hk).natTrans.app ⟨k, by simp⟩ ≫
            iter₂.F.map (homOfLE (by exact hk.le))
          naturality := fun ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ f => by
            have hf : k₁ ≤ k₂ := by simpa using leOfHom f
            dsimp
            rw [comp_id, congr_app (φ k₁ hk₁) ((truncFunctor ε hf).map (φ k₂ hk₂))]
            erw [natTrans_naturality_assoc (φ k₂ hk₂) k₁ k₂ hf (by rfl)]
            dsimp
            rw [← Functor.map_comp, homOfLE_comp] })

lemma mkOfLimitNatTransApp_eq_of_lt (i : J) (hi : i < j) :
    mkOfLimitNatTransApp φ hj i hi.le = (φ i hi).natTrans.app ⟨i, by simp⟩ :=
  dif_pos hi

lemma mkOfLimitNatTransApp_naturality_top (i : J) (hi : i < j) :
    iter₁.F.map (homOfLE (by simpa using hi.le) : ⟨i, hi.le⟩ ⟶ ⟨j, by simp⟩) ≫
      mkOfLimitNatTransApp φ hj j (by rfl) =
      mkOfLimitNatTransApp φ hj i hi.le ≫ iter₂.F.map (homOfLE (by simpa using hi.le)) := by
  rw [mkOfLimitNatTransApp_eq_of_lt φ hj i hi, mkOfLimitNatTransApp, dif_neg (by simp)]
  exact (iter₁.isColimit j hj (by rfl)).fac _ ⟨i, hi⟩

@[simps]
def mkOfLimitNatTrans : iter₁.F ⟶ iter₂.F where
  app := fun ⟨k, hk⟩ => mkOfLimitNatTransApp φ hj k hk
  naturality := fun ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ f => by
    have hk : k₁ ≤ k₂ := leOfHom f
    obtain h₂ | rfl := hk₂.lt_or_eq
    · dsimp
      rw [mkOfLimitNatTransApp_eq_of_lt _ hj k₂ h₂,
        mkOfLimitNatTransApp_eq_of_lt _ hj k₁ (lt_of_le_of_lt hk h₂),
        congr_app (φ k₁ (lt_of_le_of_lt hk h₂)) ((truncFunctor ε hk).map (φ k₂ h₂))]
      exact natTrans_naturality (φ k₂ h₂) k₁ k₂ hk (by rfl)
    · obtain h₁ | rfl := hk₁.lt_or_eq
      · exact mkOfLimitNatTransApp_naturality_top _ hj _ h₁
      · obtain rfl : f = 𝟙 _ := rfl
        simp only [map_id, id_comp, comp_id]

def mkOfLimit : iter₁ ⟶ iter₂ where
  natTrans := mkOfLimitNatTrans φ hj
  natTrans_app_zero := by
    simp [mkOfLimitNatTransApp_eq_of_lt φ _ ⊥ (by simpa only [bot_lt_iff_ne_bot] using hj.ne_bot)]
  natTrans_app_succ i h := by
    dsimp
    have h' := hj.succ_lt h
    rw [mkOfLimitNatTransApp_eq_of_lt φ hj _ h',
      (φ _ h').natTrans_app_succ i (Order.lt_succ_of_not_isMax (not_isMax_of_lt h)),
      mkOfLimitNatTransApp_eq_of_lt φ _ _ h,
      congr_app (φ i h) ((truncFunctor ε (Order.le_succ i)).map (φ (Order.succ i) h'))]
    dsimp

end

variable [WellFoundedLT J]

instance : Nonempty (iter₁ ⟶ iter₂) := by
  let P := fun (i : J) => ∀ (hi : i ≤ j),
    Nonempty ((truncFunctor ε hi).obj iter₁ ⟶ (truncFunctor ε hi).obj iter₂)
  suffices ∀ i, P i from this j (by rfl)
  intro i
  induction i using SuccOrder.limitRecOn with
  | hm i hi =>
    obtain rfl : i = ⊥ := by simpa using hi
    exact fun hi' ↦ ⟨Hom.mkOfBot _ _⟩
  | hs i hi hi' =>
    exact fun hi'' ↦ ⟨Hom.mkOfSucc _ _ hi (hi' ((Order.le_succ i).trans hi'')).some⟩
  | hl i hi hi' =>
    exact fun hi'' ↦ ⟨Hom.mkOfLimit (fun k hk ↦ (hi' k hk (hk.le.trans hi'')).some) hi⟩

noncomputable instance : Unique (iter₁ ⟶ iter₂) :=
  uniqueOfSubsingleton (Nonempty.some inferInstance)

end Hom

variable [WellFoundedLT J] {j : J} (iter₁ iter₂ iter₃ : Iteration ε j)

noncomputable def iso : iter₁ ≅ iter₂ where
  hom := default
  inv := default

@[simp]
lemma iso_refl : iso iter₁ iter₁ = Iso.refl _ := by aesop_cat

lemma iso_trans : iso iter₁ iter₂ ≪≫ iso iter₂ iter₃ = iso iter₁ iter₃ := by aesop_cat

end Iteration

end Functor

end CategoryTheory
