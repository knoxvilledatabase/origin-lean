/-
Extracted from CategoryTheory/Functor/OfSequence.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Functors from the category of the ordered set `ℕ`

In this file, we provide a constructor `Functor.ofSequence`
for functors `ℕ ⥤ C` which takes as an input a sequence
of morphisms `f : X n ⟶ X (n + 1)` for all `n : ℕ`.

We also provide a constructor `NatTrans.ofSequence` for natural
transformations between functors `ℕ ⥤ C` which allows to check
the naturality condition only for morphisms `n ⟶ n + 1`.

The duals of the above for functors `ℕᵒᵖ ⥤ C` are given by `Functor.ofOpSequence` and
`NatTrans.ofOpSequence`.

-/

namespace CategoryTheory

open Category

variable {C : Type*} [Category* C]

namespace Functor

variable {X : ℕ → C} (f : ∀ n, X n ⟶ X (n + 1))

namespace OfSequence

lemma congr_f (i j : ℕ) (h : i = j) :
    f i = eqToHom (by rw [h]) ≫ f j ≫ eqToHom (by rw [h]) := by
  subst h
  simp

def map : ∀ {X : ℕ → C} (_ : ∀ n, X n ⟶ X (n + 1)) (i j : ℕ), i ≤ j → (X i ⟶ X j)
  | _, _, 0, 0 => fun _ ↦ 𝟙 _
  | _, f, 0, 1 => fun _ ↦ f 0
  | _, f, 0, l + 1 => fun _ ↦ f 0 ≫ map (fun n ↦ f (n + 1)) 0 l (by lia)
  | _, _, _ + 1, 0 => nofun
  | _, f, k + 1, l + 1 => fun _ ↦ map (fun n ↦ f (n + 1)) k l (by lia)

lemma map_id (i : ℕ) : map f i i (by lia) = 𝟙 _ := by
  revert X f
  induction i with
  | zero => intros; rfl
  | succ _ hi =>
      intro X f
      apply hi

lemma map_le_succ (i : ℕ) : map f i (i + 1) (by lia) = f i := by
  revert X f
  induction i with
  | zero => intros; rfl
  | succ _ hi =>
      intro X f
      apply hi
