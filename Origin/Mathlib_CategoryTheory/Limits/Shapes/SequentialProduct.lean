/-
Extracted from CategoryTheory/Limits/Shapes/SequentialProduct.lean
Genuine: 10 of 11 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# ℕ-indexed products as sequential limits

Given sequences `M N : ℕ → C` of objects with morphisms `f n : M n ⟶ N n` for all `n`, this file
exhibits `∏ M` as the limit of the tower

```
⋯ → ∏_{n < m + 1} M n × ∏_{n ≥ m + 1} N n → ∏_{n < m} M n × ∏_{n ≥ m} N n → ⋯ → ∏ N
```

Further, we prove that the transition maps in this tower are epimorphisms, in the case when each
`f n` is an epimorphism and `C` has finite biproducts.
-/

namespace CategoryTheory.Limits.SequentialProduct

variable {C : Type*} {M N : ℕ → C}

lemma functorObj_eq_pos {n m : ℕ} (h : m < n) :
    (fun i ↦ if _ : i < n then M i else N i) m = M m := dif_pos h

lemma functorObj_eq_neg {n m : ℕ} (h : ¬(m < n)) :
    (fun i ↦ if _ : i < n then M i else N i) m = N m := dif_neg h

variable [Category* C] (f : ∀ n, M n ⟶ N n) [HasCountableProducts C]

variable (M N) in

noncomputable def functorObj : ℕ → C :=
  fun n ↦ ∏ᶜ (fun m ↦ if _ : m < n then M m else N m)

noncomputable def functorObjProj_pos (n m : ℕ) (h : m < n) :
    functorObj M N n ⟶ M m :=
  Pi.π (fun m ↦ if _ : m < n then M m else N m) m ≫ eqToHom (functorObj_eq_pos (by lia))

noncomputable def functorObjProj_neg (n m : ℕ) (h : ¬(m < n)) :
    functorObj M N n ⟶ N m :=
  Pi.π (fun m ↦ if _ : m < n then M m else N m) m ≫ eqToHom (functorObj_eq_neg (by lia))

noncomputable def functorMap : ∀ n,
    functorObj M N (n + 1) ⟶ functorObj M N n := by
  intro n
  refine Limits.Pi.map fun m ↦ if h : m < n then eqToHom ?_ else
    if h' : m < n + 1 then eqToHom ?_ ≫ f m ≫ eqToHom ?_ else eqToHom ?_
  all_goals split_ifs; try rfl; try lia

set_option backward.isDefEq.respectTransparency false in

lemma functorMap_commSq_succ (n : ℕ) :
    (Functor.ofOpSequence (functorMap f)).map (homOfLE (by lia : n ≤ n + 1)).op ≫ Pi.π _ n ≫
      eqToHom (functorObj_eq_neg (by lia : ¬(n < n))) =
        (Pi.π (fun i ↦ if _ : i < (n + 1) then M i else N i) n) ≫
          eqToHom (functorObj_eq_pos (by lia)) ≫ f n := by
  simp [functorMap]

set_option backward.isDefEq.respectTransparency false in

lemma functorMap_commSq_aux {n m k : ℕ} (h : n ≤ m) (hh : ¬(k < m)) :
    (Functor.ofOpSequence (functorMap f)).map (homOfLE h).op ≫ Pi.π _ k ≫
      eqToHom (functorObj_eq_neg (by lia : ¬(k < n))) =
        (Pi.π (fun i ↦ if _ : i < m then M i else N i) k) ≫
          eqToHom (functorObj_eq_neg hh) := by
  induction h using Nat.leRec with
  | refl => simp
  | @le_succ_of_le m h ih =>
    specialize ih (by lia)
    have : homOfLE (by lia : n ≤ m + 1) =
        homOfLE (by lia : n ≤ m) ≫ homOfLE (by lia : m ≤ m + 1) := by simp
    rw [this, op_comp, Functor.map_comp]
    slice_lhs 2 4 => rw [ih]
    simp only [Functor.ofOpSequence_obj, homOfLE_leOfHom, Functor.ofOpSequence_map_homOfLE_succ,
      functorMap, dite_eq_ite, limMap_π_assoc, Discrete.functor_obj_eq_as, Discrete.natTrans_app]
    split_ifs
    simp [dif_neg (by lia : ¬(k < m))]

set_option backward.isDefEq.respectTransparency false in

lemma functorMap_commSq {n m : ℕ} (h : ¬(m < n)) :
    (Functor.ofOpSequence (functorMap f)).map (homOfLE (by lia : n ≤ m + 1)).op ≫ Pi.π _ m ≫
      eqToHom (functorObj_eq_neg (by lia : ¬(m < n))) =
        (Pi.π (fun i ↦ if _ : i < m + 1 then M i else N i) m) ≫
          eqToHom (functorObj_eq_pos (by lia)) ≫ f m := by
  cases m with
  | zero =>
      have : n = 0 := by lia
      subst this
      simp [functorMap]
  | succ m =>
      rw [← functorMap_commSq_succ f (m + 1)]
      simp only [Functor.ofOpSequence_obj, homOfLE_leOfHom, dite_eq_ite,
        Functor.ofOpSequence_map_homOfLE_succ]
      have : homOfLE (by lia : n ≤ m + 1 + 1) =
          homOfLE (by lia : n ≤ m + 1) ≫ homOfLE (by lia : m + 1 ≤ m + 1 + 1) := by simp
      rw [this, op_comp, Functor.map_comp]
      simp only [Functor.ofOpSequence_obj, homOfLE_leOfHom, Functor.ofOpSequence_map_homOfLE_succ,
        Category.assoc]
      congr 1
      exact functorMap_commSq_aux f (by lia) (by lia)

set_option backward.isDefEq.respectTransparency false in

noncomputable def cone : Cone (Functor.ofOpSequence (functorMap f)) where
  pt := ∏ᶜ M
  π := by
    refine NatTrans.ofOpSequence
      (fun n ↦ Limits.Pi.map fun m ↦ if h : m < n then eqToHom (functorObj_eq_pos h).symm else
        f m ≫ eqToHom (functorObj_eq_neg h).symm) (fun n ↦ ?_)
    apply Limits.Pi.hom_ext
    intro m
    simp only [Functor.const_obj_obj, Functor.ofOpSequence_obj, homOfLE_leOfHom,
      Functor.const_obj_map, Category.id_comp, limMap_π, Discrete.functor_obj_eq_as,
      Discrete.natTrans_app, Functor.ofOpSequence_map_homOfLE_succ, functorMap, Category.assoc,
      limMap_π_assoc]
    split
    · simp [dif_pos (by lia : m < n + 1)]
    · split
      all_goals simp

set_option backward.isDefEq.respectTransparency false in
