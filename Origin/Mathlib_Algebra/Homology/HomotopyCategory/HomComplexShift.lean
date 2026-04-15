/-
Extracted from Algebra/Homology/HomotopyCategory/HomComplexShift.lean
Genuine: 11 of 11 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! Shifting cochains

Let `C` be a preadditive category. Given two cochain complexes (indexed by `ℤ`),
the type of cochains `HomComplex.Cochain K L n` of degree `n` was introduced
in `Mathlib/Algebra/Homology/HomotopyCategory/HomComplex.lean`. In this file, we
study how these cochains behave with respect to the shift on the complexes `K`
and `L`.

When `n`, `a`, `n'` are integers such that `h : n' + a = n`,
we obtain `rightShiftAddEquiv K L n a n' h : Cochain K L n ≃+ Cochain K (L⟦a⟧) n'`.
This definition does not involve signs, but the analogous definition
of `leftShiftAddEquiv K L n a n' h' : Cochain K L n ≃+ Cochain (K⟦a⟧) L n'`
when `h' : n + a = n'` does involve signs, as we follow the conventions
appearing in the introduction of
[Brian Conrad's book *Grothendieck duality and base change*][conrad2000].

## References
* [Brian Conrad, Grothendieck duality and base change][conrad2000]

-/

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

namespace CochainComplex.HomComplex

namespace Cochain

variable (γ γ₁ γ₂ : Cochain K L n)

def rightShift (a n' : ℤ) (hn' : n' + a = n) : Cochain K (L⟦a⟧) n' :=
  Cochain.mk (fun p q hpq => γ.v p (p + n) rfl ≫
    (L.shiftFunctorObjXIso a q (p + n) (by lia)).inv)

set_option backward.isDefEq.respectTransparency false in

lemma rightShift_v (a n' : ℤ) (hn' : n' + a = n) (p q : ℤ) (hpq : p + n' = q)
    (p' : ℤ) (hp' : p + n = p') :
    (γ.rightShift a n' hn').v p q hpq = γ.v p p' hp' ≫
      (L.shiftFunctorObjXIso a q p' (by rw [← hp', ← hpq, ← hn', add_assoc])).inv := by
  subst hp'
  dsimp only [rightShift]
  simp only [mk_v]

def leftShift (a n' : ℤ) (hn' : n + a = n') : Cochain (K⟦a⟧) L n' :=
  Cochain.mk (fun p q hpq => (a * n' + ((a * (a - 1)) / 2)).negOnePow •
    (K.shiftFunctorObjXIso a p (p + a) rfl).hom ≫ γ.v (p + a) q (by lia))

lemma leftShift_v (a n' : ℤ) (hn' : n + a = n') (p q : ℤ) (hpq : p + n' = q)
    (p' : ℤ) (hp' : p' + n = q) :
    (γ.leftShift a n' hn').v p q hpq = (a * n' + ((a * (a - 1)) / 2)).negOnePow •
      (K.shiftFunctorObjXIso a p p'
        (by rw [← add_left_inj n, hp', add_assoc, add_comm a, hn', hpq])).hom ≫ γ.v p' q hp' := by
  obtain rfl : p' = p + a := by lia
  dsimp only [leftShift]
  simp only [mk_v]

def rightUnshift {n' a : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n) :
    Cochain K L n :=
  Cochain.mk (fun p q hpq => γ.v p (p + n') rfl ≫
    (L.shiftFunctorObjXIso a (p + n') q (by rw [← hpq, add_assoc, hn])).hom)

lemma rightUnshift_v {n' a : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n)
    (p q : ℤ) (hpq : p + n = q) (p' : ℤ) (hp' : p + n' = p') :
    (γ.rightUnshift n hn).v p q hpq = γ.v p p' hp' ≫
      (L.shiftFunctorObjXIso a p' q (by rw [← hpq, ← hn, ← add_assoc, hp'])).hom := by
  subst hp'
  dsimp only [rightUnshift]
  simp only [mk_v]

def leftUnshift {n' a : ℤ} (γ : Cochain (K⟦a⟧) L n') (n : ℤ) (hn : n + a = n') :
    Cochain K L n :=
  Cochain.mk (fun p q hpq => (a * n' + ((a * (a - 1)) / 2)).negOnePow •
    (K.shiftFunctorObjXIso a (p - a) p (by lia)).inv ≫ γ.v (p - a) q (by lia))

lemma leftUnshift_v {n' a : ℤ} (γ : Cochain (K⟦a⟧) L n') (n : ℤ) (hn : n + a = n')
    (p q : ℤ) (hpq : p + n = q) (p' : ℤ) (hp' : p' + n' = q) :
    (γ.leftUnshift n hn).v p q hpq = (a * n' + ((a * (a - 1)) / 2)).negOnePow •
      (K.shiftFunctorObjXIso a p' p (by lia)).inv ≫ γ.v p' q (by lia) := by
  obtain rfl : p' = p - a := by lia
  rfl

def shift (a : ℤ) : Cochain (K⟦a⟧) (L⟦a⟧) n :=
  Cochain.mk (fun p q hpq => (K.shiftFunctorObjXIso a p _ rfl).hom ≫
    γ.v (p + a) (q + a) (by lia) ≫ (L.shiftFunctorObjXIso a q _ rfl).inv)

lemma shift_v (a : ℤ) (p q : ℤ) (hpq : p + n = q) (p' q' : ℤ)
    (hp' : p' = p + a) (hq' : q' = q + a) :
    (γ.shift a).v p q hpq = (K.shiftFunctorObjXIso a p p' hp').hom ≫
      γ.v p' q' (by rw [hp', hq', ← hpq, add_assoc, add_comm a, add_assoc]) ≫
      (L.shiftFunctorObjXIso a q q' hq').inv := by
  subst hp' hq'
  rfl

lemma shift_v' (a : ℤ) (p q : ℤ) (hpq : p + n = q) :
    (γ.shift a).v p q hpq = γ.v (p + a) (q + a) (by lia) := by
  simp only [shift_v γ a p q hpq _ _ rfl rfl, shiftFunctor_obj_X, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv, comp_id, id_comp]

set_option backward.isDefEq.respectTransparency false in
