/-
Extracted from Algebra/FreeMonoid/Count.lean
Genuine: 9 | Conflates: 0 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.TypeTags.Hom

noncomputable section

/-!
# `List.count` as a bundled homomorphism

In this file we define `FreeMonoid.countP`, `FreeMonoid.count`, `FreeAddMonoid.countP`, and
`FreeAddMonoid.count`. These are `List.countP` and `List.count` bundled as multiplicative and
additive homomorphisms from `FreeMonoid` and `FreeAddMonoid`.

We do not use `to_additive` because it can't map `Multiplicative ℕ` to `ℕ`.
-/

variable {α : Type*} (p : α → Prop) [DecidablePred p]

namespace FreeAddMonoid

def countP : FreeAddMonoid α →+ ℕ where
  toFun := List.countP p
  map_zero' := List.countP_nil _
  map_add' := List.countP_append _

theorem countP_of (x : α) : countP p (of x) = if p x = true then 1 else 0 := by
  simp [countP, List.countP, List.countP.go]

def count [DecidableEq α] (x : α) : FreeAddMonoid α →+ ℕ := countP (· = x)

theorem count_of [DecidableEq α] (x y : α) : count x (of y) = (Pi.single x 1 : α → ℕ) y := by
  simp [Pi.single, Function.update, count, countP, List.countP, List.countP.go,
    Bool.beq_eq_decide_eq]

end FreeAddMonoid

namespace FreeMonoid

def countP : FreeMonoid α →* Multiplicative ℕ :=
    AddMonoidHom.toMultiplicative (FreeAddMonoid.countP p)

theorem countP_of' (x : α) :
    countP p (of x) = if p x then Multiplicative.ofAdd 1 else Multiplicative.ofAdd 0 := by
    erw [FreeAddMonoid.countP_of]
    simp only [eq_iff_iff, iff_true, ofAdd_zero]; rfl

theorem countP_of (x : α) : countP p (of x) = if p x then Multiplicative.ofAdd 1 else 1 := by
  rw [countP_of', ofAdd_zero]

def count [DecidableEq α] (x : α) : FreeMonoid α →* Multiplicative ℕ := countP (· = x)

theorem count_of [DecidableEq α] (x y : α) :
    count x (of y) = @Pi.mulSingle α (fun _ => Multiplicative ℕ) _ _ x (Multiplicative.ofAdd 1) y :=
  by simp [count, countP_of, Pi.mulSingle_apply, eq_comm, Bool.beq_eq_decide_eq]

end FreeMonoid
