/-
Extracted from Logic/Function/FromTypes.lean
Genuine: 8 | Conflates: 0 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core
import Mathlib.Data.Fin.VecNotation

noncomputable section

/-! # Function types of a given heterogeneous arity

This provides `Function.FromTypes`, such that `FromTypes ![α, β] τ = α → β → τ`.
Note that it is often preferable to use `((i : Fin n) → p i) → τ` in place of `FromTypes p τ`.

## Main definitions

* `Function.FromTypes p τ`: `n`-ary function `p 0 → p 1 → ... → p (n - 1) → β`.
-/

universe u

namespace Function

open Matrix (vecCons vecHead vecTail vecEmpty)

def FromTypes : {n : ℕ} → (Fin n → Type u) → Type u → Type u
  | 0    , _, τ => τ
  | n + 1, p, τ => vecHead p → @FromTypes n (vecTail p) τ

theorem fromTypes_zero (p : Fin 0 → Type u) (τ : Type u) : FromTypes p τ = τ := rfl

theorem fromTypes_nil (τ : Type u) : FromTypes ![] τ = τ := fromTypes_zero ![] τ

theorem fromTypes_succ {n} (p : Fin (n + 1) → Type u) (τ : Type u) :
    FromTypes p τ = (vecHead p → FromTypes (vecTail p) τ) := rfl

theorem fromTypes_cons {n} (α : Type u) (p : Fin n → Type u) (τ : Type u) :
    FromTypes (vecCons α p) τ = (α → FromTypes p τ) := fromTypes_succ _ τ

@[simps!]
def fromTypes_zero_equiv (p : Fin 0 → Type u) (τ : Type u) :
    FromTypes p τ ≃ τ := Equiv.refl _

@[simps!]
def fromTypes_nil_equiv (τ : Type u) : FromTypes ![] τ ≃ τ :=
  fromTypes_zero_equiv ![] τ

@[simps!]
def fromTypes_succ_equiv {n} (p : Fin (n + 1) → Type u) (τ : Type u) :
    FromTypes p τ ≃ (vecHead p → FromTypes (vecTail p) τ) := Equiv.refl _

@[simps!]
def fromTypes_cons_equiv {n} (α : Type u) (p : Fin n → Type u) (τ : Type u) :
    FromTypes (vecCons α p) τ ≃ (α → FromTypes p τ) := fromTypes_succ_equiv _ _

namespace FromTypes

def const : {n : ℕ} → (p : Fin n → Type u) → {τ : Type u} → (t : τ) → FromTypes p τ
  | 0,     _, _, t => t
  | n + 1, p, τ, t => fun _ => @const n (vecTail p) τ t

@[simp]
theorem const_zero (p : Fin 0 → Type u) {τ : Type u} (t : τ) : const p t = t :=
  rfl

@[simp]
theorem const_succ {n} (p : Fin (n + 1) → Type u) {τ : Type u} (t : τ) :
    const p t = fun _ => const (vecTail p) t := rfl

instance inhabited {n} {p : Fin n → Type u} {τ} [Inhabited τ] :
    Inhabited (FromTypes p τ) := ⟨const p default⟩

end FromTypes

end Function
