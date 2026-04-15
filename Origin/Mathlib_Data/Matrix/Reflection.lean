/-
Extracted from Data/Matrix/Reflection.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lemmas for concrete matrices `Matrix (Fin m) (Fin n) α`

This file contains alternative definitions of common operators on matrices that expand
definitionally to the expected expression when evaluated on `!![]` notation.

This allows "proof by reflection", where we prove `A = !![A 0 0, A 0 1;  A 1 0, A 1 1]` by defining
`Matrix.etaExpand A` to be equal to the RHS definitionally, and then prove that
`A = eta_expand A`.

The definitions in this file should normally not be used directly; the intent is for the
corresponding `*_eq` lemmas to be used in a place where they are definitionally unfolded.

## Main definitions

* `Matrix.transposeᵣ`
* `dotProductᵣ`
* `Matrix.mulᵣ`
* `Matrix.mulVecᵣ`
* `Matrix.vecMulᵣ`
* `Matrix.etaExpand`

-/

open Matrix

namespace Matrix

variable {l m n : ℕ} {α : Type*}

def Forall : ∀ {m n} (_ : Matrix (Fin m) (Fin n) α → Prop), Prop
  | 0, _, P => P (of ![])
  | _ + 1, _, P => FinVec.Forall fun r => Forall fun A => P (of (Matrix.vecCons r A))

theorem forall_iff : ∀ {m n} (P : Matrix (Fin m) (Fin n) α → Prop), Forall P ↔ ∀ x, P x
  | 0, _, _ => Iff.symm Fin.forall_fin_zero_pi
  | m + 1, n, P => by
    simp only [Forall, FinVec.forall_iff, forall_iff]
    exact Iff.symm Fin.forall_fin_succ_pi

example (P : Matrix (Fin 2) (Fin 3) α → Prop) :

    (∀ x, P x) ↔ ∀ a b c d e f, P !![a, b, c; d, e, f] :=

  (forall_iff _).symm

def Exists : ∀ {m n} (_ : Matrix (Fin m) (Fin n) α → Prop), Prop
  | 0, _, P => P (of ![])
  | _ + 1, _, P => FinVec.Exists fun r => Exists fun A => P (of (Matrix.vecCons r A))

theorem exists_iff : ∀ {m n} (P : Matrix (Fin m) (Fin n) α → Prop), Exists P ↔ ∃ x, P x
  | 0, _, _ => Iff.symm Fin.exists_fin_zero_pi
  | m + 1, n, P => by
    simp only [Exists, FinVec.exists_iff, exists_iff]
    exact Iff.symm Fin.exists_fin_succ_pi

example (P : Matrix (Fin 2) (Fin 3) α → Prop) :

    (∃ x, P x) ↔ ∃ a b c d e f, P !![a, b, c; d, e, f] :=

  (exists_iff _).symm

def transposeᵣ : ∀ {m n}, Matrix (Fin m) (Fin n) α → Matrix (Fin n) (Fin m) α
  | _, 0, _ => of ![]
  | _, _ + 1, A =>
    of <| vecCons (FinVec.map (fun v : Fin _ → α => v 0) A) (transposeᵣ (A.submatrix id Fin.succ))
