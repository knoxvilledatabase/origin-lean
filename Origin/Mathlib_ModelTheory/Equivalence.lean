/-
Extracted from ModelTheory/Equivalence.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Equivalence of Formulas

## Main Definitions
- `FirstOrder.Language.Theory.Imp`: `φ ⟹[T] ψ` indicates that `φ` implies `ψ` in models of `T`.
- `FirstOrder.Language.Theory.Iff`: `φ ⇔[T] ψ` indicates that `φ` and `ψ` are equivalent formulas or
  sentences in models of `T`.

## TODO
- Define the quotient of `L.Formula α` modulo `⇔[T]` and its Boolean Algebra structure.

-/

universe u v w w'

open Cardinal CategoryTheory

open FirstOrder

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {T : L.Theory} {α : Type w} {n : ℕ}

variable {M : Type*} [Nonempty M] [L.Structure M] [M ⊨ T]

namespace Theory

protected def Imp (T : L.Theory) (φ ψ : L.BoundedFormula α n) : Prop :=
  T ⊨ᵇ φ.imp ψ
