/-
Extracted from Data/QPF/Multivariate/Constructions/Sigma.lean
Genuine: 8 of 14 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Dependent product and sum of QPFs are QPFs
-/

universe u

namespace MvQPF

open MvFunctor

variable {n : ℕ} {A : Type u}

variable (F : A → TypeVec.{u} n → Type u)

def Sigma (v : TypeVec.{u} n) : Type u :=
  Σ α : A, F α v

def Pi (v : TypeVec.{u} n) : Type u :=
  ∀ α : A, F α v

-- INSTANCE (free from Core): Sigma.inhabited

-- INSTANCE (free from Core): Pi.inhabited

namespace Sigma

-- INSTANCE (free from Core): [∀

variable [∀ α, MvQPF <| F α]

protected def P : MvPFunctor n :=
  ⟨Σ a, (P (F a)).A, fun x => (P (F x.1)).B x.2⟩

protected def abs ⦃α⦄ : Sigma.P F α → Sigma F α
  | ⟨a, f⟩ => ⟨a.1, MvQPF.abs ⟨a.2, f⟩⟩

protected def repr ⦃α⦄ : Sigma F α → Sigma.P F α
  | ⟨a, f⟩ =>
    let x := MvQPF.repr f
    ⟨⟨a, x.1⟩, x.2⟩

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): :

end Sigma

namespace Pi

-- INSTANCE (free from Core): [∀

variable [∀ α, MvQPF <| F α]

protected def P : MvPFunctor n :=
  ⟨∀ a, (P (F a)).A, fun x i => Σ a, (P (F a)).B (x a) i⟩

protected def abs ⦃α⦄ : Pi.P F α → Pi F α
  | ⟨a, f⟩ => fun x => MvQPF.abs ⟨a x, fun i y => f i ⟨_, y⟩⟩

protected def repr ⦃α⦄ : Pi F α → Pi.P F α
  | f => ⟨fun a => (MvQPF.repr (f a)).1, fun _i a => (MvQPF.repr (f _)).2 _ a.2⟩

-- INSTANCE (free from Core): :

end Pi

end MvQPF
