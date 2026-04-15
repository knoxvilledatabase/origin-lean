/-
Extracted from Data/QPF/Multivariate/Constructions/Prj.lean
Genuine: 5 of 8 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
Projection functors are QPFs. The `n`-ary projection functors on `i` is an `n`-ary
functor `F` such that `F (α₀..αᵢ₋₁, αᵢ, αᵢ₊₁..αₙ₋₁) = αᵢ`
-/

universe u v

namespace MvQPF

open MvFunctor

variable {n : ℕ} (i : Fin2 n)

def Prj (v : TypeVec.{u} n) : Type u := v i

-- INSTANCE (free from Core): Prj.inhabited

def Prj.map ⦃α β : TypeVec n⦄ (f : α ⟹ β) : Prj i α → Prj i β := f _

-- INSTANCE (free from Core): Prj.mvfunctor

def Prj.P : MvPFunctor.{u} n where
  A := PUnit
  B _ j := ULift <| PLift <| i = j

def Prj.abs ⦃α : TypeVec n⦄ : Prj.P i α → Prj i α
  | ⟨_x, f⟩ => f _ ⟨⟨rfl⟩⟩

def Prj.repr ⦃α : TypeVec n⦄ : Prj i α → Prj.P i α := fun x : α i =>
  ⟨⟨⟩, fun j ⟨⟨h⟩⟩ => (h.rec x : α j)⟩

-- INSTANCE (free from Core): Prj.mvqpf

end MvQPF
