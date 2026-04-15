/-
Extracted from Data/QPF/Multivariate/Constructions/Comp.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The composition of QPFs is itself a QPF

We define composition between one `n`-ary functor and `n` `m`-ary functors
and show that it preserves the QPF structure
-/

universe u

namespace MvQPF

open MvFunctor

variable {n m : ℕ} (F : TypeVec.{u} n → Type*) (G : Fin2 n → TypeVec.{u} m → Type u)

def Comp (v : TypeVec.{u} m) : Type _ :=
  F fun i : Fin2 n ↦ G i v

namespace Comp

open MvPFunctor

variable {F G} {α β : TypeVec.{u} m} (f : α ⟹ β)

-- INSTANCE (free from Core): [I

protected def mk (x : F fun i ↦ G i α) : Comp F G α := x

protected def get (x : Comp F G α) : F fun i ↦ G i α := x
