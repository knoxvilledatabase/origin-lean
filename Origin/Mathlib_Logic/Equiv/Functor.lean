/-
Extracted from Logic/Equiv/Functor.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Functor and bifunctors can be applied to `Equiv`s.

We define
```lean
def Functor.mapEquiv (f : Type u → Type v) [Functor f] [LawfulFunctor f] :
    α ≃ β → f α ≃ f β
```
and
```lean
def Bifunctor.mapEquiv (F : Type u → Type v → Type w) [Bifunctor F] [LawfulBifunctor F] :
    α ≃ β → α' ≃ β' → F α α' ≃ F β β'
```
-/

universe u v w

variable {α β : Type u}

open Equiv

namespace Functor

variable (f : Type u → Type v) [Functor f] [LawfulFunctor f]

def mapEquiv (h : α ≃ β) : f α ≃ f β where
  toFun := map h
  invFun := map h.symm
  left_inv x := by simp [map_map]
  right_inv x := by simp [map_map]
