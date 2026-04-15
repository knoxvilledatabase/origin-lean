/-
Extracted from Algebra/Ring/Hom/InjSurj.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Pulling back rings along injective maps, and pushing them forward along surjective maps
-/

open Function

variable {α β : Type*}

protected theorem Function.Injective.isDomain [Semiring α] [IsDomain α] [Semiring β] {F}
    [FunLike F β α] [MonoidWithZeroHomClass F β α] (f : F) (hf : Injective f) : IsDomain β where
  __ := domain_nontrivial f (map_zero _) (map_one _)
  __ := hf.isCancelMulZero f (map_zero _) (map_mul _)
