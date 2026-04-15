/-
Extracted from Algebra/Group/Nat/Hom.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Extensionality of monoid homs from `ℕ`
-/

assert_not_exists IsOrderedMonoid MonoidWithZero

open Additive Multiplicative

variable {M : Type*}

section AddMonoidHomClass

variable {A B F : Type*} [FunLike F ℕ A]

lemma ext_nat' [AddZeroClass A] [AddMonoidHomClass F ℕ A] (f g : F) (h : f 1 = g 1) : f = g :=
  DFunLike.ext f g <| by
    intro n
    induction n with
    | zero => simp_rw [map_zero f, map_zero g]
    | succ n ihn =>
      simp [h, ihn]
