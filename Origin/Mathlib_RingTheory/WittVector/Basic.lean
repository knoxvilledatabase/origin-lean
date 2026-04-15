/-
Extracted from RingTheory/WittVector/Basic.lean
Genuine: 15 of 15 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Witt vectors

This file verifies that the ring operations on `WittVector p R`
satisfy the axioms of a commutative ring.

## Main definitions

* `WittVector.map`: lifts a ring homomorphism `R →+* S` to a ring homomorphism `𝕎 R →+* 𝕎 S`.
* `WittVector.ghostComponent n x`: evaluates the `n`th Witt polynomial
  on the first `n` coefficients of `x`, producing a value in `R`.
  This is a ring homomorphism.
* `WittVector.ghostMap`: a ring homomorphism `𝕎 R →+* (ℕ → R)`, obtained by packaging
  all the ghost components together.
  If `p` is invertible in `R`, then the ghost map is an equivalence,
  which we use to define the ring operations on `𝕎 R`.
* `WittVector.CommRing`: the ring structure induced by the ghost components.

## Notation

We use notation `𝕎 R`, entered `\bbW`, for the Witt vectors over `R`.

## Implementation details

As we prove that the ghost components respect the ring operations, we face a number of repetitive
proofs. To avoid duplicating code we factor these proofs into a custom tactic, only slightly more
powerful than a tactic macro. This tactic is not particularly useful outside of its applications
in this file.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]

-/

noncomputable section

open MvPolynomial Function

variable {p : ℕ} {R S : Type*} [CommRing R] [CommRing S]

variable {α : Type*} {β : Type*}

local notation "𝕎" => WittVector p

local notation "W_" => wittPolynomial p

open scoped Witt

namespace WittVector

def mapFun (f : α → β) : 𝕎 α → 𝕎 β := fun x => mk _ (f ∘ x.coeff)

namespace mapFun

theorem injective (f : α → β) (hf : Injective f) : Injective (mapFun f : 𝕎 α → 𝕎 β) :=
  fun _ _ h => ext fun n => hf (congr_arg (fun x => coeff x n) h :)

theorem surjective (f : α → β) (hf : Surjective f) : Surjective (mapFun f : 𝕎 α → 𝕎 β) := fun x =>
  ⟨mk _ fun n => Classical.choose <| hf <| x.coeff n,
    by ext n; simp only [mapFun, coeff_mk, comp_apply, Classical.choose_spec (hf (x.coeff n))]⟩

macro "map_fun_tac" : tactic => `(tactic| (

  ext n

  simp only [mapFun, mk, comp_apply, zero_coeff, map_zero,

    add_coeff, sub_coeff, mul_coeff, neg_coeff, nsmul_coeff, zsmul_coeff, pow_coeff,

    peval, map_aeval, algebraMap_int_eq, coe_eval₂Hom] <;>

  try { cases n <;> simp <;> done } <;> -- this line solves `one`

  apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl <;>

  ext ⟨i, k⟩ <;>

    fin_cases i <;> rfl))

variable [Fact p.Prime]

variable (f : R →+* S) (x y : WittVector p R)

theorem zero : mapFun f (0 : 𝕎 R) = 0 := by map_fun_tac

theorem one : mapFun f (1 : 𝕎 R) = 1 := by map_fun_tac

theorem add : mapFun f (x + y) = mapFun f x + mapFun f y := by map_fun_tac

theorem sub : mapFun f (x - y) = mapFun f x - mapFun f y := by map_fun_tac

theorem mul : mapFun f (x * y) = mapFun f x * mapFun f y := by map_fun_tac

theorem neg : mapFun f (-x) = -mapFun f x := by map_fun_tac

theorem nsmul (n : ℕ) (x : WittVector p R) : mapFun f (n • x) = n • mapFun f x := by map_fun_tac

theorem zsmul (z : ℤ) (x : WittVector p R) : mapFun f (z • x) = z • mapFun f x := by map_fun_tac

theorem pow (n : ℕ) : mapFun f (x ^ n) = mapFun f x ^ n := by map_fun_tac

theorem natCast (n : ℕ) : mapFun f (n : 𝕎 R) = n :=
  show mapFun f n.unaryCast = (n : WittVector p S) by
    induction n <;> simp [*, Nat.unaryCast, add, one, zero] <;> rfl

theorem intCast (n : ℤ) : mapFun f (n : 𝕎 R) = n :=
  show mapFun f n.castDef = (n : WittVector p S) by
    cases n <;> simp [*, Int.castDef, neg, natCast] <;> rfl

end mapFun

end WittVector

namespace WittVector

set_option backward.privateInPublic true in

private def ghostFun : 𝕎 R → ℕ → R := fun x n => aeval x.coeff (W_ ℤ n)

section Tactic

open Lean Elab Tactic

elab "ghost_fun_tac " φ:term ", " fn:term : tactic => do

  evalTactic (← `(tactic| (

  ext n

  have := congr_fun (congr_arg (@peval R _ _) (wittStructureInt_prop p $φ n)) $fn

  simp only [wittZero, OfNat.ofNat, Zero.zero, wittOne, One.one,

    HAdd.hAdd, Add.add, HSub.hSub, Sub.sub, Neg.neg, HMul.hMul, Mul.mul, HPow.hPow, Pow.pow,

    wittNSMul, wittZSMul, HSMul.hSMul, SMul.smul]

  simpa +unfoldPartialApp [WittVector.ghostFun, aeval_rename, aeval_bind₁,

    comp, uncurry, peval, eval] using this

  )))

end Tactic

section GhostFun
