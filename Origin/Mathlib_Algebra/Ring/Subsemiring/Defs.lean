/-
Extracted from Algebra/Ring/Subsemiring/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bundled subsemirings

We define bundled subsemirings and some standard constructions: `subtype` and `inclusion`
ring homomorphisms.
-/

assert_not_exists RelIso

universe u v w

section AddSubmonoidWithOneClass

class AddSubmonoidWithOneClass (S : Type*) (R : outParam Type*) [AddMonoidWithOne R]
  [SetLike S R] : Prop extends AddSubmonoidClass S R, OneMemClass S R

variable {S R : Type*} [AddMonoidWithOne R] [SetLike S R] (s : S)
