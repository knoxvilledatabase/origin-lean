/-
Extracted from Data/UInt.lean
Genuine: 7 of 8 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Adds Mathlib specific instances to the `UIntX` data types.

The `CommRing` instances (and the `NatCast` and `IntCast` instances from which they is built) are
scoped in the `UIntX.CommRing` namespace, rather than available globally. As a result, the `ring`
tactic will not work on `UIntX` types without `open scoped UIntX.Ring`.

This is because the presence of these casting operations contradicts assumptions made by the
expression tree elaborator, namely that coercions do not form a cycle.

The UInt
version also interferes more with software-verification use-cases, which is reason to be more
cautious here.
-/

set_option linter.style.emptyLine false in

set_option hygiene false in

run_cmd

  for typeName' in [`UInt8, `UInt16, `UInt32, `UInt64, `USize] do

  let typeName := Lean.mkIdent typeName'

  Lean.Elab.Command.elabCommand (← `(

    namespace $typeName

      open $typeName (toBitVec_mul) in

set_option linter.style.emptyLine false in

set_option hygiene false in

run_cmd

  for typeName' in [`UInt8, `UInt16, `UInt32, `UInt64, `USize] do

  let typeName := Lean.mkIdent typeName'

  Lean.Elab.Command.elabCommand (← `(

    namespace $typeName

      open $typeName (eq_of_toFin_eq) in

      lemma toFin_injective : Function.Injective toFin := @eq_of_toFin_eq

      open $typeName (eq_of_toBitVec_eq) in
      lemma toBitVec_injective : Function.Injective toBitVec := @eq_of_toBitVec_eq

      open $typeName (toBitVec_one toBitVec_mul toBitVec_pow) in
      instance instCommMonoid : CommMonoid $typeName :=
        Function.Injective.commMonoid toBitVec toBitVec_injective
          toBitVec_one (fun _ _ => toBitVec_mul) (fun _ _ => toBitVec_pow _ _)

      open $typeName (
        toBitVec_zero toBitVec_add toBitVec_mul toBitVec_neg toBitVec_sub toBitVec_nsmul
        toBitVec_zsmul) in
      instance instNonUnitalCommRing : NonUnitalCommRing $typeName :=
        Function.Injective.nonUnitalCommRing toBitVec toBitVec_injective
          toBitVec_zero (fun _ _ => toBitVec_add) (fun _ _ => toBitVec_mul) (fun _ => toBitVec_neg)
          (fun _ _ => toBitVec_sub)
          (fun _ _ => toBitVec_nsmul _ _) (fun _ _ => toBitVec_zsmul _ _)

      attribute [local instance] intCast natCast

      open $typeName (
        toBitVec_zero toBitVec_one toBitVec_add toBitVec_mul toBitVec_neg
        toBitVec_sub toBitVec_nsmul toBitVec_zsmul toBitVec_pow
        toBitVec_natCast toBitVec_intCast) in
      -- `noncomputable` should not be necessary but triggers some codegen assertion
      noncomputable local instance instCommRing : CommRing $typeName :=
        Function.Injective.commRing toBitVec toBitVec_injective
          toBitVec_zero toBitVec_one (fun _ _ => toBitVec_add) (fun _ _ => toBitVec_mul)
          (fun _ => toBitVec_neg) (fun _ _ => toBitVec_sub)
          (fun _ _ => toBitVec_nsmul _ _) (fun _ _ => toBitVec_zsmul _ _)
          (fun _ _ => toBitVec_pow _ _)
          toBitVec_natCast toBitVec_intCast

      namespace CommRing
      attribute [scoped instance] instCommRing natCast intCast
      end CommRing

    end $typeName
  ))
  -- interpolating docstrings above is more trouble than it's worth
  let docString :=
    s!"To use this instance, use `open scoped {typeName'}.CommRing`.\n\n" ++
    "See the module docstring for an explanation"
  Lean.addDocStringCore (typeName'.mkStr "instCommRing") docString
  -- TODO: add these docstrings in core?
  -- Lean.addDocStringCore (typeName'.mkStr "instNatCast") docString
  -- Lean.addDocStringCore (typeName'.mkStr "instIntCast") docString

namespace UInt8

def isASCIIUpper (c : UInt8) : Bool :=
  c ≥ 65 && c ≤ 90

def isASCIILower (c : UInt8) : Bool :=
  c ≥ 97 && c ≤ 122

def isASCIIAlpha (c : UInt8) : Bool :=
  c.isASCIIUpper || c.isASCIILower

def isASCIIDigit (c : UInt8) : Bool :=
  c ≥ 48 && c ≤ 57

def isASCIIAlphanum (c : UInt8) : Bool :=
  c.isASCIIAlpha || c.isASCIIDigit

def toChar (n : UInt8) : Char := ⟨n.toUInt32, .inl (Nat.lt_trans n.toBitVec.isLt (by decide))⟩

end UInt8
