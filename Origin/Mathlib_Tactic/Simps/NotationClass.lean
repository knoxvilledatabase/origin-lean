/-
Extracted from Tactic/Simps/NotationClass.lean
Genuine: 11 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init
import Lean.Elab.Exception
import Batteries.Lean.NameMapAttribute
import Batteries.Tactic.Lint

/-!
# `@[notation_class]` attribute for `@[simps]`

This declares the `@[notation_class]` attribute, which is used to give smarter default projections
for `@[simps]`.

We put this in a separate file so that we can already tag some declarations with this attribute
in the file where we declare `@[simps]`. For further documentation, see `Tactic.Simps.Basic`.
-/

syntax (name := notation_class) "notation_class" "*"? (ppSpace ident)? (ppSpace ident)? : attr

open Lean Meta Elab Term

namespace Simps

def findArgType : Type := Name → Name → Array Expr → MetaM (Array (Option Expr))

def defaultfindArgs : findArgType := fun _ className args ↦ do
  let some classExpr := (← getEnv).find? className | throwError "no such class {className}"
  let arity := classExpr.type.getNumHeadForalls
  if arity == args.size then
    return args.map some
  else if args.size == 1 then
    return mkArray arity args[0]!
  else
    throwError "initialize_simps_projections cannot automatically find arguments for class \
      {className}"

def copyFirst : findArgType := fun _ _ args ↦ return (args.push <| args[0]?.getD default).map some

def copySecond : findArgType := fun _ _ args ↦ return (args.push <| args[1]?.getD default).map some

def nsmulArgs : findArgType := fun _ _ args ↦
  return #[Expr.const `Nat [], args[0]?.getD default] ++ args |>.map some

def zsmulArgs : findArgType := fun _ _ args ↦
  return #[Expr.const `Int [], args[0]?.getD default] ++ args |>.map some

def findZeroArgs : findArgType := fun _ _ args ↦
  return #[some <| args[0]?.getD default, some <| mkRawNatLit 0]

def findOneArgs : findArgType := fun _ _ args ↦
  return #[some <| args[0]?.getD default, some <| mkRawNatLit 1]

def findCoercionArgs : findArgType := fun str className args ↦ do
  let some classExpr := (← getEnv).find? className | throwError "no such class {className}"
  let arity := classExpr.type.getNumHeadForalls
  let eStr := mkAppN (← mkConstWithLevelParams str) args
  let classArgs := mkArray (arity - 1) none
  return #[some eStr] ++ classArgs

structure AutomaticProjectionData where
  /-- `className` is the name of the class we are looking for. -/
  className : Name
  /-- `isNotation` is a boolean that specifies whether this is notation
    (false for the coercions `DFunLike` and `SetLike`). If this is set to true, we add the current
    class as hypothesis during type-class synthesis. -/
  isNotation := true
  /-- The method to find the arguments of the class. -/
  findArgs : Name := `Simps.defaultfindArgs

deriving Inhabited

initialize notationClassAttr : NameMapExtension AutomaticProjectionData ← do

  let ext ← registerNameMapExtension AutomaticProjectionData

  registerBuiltinAttribute {

    name := `notation_class

    descr := "An attribute specifying that this is a notation class. Used by @[simps]."

    add := fun src stx _kind => do

      unless isStructure (← getEnv) src do

        throwError "@[notation_class] attribute can only be added to classes."

      match stx with

      | `(attr|notation_class $[*%$coercion]? $[$projName?]? $[$findArgs?]?) => do
        let projName ← match projName? with
          | none => pure (getStructureFields (← getEnv) src)[0]!
          | some projName => pure projName.getId
        let findArgs := if findArgs?.isSome then findArgs?.get!.getId else `Simps.defaultfindArgs
        match (← getEnv).find? findArgs with
        | none => throwError "no such declaration {findArgs}"
        | some declInfo =>
          unless ← MetaM.run' <| isDefEq declInfo.type (mkConst ``findArgType) do
            throwError "declaration {findArgs} has wrong type"
        ext.add projName ⟨src, coercion.isNone, findArgs⟩
      | _ => throwUnsupportedSyntax }
  return ext

end Simps
