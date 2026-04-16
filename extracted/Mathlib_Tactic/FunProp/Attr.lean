/-
Extracted from Tactic/FunProp/Attr.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Tactic.FunProp.Decl
import Mathlib.Tactic.FunProp.Theorems

noncomputable section

/-!
## `funProp` attribute
-/

namespace Mathlib

open Lean Meta

namespace Meta.FunProp

private def funPropHelpString : String :=

"`fun_prop` tactic to prove function properties like `Continuous`, `Differentiable`, `IsLinearMap`"

initialize funPropAttr : Unit ←

  registerBuiltinAttribute {

    name  := `fun_prop

    descr := funPropHelpString

    applicationTime := AttributeApplicationTime.afterCompilation

    add   := fun declName _stx attrKind =>

       discard <| MetaM.run do

       let info ← getConstInfo declName

       forallTelescope info.type fun _ b => do

         if b.isProp then

           addFunPropDecl declName

         else

           addTheorem declName attrKind

    erase := fun _declName =>

      throwError "can't remove `funProp` attribute (not implemented yet)"

  }

end Meta.FunProp

end Mathlib
