/-
Extracted from Tactic/Algebraize.lean
Genuine: 5 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Algebra.Tower

noncomputable section

/-!

## Algebraize tactic

This file defines the `algebraize` tactic. The basic functionality of this tactic is to
automatically add `Algebra` instances given `RingHom`s. For example, `algebraize [f, g]` where
`f : A →+* B` and `g : B →+* C` are `RingHom`s, will add the instances `Algebra A B` and
`Algebra B C` corresponding to these `RingHom`s.

## Further functionality

When given a composition of `RingHom`s, e.g. `algebraize [g.comp f]`, the tactic will also try to
add the instance `IsScalarTower A B C` if possible.

After having added suitable `Algebra` and `IsScalarTower` instances, the tactic will search through
the local context for `RingHom` properties that can be converted to properties of the corresponding
`Algebra`. For example, given `f : A →+* B` and `hf : f.FiniteType`, then `algebraize [f]` will add
the instance `Algebra A B` and the corresponding property `Algebra.FiniteType A B`. The tactic knows
which `RingHom` properties have a corresponding `Algebra` property through the `algebraize`
attribute.

## Algebraize attribute

The `algebraize` attribute is used to tag `RingHom` properties that can be converted to `Algebra`
properties. It assumes that the tagged declaration has a name of the form `RingHom.Property` and
that the corresponding `Algebra` property has the name `Algebra.Property`.

If not, the `Name` of the corresponding algebra property can be provided as optional argument. The
specified declaration should be one of the following:

1. An inductive type (i.e. the `Algebra` property itself), in this case it is assumed that the
`RingHom` and the `Algebra` property are definitionally the same, and the tactic will construct the
`Algebra` property by giving the `RingHom` property as a term. Due to how this is peformed, we also
need to assume that the `Algebra` property can be constructed only from the homomorphism, so it can
not have any other explicit arguments.
2. A lemma (or constructor) proving the `Algebra` property from the `RingHom` property. In this case
it is assumed that the `RingHom` property is the final argument, and that no other explicit argument
is needed. The tactic then constructs the `Algebra` property by applying the lemma or constructor.

Here are three examples of properties tagged with the `algebraize` attribute:
```
@[algebraize]
def RingHom.FiniteType (f : A →+* B) : Prop :=
  @Algebra.FiniteType A B _ _ f.toAlgebra
```
An example when the `Name` is provided (as the `Algebra` does not have the expected name):
```
@[algebraize Module.Finite]
def RingHom.Finite (f : A →+* B) : Prop :=
  letI : Algebra A B := f.toAlgebra
  Module.Finite A B
```
An example with a constructor as parameter (as the two properties are not definitonally the same):
```
@[algebraize Algebra.Flat.out]
class RingHom.Flat {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) : Prop where
  out : f.toAlgebra.Flat := by infer_instance
```

## algebraize_only

To avoid searching through the local context and adding corresponding `Algebra` properties, use
`algebraize_only` which only adds `Algebra` and `IsScalarTower` instances.
-/

open Lean Elab Tactic Term Meta

namespace Lean.Attr

def algebraizeGetParam (thm : Name) (stx : Syntax) : AttrM Name := do
  match stx with
  | `(attr| algebraize $name:ident) => return name.getId
  /- If no argument is provided, assume `thm` is of the form `RingHom.Property`,
  and return `Algebra.Property` -/
  | `(attr| algebraize) =>
    match thm with
    | .str `RingHom t => return .str `Algebra t
    | _ =>
      throwError "theorem name must be of the form `RingHom.Property` if no argument is provided"
  | _ => throwError "unexpected algebraize argument"

initialize algebraizeAttr : ParametricAttribute Name ←

  registerParametricAttribute {

    name := `algebraize,

    descr :=

"Tag that lets the `algebraize` tactic know which `Algebra` property corresponds to this `RingHom`

property.",

    getParam := algebraizeGetParam }

end Lean.Attr

namespace Mathlib.Tactic

namespace Algebraize

def addAlgebraInstanceFromRingHom (f ft : Expr) : TacticM Unit := withMainContext do
  let (_, l) := ft.getAppFnArgs
  -- The type of the corresponding algebra instance
  let alg ← mkAppOptM ``Algebra #[l[0]!, l[1]!, none, none]
  -- If the instance already exists, we do not do anything
  unless (← synthInstance? alg).isSome do
  liftMetaTactic fun mvarid => do
    let nm ← mkFreshBinderNameForTactic `algInst
    let mvar ← mvarid.define nm alg (← mkAppM ``RingHom.toAlgebra #[f])
    let (_, mvar) ← mvar.intro1P
    return [mvar]

def addIsScalarTowerInstanceFromRingHomComp (fn : Expr) : TacticM Unit := withMainContext do
  let (_, l) := fn.getAppFnArgs
  let tower ← mkAppOptM ``IsScalarTower #[l[0]!, l[1]!, l[2]!, none, none, none]
  -- If the instance already exists, we do not do anything
  unless (← synthInstance? tower).isSome do
  liftMetaTactic fun mvarid => do
    let nm ← mkFreshBinderNameForTactic `scalarTowerInst
    let h ← mkFreshExprMVar (← mkAppM ``Eq #[
      ← mkAppOptM ``algebraMap #[l[0]!, l[2]!, none, none, none],
      ← mkAppM ``RingHom.comp #[
        ← mkAppOptM ``algebraMap #[l[1]!, l[2]!, none, none, none],
        ← mkAppOptM ``algebraMap #[l[0]!, l[1]!, none, none, none]]])
    -- Note: this could fail, but then `algebraize` will just continue, and won't add this instance
    h.mvarId!.refl
    let val ← mkAppOptM ``IsScalarTower.of_algebraMap_eq'
      #[l[0]!, l[1]!, l[2]!, none, none, none, none, none, none, h]
    let mvar ← mvarid.define nm tower val
    let (_, mvar) ← mvar.intro1P
    return [mvar]

def addProperties (t : Array Expr) : TacticM Unit := withMainContext do
  let ctx ← getLCtx
  ctx.forM fun decl => do
    if decl.isImplementationDetail then return
    let (nm, args) := decl.type.getAppFnArgs
    -- Check if the type of the current hypothesis has been tagged with the `algebraize` attribute
    match Attr.algebraizeAttr.getParam? (← getEnv) nm with
    -- If it has, `p` will either be the name of the corresponding `Algebra` property, or a
    -- lemma/constructor.
    | some p =>
      -- The last argument of the `RingHom` property is assumed to be `f`
      let f := args[args.size - 1]!
      -- Check that `f` appears in the list of functions given to `algebraize`
      if ¬ (← t.anyM (Meta.isDefEq · f)) then return

      let cinfo ← getConstInfo p
      let n ← getExpectedNumArgs cinfo.type
      let pargs := Array.mkArray n (none : Option Expr)
      /- If the attribute points to the corresponding `Algebra` property itself, we assume that it
      is definitionally the same as the `RingHom` property. Then, we just need to construct its type
      and the local declaration will already give a valid term. -/
      if cinfo.isInductive then
        let pargs := pargs.set! 0 args[0]!
        let pargs := pargs.set! 1 args[1]!
        let tp ← mkAppOptM p pargs -- This should be the type `Algebra.Property A B`
        unless (← synthInstance? tp).isSome do
        liftMetaTactic fun mvarid => do
          let nm ← mkFreshBinderNameForTactic `algebraizeInst
          let (_, mvar) ← mvarid.note nm decl.toExpr tp
          return [mvar]
      /- Otherwise, the attribute points to a lemma or a constructor for the `Algebra` property.
      In this case, we assume that the `RingHom` property is the last argument of the lemma or
      constructor (and that this is all we need to supply explicitly). -/
      else
        let pargs := pargs.set! (n - 1) decl.toExpr
        let val ← mkAppOptM p pargs
        let tp ← inferType val
        unless (← synthInstance? tp).isSome do
        liftMetaTactic fun mvarid => do
          let nm ← mkFreshBinderNameForTactic `algebraizeInst
          let (_, mvar) ← mvarid.note nm val
          return [mvar]
    | none => return

structure Config where
  /-- If true (default), the tactic will search the local context for `RingHom` properties
    that can be converted to `Algebra` properties. -/
  properties : Bool := true

deriving Inhabited

declare_config_elab elabAlgebraizeConfig Algebraize.Config

end Algebraize

open Algebraize Lean.Parser.Tactic

syntax algebraizeTermSeq := " [" withoutPosition(term,*,?) "]"

syntax "algebraize " optConfig (algebraizeTermSeq)? : tactic

elab_rules : tactic

  | `(tactic| algebraize $cfg:optConfig $args) => withMainContext do

    let cfg ← elabAlgebraizeConfig cfg

    let t ← match args with

    | `(algebraizeTermSeq| [$rs,*]) => rs.getElems.mapM fun i => Term.elabTerm i none

    | _ =>

      throwError ""

    if t.size == 0 then

      logWarningAt args "`algebraize []` without arguments has no effect!"

    for f in t do

      let ft ← inferType f

      match ft.getAppFn with

      | Expr.const ``RingHom _ => addAlgebraInstanceFromRingHom f ft

      | _ => throwError m!"{f} is not of type `RingHom`"

    for f in t do

      match f.getAppFn with

      | Expr.const ``RingHom.comp _ =>

        try addIsScalarTowerInstanceFromRingHomComp f

        catch _ => continue

      | _ => continue

    if cfg.properties then

      addProperties t

  | `(tactic| algebraize $[$config]?) => do

    throwError "`algebraize` expects a list of arguments: `algebraize [f]`"

syntax "algebraize_only" (ppSpace algebraizeTermSeq)? : tactic

macro_rules
  | `(tactic| algebraize_only $[$args]?) =>
    `(tactic| algebraize -properties $[$args]?)

end Mathlib.Tactic
