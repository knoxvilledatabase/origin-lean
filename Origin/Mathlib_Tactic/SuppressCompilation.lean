/-
Extracted from Tactic/SuppressCompilation.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init
import Lean.Elab.Declaration
import Lean.Elab.Notation

/-!
# Suppressing compilation to executable code in a file or in a section

Currently, the compiler may spend a lot of time trying to produce executable code for complicated
definitions. This is a waste of resources for definitions in area of mathematics that will never
lead to executable code. The command `suppress_compilation` is a hack to disable code generation
on all definitions (in a section or in a whole file). See the issue https://github.com/leanprover-community/mathlib4/issues/7103

To compile a definition even when `suppress_compilation` is active, use
`unsuppress_compilation in def foo : ...`. This is activated by default on notations to make
sure that they work properly.

Note that `suppress_compilation` does not work with `notation3`. You need to prefix such a notation
declaration with `unsuppress_compilation` if `suppress_compilation` is active.
-/

open Lean Parser Elab Command

def elabSuppressCompilationDecl : CommandElab := fun
| `($[$doc?:docComment]? $(attrs?)? $(vis?)? $[noncomputable]? $(unsafe?)?
    $(recKind?)? def $id $sig:optDeclSig $val:declVal) => do
  elabDeclaration <| ← `($[$doc?:docComment]? $(attrs?)? $(vis?)? noncomputable $(unsafe?)?
    $(recKind?)? def $id $sig:optDeclSig $val:declVal)
| `($[$doc?:docComment]? $(attrs?)? $(vis?)? $[noncomputable]? $(unsafe?)?
    $(recKind?)? def $id $sig:optDeclSig $val:declVal deriving $derivs,*) => do
  elabDeclaration <| ← `($[$doc?:docComment]? $(attrs?)? $(vis?)? noncomputable $(unsafe?)?
    $(recKind?)? def $id $sig:optDeclSig $val:declVal deriving $derivs,*)
| `($[$doc?:docComment]? $(attrs?)? $(vis?)? $[noncomputable]? $(unsafe?)?
    $(recKind?)? $(attrKind?)? instance $(prio?)? $(id?)? $sig:declSig $val:declVal) => do
  elabDeclaration <| ← `($[$doc?:docComment]? $(attrs?)? $(vis?)? noncomputable $(unsafe?)?
    $(recKind?)? $(attrKind?)? instance $(prio?)? $(id?)? $sig:declSig $val:declVal)
| `($[$doc?:docComment]? $(attrs?)? $(vis?)? $[noncomputable]? $(unsafe?)?
    $(recKind?)? example $sig:optDeclSig $val:declVal) => do
  elabDeclaration <| ← `($[$doc?:docComment]? $(attrs?)? $(vis?)? noncomputable $(unsafe?)?
    $(recKind?)? example $sig:optDeclSig $val:declVal)
| `($[$doc?:docComment]? $(attrs?)? $(vis?)? $[noncomputable]? $(unsafe?)?
    $(recKind?)? abbrev $id $sig:optDeclSig $val:declVal) => do
  elabDeclaration <| ← `($[$doc?:docComment]? $(attrs?)? $(vis?)? noncomputable $(unsafe?)?
    $(recKind?)? abbrev $id $sig:optDeclSig $val:declVal)
| _ => throwUnsupportedSyntax

syntax "unsuppress_compilation" (" in " command)? : command

def expandSuppressCompilationNotation : Macro := fun
| `($[$doc?:docComment]? $(attrs?)? $(attrKind)? notation
    $(prec?)? $(name?)? $(prio?)? $items* => $v) => do
  let defn ← expandNotation <| ← `($[$doc?:docComment]? $(attrs?)? $(attrKind)? notation
    $(prec?)? $(name?)? $(prio?)? $items* => $v)
  `(unsuppress_compilation in $(⟨defn⟩):command)
| _ => Macro.throwUnsupported

macro "suppress_compilation" : command => do

  let declKind := mkIdent ``declaration

  let notaKind := mkIdent ``«notation»

  let declElab := mkCIdent ``elabSuppressCompilationDecl

  let notaMacro := mkCIdent ``expandSuppressCompilationNotation

  `(

  attribute [local command_elab $declKind] $declElab
  attribute [local macro $notaKind] $notaMacro
  )

macro_rules

| `(unsuppress_compilation $[in $cmd?]?) => do

  let declElab := mkCIdent ``elabSuppressCompilationDecl

  let notaMacro := mkCIdent ``expandSuppressCompilationNotation

  let attrCmds ← `(

    attribute [-command_elab] $declElab
    attribute [-macro] $notaMacro
  )
  if let some cmd := cmd? then
    `($attrCmds:command $cmd:command suppress_compilation)
  else
    return attrCmds
