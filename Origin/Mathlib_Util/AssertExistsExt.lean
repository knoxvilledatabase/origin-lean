/-
Extracted from Util/AssertExistsExt.lean
Genuine: 3 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Lean.Environment
import Mathlib.Init

/-!
# Environment extension for tracking existence of declarations and imports

This is used by the `assert_not_exists` and `assert_not_imported` commands.
-/

open Lean

namespace Mathlib.AssertNotExist

structure AssertExists where
  /-- The type of the assertion: `true` means declaration, `false` means import. -/
  isDecl : Bool
  /-- The fully qualified name of a declaration that is expected to exist. -/
  givenName : Name
  /-- The name of the module where the assertion was made. -/
  modName : Name
  deriving BEq, Hashable

initialize assertExistsExt : SimplePersistentEnvExtension AssertExists (Std.HashSet AssertExists) ←

  registerSimplePersistentEnvExtension {

    addImportedFn := fun as => as.foldl Std.HashSet.insertMany {}

    addEntryFn := .insert

  }

def addDeclEntry {m : Type → Type} [MonadEnv m] (isDecl : Bool) (declName mod : Name) : m Unit :=
  modifyEnv (assertExistsExt.addEntry · { isDecl := isDecl, givenName := declName, modName := mod })

end Mathlib.AssertNotExist

open Mathlib.AssertNotExist

def Lean.Environment.getSortedAssertExists (env : Environment) : Array AssertExists :=
  assertExistsExt.getState env |>.toArray.qsort fun d e => (e.isDecl < d.isDecl) ||
    (e.isDecl == d.isDecl && (d.givenName.toString < e.givenName.toString))
