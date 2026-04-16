/-
Extracted from Tactic/CategoryTheory/Coherence/Datatypes.lean
Genuine: 48 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Lean.Meta.Basic
import Mathlib.Init

noncomputable section

/-!
# Datatypes for bicategory like structures

This file defines the basic datatypes for bicategory like structures. We will use these datatypes
to write tactics that can be applied to both monoidal categories and bicategories:
- `Obj`: objects type
- `Atom₁`: atomic 1-morphisms type
- `Mor₁`: 1-morphisms type
- `Atom`: atomic non-structural 2-morphisms type
- `Mor₂`: 2-morphisms type
- `AtomIso`: atomic non-structural 2-isomorphisms type
- `Mor₂Iso`: 2-isomorphisms type
- `NormalizedHom`: normalized 1-morphisms type

A term of these datatypes wraps the corresponding `Expr` term, which can be extracted by
e.g. `η.e` for `η : Mor₂`.

The operations of these datatypes are defined in a monad `m` with the corresponding typeclasses:
- `MonadMor₁`: operations on `Mor₁`
- `MonadMor₂Iso`: operations on `Mor₂Iso`
- `MonadMor₂`: operations on `Mor₂`

For example, a monad `m` with `[MonadMor₂ m]` provides the operation
`MonadMor₂.comp₂M : Mor₂Iso → Mor₂Iso → m Mor₂Iso`, which constructs the expression for the
composition `η ≫ θ` of 2-morphisms `η` and `θ` in the monad `m`.

-/

open Lean Meta

namespace Mathlib.Tactic

namespace BicategoryLike

structure Obj where
  /-- Extracts a lean expression from an `Obj` term. Return `none` in the monoidal
  category context. -/
  e? : Option Expr
  deriving Inhabited

def Obj.e (a : Obj) : Expr :=
  a.e?.get!

structure Atom₁ : Type where
  /-- Extract a lean expression from an `Atom₁` term. -/
  e : Expr
  /-- The domain of the 1-morphism. -/
  src : Obj
  /-- The codomain of the 1-morphism. -/
  tgt : Obj
  deriving Inhabited

class MkAtom₁ (m : Type → Type) where
  /-- Construct a `Atom₁` term from a lean expression. -/
  ofExpr (e : Expr) : m Atom₁

inductive Mor₁ : Type
  /-- `id e a` is the expression for `𝟙 a`, where `e` is the underlying lean expression. -/
  | id (e : Expr) (a : Obj) : Mor₁
  /-- `comp e f g` is the expression for `f ≫ g`, where `e` is the underlying lean expression. -/
  | comp (e : Expr) : Mor₁ → Mor₁ → Mor₁
  /-- The expression for an atomic 1-morphism. -/
  | of : Atom₁ → Mor₁
  deriving Inhabited

class MkMor₁ (m : Type → Type) where
  /-- Construct a `Mor₁` term from a lean expression. -/
  ofExpr (e : Expr) : m Mor₁

def Mor₁.e : Mor₁ → Expr
  | .id e _ => e
  | .comp e _ _ => e
  | .of a => a.e

def Mor₁.src : Mor₁ → Obj
  | .id _ a => a
  | .comp _ f _ => f.src
  | .of f => f.src

def Mor₁.tgt : Mor₁ → Obj
  | .id _ a => a
  | .comp _ _ g => g.tgt
  | .of f => f.tgt

def Mor₁.toList : Mor₁ → List Atom₁
  | .id _ _ => []
  | .comp _ f g => f.toList ++ g.toList
  | .of f => [f]

class MonadMor₁ (m : Type → Type) where
  /-- The expression for `𝟙 a`. -/
  id₁M (a : Obj) : m Mor₁
  /-- The expression for `f ≫ g`. -/
  comp₁M (f g : Mor₁) : m Mor₁

structure CoherenceHom where
  /-- The underlying lean expression of a coherence isomorphism. -/
  e : Expr
  /-- The domain of a coherence isomorphism. -/
  src : Mor₁
  /-- The codomain of a coherence isomorphism. -/
  tgt : Mor₁
  /-- The `BicategoricalCoherence` instance. -/
  inst : Expr
  /-- Extract the structural 2-isomorphism. -/
  unfold : Expr
  deriving Inhabited

structure AtomIso where
  /-- The underlying lean expression of an `AtomIso` term. -/
  e : Expr
  /-- The domain of a 2-isomorphism. -/
  src : Mor₁
  /-- The codomain of a 2-isomorphism. -/
  tgt : Mor₁
  deriving Inhabited

inductive StructuralAtom : Type
  /-- The expression for the associator `α_ f g h`. -/
  | associator (e : Expr) (f g h : Mor₁) : StructuralAtom
  /-- The expression for the left unitor `λ_ f`. -/
  | leftUnitor (e : Expr) (f : Mor₁) : StructuralAtom
  /-- The expression for the right unitor `ρ_ f`. -/
  | rightUnitor (e : Expr) (f : Mor₁) : StructuralAtom
  | id (e : Expr) (f : Mor₁) : StructuralAtom
  | coherenceHom (α : CoherenceHom) : StructuralAtom
  deriving Inhabited

inductive Mor₂Iso : Type where
  | structuralAtom (α : StructuralAtom) : Mor₂Iso
  | comp (e : Expr) (f g h : Mor₁) (η θ : Mor₂Iso) : Mor₂Iso
  | whiskerLeft (e : Expr) (f g h : Mor₁) (η : Mor₂Iso) : Mor₂Iso
  | whiskerRight (e : Expr) (f g : Mor₁) (η : Mor₂Iso) (h : Mor₁) : Mor₂Iso
  | horizontalComp (e : Expr) (f₁ g₁ f₂ g₂ : Mor₁) (η θ : Mor₂Iso) : Mor₂Iso
  | inv (e : Expr) (f g : Mor₁) (η : Mor₂Iso) : Mor₂Iso
  | coherenceComp (e : Expr) (f g h i : Mor₁) (α : CoherenceHom) (η θ : Mor₂Iso) : Mor₂Iso
  | of (η : AtomIso) : Mor₂Iso
  deriving Inhabited

class MonadCoherehnceHom (m : Type → Type) where
  /-- Unfold a coherence isomorphism. -/
  unfoldM (α : CoherenceHom) : m Mor₂Iso

def StructuralAtom.e : StructuralAtom → Expr
  | .associator e .. => e
  | .leftUnitor e .. => e
  | .rightUnitor e .. => e
  | .id e .. => e
  | .coherenceHom α => α.e

open MonadMor₁

variable {m : Type → Type} [Monad m]

def StructuralAtom.srcM [MonadMor₁ m] : StructuralAtom → m Mor₁
  | .associator _ f g h => do comp₁M (← comp₁M f g) h
  | .leftUnitor _ f => do comp₁M (← id₁M f.src) f
  | .rightUnitor _ f => do comp₁M f (← id₁M f.tgt)
  | .id _ f => return f
  | .coherenceHom α => return α.src

def StructuralAtom.tgtM [MonadMor₁ m] : StructuralAtom → m Mor₁
  | .associator _ f g h => do comp₁M f (← comp₁M g h)
  | .leftUnitor _ f => return f
  | .rightUnitor _ f => return f
  | .id _ f => return f
  | .coherenceHom α => return α.tgt

def Mor₂Iso.e : Mor₂Iso → Expr
  | .structuralAtom α => α.e
  | .comp e .. => e
  | .whiskerLeft e .. => e
  | .whiskerRight e .. => e
  | .horizontalComp e .. => e
  | .inv e .. => e
  | .coherenceComp e .. => e
  | .of η => η.e

def Mor₂Iso.srcM {m : Type → Type} [Monad m] [MonadMor₁ m] : Mor₂Iso → m Mor₁
  | .structuralAtom α => α.srcM
  | .comp _ f .. => return f
  | .whiskerLeft _ f g .. => do comp₁M f g
  | .whiskerRight _ f _ _ h => do comp₁M f h
  | .horizontalComp _ f₁ _ f₂ .. => do comp₁M f₁ f₂
  | .inv _ _ g _ => return g
  | .coherenceComp _ f .. => return f
  | .of η => return η.src

def Mor₂Iso.tgtM {m : Type → Type} [Monad m] [MonadMor₁ m] : Mor₂Iso → m Mor₁
  | .structuralAtom α => α.tgtM
  | .comp _ _ _ h .. => return h
  | .whiskerLeft _ f _ h _ => do comp₁M f h
  | .whiskerRight _ _ g _ h => do comp₁M g h
  | .horizontalComp _ _ g₁ _ g₂ _ _ => do comp₁M g₁ g₂
  | .inv _ f _ _ => return f
  | .coherenceComp _ _ _ _ i .. => return i
  | .of η => return η.tgt

class MonadMor₂Iso (m : Type → Type) where
  /-- The expression for the associator `α_ f g h`. -/
  associatorM (f g h : Mor₁) : m StructuralAtom
  /-- The expression for the left unitor `λ_ f`. -/
  leftUnitorM (f : Mor₁) : m StructuralAtom
  /-- The expression for the right unitor `ρ_ f`. -/
  rightUnitorM (f : Mor₁) : m StructuralAtom
  /-- The expression for the identity `Iso.refl f`. -/
  id₂M (f : Mor₁) : m StructuralAtom
  /-- The expression for the coherence isomorphism `⊗𝟙 : f ⟶ g`. -/
  coherenceHomM (f g : Mor₁) (inst : Expr) : m CoherenceHom
  /-- The expression for the composition `η ≪≫ θ`. -/
  comp₂M (η θ : Mor₂Iso) : m Mor₂Iso
  /-- The expression for the left whiskering `whiskerLeftIso f η`. -/
  whiskerLeftM (f : Mor₁) (η : Mor₂Iso) : m Mor₂Iso
  /-- The expression for the right whiskering `whiskerRightIso η h`. -/
  whiskerRightM (η : Mor₂Iso) (h : Mor₁) : m Mor₂Iso
  /-- The expression for the horizontal composition `η ◫ θ`. -/
  horizontalCompM (η θ : Mor₂Iso) : m Mor₂Iso
  /-- The expression for the inverse `Iso.symm η`. -/
  symmM (η : Mor₂Iso) : m Mor₂Iso
  /-- The expression for the coherence composition `η ≪⊗≫ θ := η ≪≫ α ≪≫ θ`. -/
  coherenceCompM (α : CoherenceHom) (η θ : Mor₂Iso) : m Mor₂Iso

namespace MonadMor₂Iso

variable {m : Type → Type} [Monad m] [MonadMor₂Iso m]

def associatorM' (f g h : Mor₁) : m Mor₂Iso := do
  return .structuralAtom <| ← MonadMor₂Iso.associatorM f g h

def leftUnitorM' (f : Mor₁) : m Mor₂Iso := do
  return .structuralAtom <| ← MonadMor₂Iso.leftUnitorM f

def rightUnitorM' (f : Mor₁) : m Mor₂Iso := do
  return .structuralAtom <| ← MonadMor₂Iso.rightUnitorM f

def id₂M' (f : Mor₁) : m Mor₂Iso := do
  return .structuralAtom <| ← MonadMor₂Iso.id₂M f

def coherenceHomM' (f g : Mor₁) (inst : Expr) : m Mor₂Iso := do
  return .structuralAtom <| .coherenceHom <| ← MonadMor₂Iso.coherenceHomM f g inst

end MonadMor₂Iso

structure Atom where
  /-- Extract a lean expression from an `Atom` expression. -/
  e : Expr
  /-- The domain of a 2-morphism. -/
  src : Mor₁
  /-- The codomain of a 2-morphism. -/
  tgt : Mor₁
  deriving Inhabited

structure IsoLift where
  /-- The expression for the 2-isomorphism. -/
  e : Mor₂Iso
  /-- The expression for the proof that the forward direction of the 2-isomorphism is equal to
  the original 2-morphism. -/
  eq : Expr

inductive Mor₂ : Type where
  /-- The expression for `Iso.hom`. -/
  | isoHom (e : Expr) (isoLift : IsoLift) (iso : Mor₂Iso) : Mor₂
  /-- The expression for `Iso.inv`. -/
  | isoInv (e : Expr) (isoLift : IsoLift) (iso : Mor₂Iso) : Mor₂
  /-- The expression for the identity `𝟙 f`. -/
  | id (e : Expr) (isoLift : IsoLift) (f : Mor₁) : Mor₂
  /-- The expression for the composition `η ≫ θ`. -/
  | comp (e : Expr) (isoLift? : Option IsoLift) (f g h : Mor₁) (η θ : Mor₂) : Mor₂
  /-- The expression for the left whiskering `f ◁ η` with `η : g ⟶ h`. -/
  | whiskerLeft (e : Expr) (isoLift? : Option IsoLift) (f g h : Mor₁) (η : Mor₂) : Mor₂
  /-- The expression for the right whiskering `η ▷ h` with `η : f ⟶ g`. -/
  | whiskerRight (e : Expr) (isoLift? : Option IsoLift) (f g : Mor₁) (η : Mor₂) (h : Mor₁) : Mor₂
  /-- The expression for the horizontal composition `η ◫ θ` with `η : f₁ ⟶ g₁` and `θ : f₂ ⟶ g₂`. -/
  | horizontalComp (e : Expr) (isoLift? : Option IsoLift) (f₁ g₁ f₂ g₂ : Mor₁) (η θ : Mor₂) : Mor₂
  /-- The expression for the coherence composition `η ⊗≫ θ := η ≫ α ≫ θ` with `η : f ⟶ g`
  and `θ : h ⟶ i`. -/
  | coherenceComp (e : Expr) (isoLift? : Option IsoLift) (f g h i : Mor₁)
    (α : CoherenceHom) (η θ : Mor₂) : Mor₂
  /-- The expression for an atomic non-structural 2-morphism. -/
  | of (η : Atom) : Mor₂
  deriving Inhabited

class MkMor₂ (m : Type → Type) where
  /-- Construct a `Mor₂` term from a lean expression. -/
  ofExpr (e : Expr) : m Mor₂

def Mor₂.e : Mor₂ → Expr
  | .isoHom e .. => e
  | .isoInv e .. => e
  | .id e .. => e
  | .comp e .. => e
  | .whiskerLeft e .. => e
  | .whiskerRight e .. => e
  | .horizontalComp e .. => e
  | .coherenceComp e .. => e
  | .of η => η.e

def Mor₂.isoLift? : Mor₂ → Option IsoLift
  | .isoHom _ isoLift .. => some isoLift
  | .isoInv _ isoLift .. => some isoLift
  | .id _ isoLift .. => some isoLift
  | .comp _ isoLift? .. => isoLift?
  | .whiskerLeft _ isoLift? .. => isoLift?
  | .whiskerRight _ isoLift? .. => isoLift?
  | .horizontalComp _ isoLift? .. => isoLift?
  | .coherenceComp _ isoLift? .. => isoLift?
  | .of _ => none

def Mor₂.srcM {m : Type → Type} [Monad m] [MonadMor₁ m] : Mor₂ → m Mor₁
  | .isoHom _ _ iso => iso.srcM
  | .isoInv _ _ iso => iso.tgtM
  | .id _ _ f => return f
  | .comp _ _ f .. => return f
  | .whiskerLeft _ _ f g .. => do comp₁M f g
  | .whiskerRight _ _ f _ _ h => do comp₁M f h
  | .horizontalComp _ _ f₁ _ f₂ .. => do comp₁M f₁ f₂
  | .coherenceComp _ _ f .. => return f
  | .of η => return η.src

def Mor₂.tgtM {m : Type → Type} [Monad m] [MonadMor₁ m] : Mor₂ → m Mor₁
  | .isoHom _ _ iso => iso.tgtM
  | .isoInv _ _ iso => iso.srcM
  | .id _ _ f => return f
  | .comp _ _ _ _ h .. => return h
  | .whiskerLeft _ _ f _ h _ => do comp₁M f h
  | .whiskerRight _ _ _ g _ h => do comp₁M g h
  | .horizontalComp _ _ _ g₁ _ g₂ _ _ => do comp₁M g₁ g₂
  | .coherenceComp _ _ _ _ _ i .. => return i
  | .of η => return η.tgt

class MonadMor₂ (m : Type → Type) where
  /-- The expression for `Iso.hom η`. -/
  homM (η : Mor₂Iso) : m Mor₂
  /-- The expression for `Iso.hom η`. -/
  atomHomM (η : AtomIso) : m Atom
  /-- The expression for `Iso.inv η`. -/
  invM (η : Mor₂Iso) : m Mor₂
  /-- The expression for `Iso.inv η`. -/
  atomInvM (η : AtomIso) : m Atom
  /-- The expression for the identity `𝟙 f`. -/
  id₂M (f : Mor₁) : m Mor₂
  /-- The expression for the composition `η ≫ θ`. -/
  comp₂M (η θ : Mor₂) : m Mor₂
  /-- The expression for the left whiskering `f ◁ η`. -/
  whiskerLeftM (f : Mor₁) (η : Mor₂) : m Mor₂
  /-- The expression for the right whiskering `η ▷ h`. -/
  whiskerRightM (η : Mor₂) (h : Mor₁) : m Mor₂
  /-- The expression for the horizontal composition `η ◫ θ`. -/
  horizontalCompM (η θ : Mor₂) : m Mor₂
  /-- The expression for the coherence composition `η ⊗≫ θ := η ≫ α ≫ θ`. -/
  coherenceCompM (α : CoherenceHom) (η θ : Mor₂) : m Mor₂

inductive NormalizedHom : Type
  /-- The identity 1-morphism `𝟙 a`. -/
  | nil (e : Mor₁) (a : Obj) : NormalizedHom
  /-- The `cons` composes an atomic 1-morphism at the end of a normalized 1-morphism. -/
  | cons (e : Mor₁) : NormalizedHom → Atom₁ → NormalizedHom
  deriving Inhabited

def NormalizedHom.e : NormalizedHom → Mor₁
  | NormalizedHom.nil e _ => e
  | NormalizedHom.cons e _ _  => e

def NormalizedHom.src : NormalizedHom → Obj
  | NormalizedHom.nil _ a => a
  | NormalizedHom.cons _ p _ => p.src

def NormalizedHom.tgt : NormalizedHom → Obj
  | NormalizedHom.nil _ a => a
  | NormalizedHom.cons _ _  f => f.tgt

def normalizedHom.nilM [MonadMor₁ m] (a : Obj) : m NormalizedHom := do
  return NormalizedHom.nil (← id₁M a) a

def NormalizedHom.consM [MonadMor₁ m] (p : NormalizedHom) (f : Atom₁) :
    m NormalizedHom := do
  return NormalizedHom.cons (← comp₁M p.e (.of f)) p f

class Context (ρ : Type) where
  /-- Construct a context from a lean expression for a 2-morphism. -/
  mkContext? : Expr → MetaM (Option ρ)

export Context (mkContext?)

def mkContext {ρ  : Type} [Context ρ] (e : Expr) : MetaM ρ := do
  match ← mkContext? e with
  | some c => return c
  | none => throwError "failed to construct a monoidal category or bicategory context from {e}"

structure State where
  /-- The cache for evaluating lean expressions of 1-morphisms into `Mor₁` terms. -/
  cache : PersistentExprMap Mor₁ := {}

abbrev CoherenceM (ρ : Type) := ReaderT ρ <| StateT State MetaM

def CoherenceM.run {α ρ : Type} (x : CoherenceM ρ α) (ctx : ρ) (s : State := {}) :
    MetaM α := do
  Prod.fst <$> ReaderT.run x ctx s

end BicategoryLike

end Tactic

end Mathlib
