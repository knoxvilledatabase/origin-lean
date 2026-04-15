/-
Extracted from Order/Notation.lean
Genuine: 7 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Simps.NotationClass

/-!
# Notation classes for lattice operations

In this file we introduce typeclasses and definitions for lattice operations.

## Main definitions

* the `⊔` notation is used for `Max` since November 2024
* the `⊓` notation is used for `Min` since November 2024
* `HasCompl`: type class for the `ᶜ` notation
* `Top`: type class for the `⊤` notation
* `Bot`: type class for the `⊥` notation

## Notations

* `x ⊔ y`: lattice join operation;
* `x ⊓ y`: lattice meet operation;
* `xᶜ`: complement in a lattice;

-/

@[notation_class]
class HasCompl (α : Type*) where
  /-- Set / lattice complement -/
  compl : α → α

export HasCompl (compl)

postfix:1024 "ᶜ" => compl

/-! ### `Sup` and `Inf` -/

class Sup (α : Type*) where
  /-- Least upper bound (`\lub` notation) -/
  sup : α → α → α

class Inf (α : Type*) where
  /-- Greatest lower bound (`\glb` notation) -/
  inf : α → α → α

attribute [ext] Min Max

infixl:68 " ⊔ " => Max.max

infixl:69 " ⊓ " => Min.min

@[notation_class]
class HImp (α : Type*) where
  /-- Heyting implication `⇨` -/
  himp : α → α → α

@[notation_class]
class HNot (α : Type*) where
  /-- Heyting negation `￢` -/
  hnot : α → α

export HImp (himp)

export SDiff (sdiff)

export HNot (hnot)

infixr:60 " ⇨ " => himp

prefix:72 "￢" => hnot

@[notation_class, ext]
class Top (α : Type*) where
  /-- The top (`⊤`, `\top`) element -/
  top : α

@[notation_class, ext]
class Bot (α : Type*) where
  /-- The bot (`⊥`, `\bot`) element -/
  bot : α

notation "⊤" => Top.top

notation "⊥" => Bot.bot

instance (priority := 100) top_nonempty (α : Type*) [Top α] : Nonempty α :=
  ⟨⊤⟩

instance (priority := 100) bot_nonempty (α : Type*) [Bot α] : Nonempty α :=
  ⟨⊥⟩

attribute [match_pattern] Bot.bot Top.top
