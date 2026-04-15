/-
Extracted from CategoryTheory/Category/Cat/Terminal.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Terminal categories

We prove that a category is terminal if its underlying type has a `Unique` structure and the
category has an `IsDiscrete` instance.

We then use this to provide various examples of terminal categories.

TODO: Show the converse: that terminal categories have a unique object and are discrete.

TODO: Provide an analogous characterization of terminal categories as codiscrete categories
with a unique object.

-/

universe v u v' u'

open CategoryTheory Limits Functor

namespace CategoryTheory.Cat

set_option backward.isDefEq.respectTransparency false in

def isTerminalOfUniqueOfIsDiscrete {T : Type u} [Category.{v} T] [Unique T] [IsDiscrete T] :
    IsTerminal (Cat.of T) :=
  IsTerminal.ofUniqueHom (fun X ↦ ((const X).obj (default : T)).toCatHom)
    (fun _ _ ↦ Cat.Hom.ext <| Functor.ext (by simp [eq_iff_true_of_subsingleton]))

-- INSTANCE (free from Core): :

noncomputable def terminalIsoOfUniqueOfIsDiscrete
    {T : Type u} [Category.{v} T] [Unique T] [IsDiscrete T] : ⊤_ Cat.{v, u} ≅ Cat.of T :=
  terminalIsoIsTerminal isTerminalOfUniqueOfIsDiscrete

def isTerminalDiscretePUnit : IsTerminal (Cat.of (Discrete PUnit)) :=
  isTerminalOfUniqueOfIsDiscrete

def isoDiscretePUnitOfIsTerminal {T : Type u} [Category.{u} T] (hT : IsTerminal (Cat.of T)) :
    Cat.of T ≅ Cat.of (Discrete PUnit) :=
  IsTerminal.uniqueUpToIso hT isTerminalDiscretePUnit

end CategoryTheory.Cat
