/-
Extracted from CategoryTheory/Bicategory/Kan/HasKan.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Existence of Kan extensions and Kan lifts in bicategories

We provide the propositional typeclass `HasLeftKanExtension f g`, which asserts that there
exists a left Kan extension of `g` along `f`. See `CategoryTheory.Bicategory.Kan.IsKan` for
the definition of left Kan extensions. Under the assumption that `HasLeftKanExtension f g`,
we define the left Kan extension `lan f g` by using the axiom of choice.

## Main definitions

* `lan f g` is the left Kan extension of `g` along `f`, and is denoted by `f⁺ g`.
* `lanLift f g` is the left Kan lift of `g` along `f`, and is denoted by `f₊ g`.

These notations are inspired by
[M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006].

## TODO

* `ran f g` is the right Kan extension of `g` along `f`, and is denoted by `f⁺⁺ g`.
* `ranLift f g` is the right Kan lift of `g` along `f`, and is denoted by `f₊₊ g`.

-/

noncomputable section

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}

open Limits

section LeftKan

open LeftExtension

variable {f : a ⟶ b} {g : a ⟶ c}

class HasLeftKanExtension (f : a ⟶ b) (g : a ⟶ c) : Prop where
  hasInitial : HasInitial <| LeftExtension f g

theorem LeftExtension.IsKan.hasLeftKanExtension {t : LeftExtension f g} (H : IsKan t) :
    HasLeftKanExtension f g :=
  ⟨IsInitial.hasInitial H⟩

-- INSTANCE (free from Core): [HasLeftKanExtension

def lanLeftExtension (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : LeftExtension f g :=
  ⊥_ (LeftExtension f g)

def lan (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : b ⟶ c :=
  (lanLeftExtension f g).extension

scoped infixr:90 "⁺ " => lan
