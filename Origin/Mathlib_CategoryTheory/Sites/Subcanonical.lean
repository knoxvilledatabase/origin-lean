/-
Extracted from CategoryTheory/Sites/Subcanonical.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Subcanonical Grothendieck topologies

This file provides some API for the Yoneda embedding into the category of sheaves for a
subcanonical Grothendieck topology.
-/

universe v' v u

namespace CategoryTheory.GrothendieckTopology

open Opposite Functor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [Subcanonical J]

def yonedaEquiv {X : C} {F : Sheaf J (Type v)} : (J.yoneda.obj X ⟶ F) ≃ F.obj.obj (op X) :=
  (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans CategoryTheory.yonedaEquiv
