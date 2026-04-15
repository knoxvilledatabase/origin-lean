/-
Extracted from GroupTheory/FixedPointFree.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Fixed-point-free automorphisms

This file defines fixed-point-free automorphisms and proves some basic properties.

An automorphism `φ` of a group `G` is fixed-point-free if `1 : G` is the only fixed point of `φ`.
-/

namespace MonoidHom

variable {F G : Type*}

section Definitions

variable (φ : G → G)

def FixedPointFree [One G] := ∀ g, φ g = g → g = 1

def commutatorMap [Div G] (g : G) := g / φ g
