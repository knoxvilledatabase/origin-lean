/-
Extracted from CategoryTheory/Sites/Coherent/Equivalence.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!

# Coherence and equivalence of categories

This file proves that the coherent and regular topologies transfer nicely along equivalences of
categories.
-/

namespace CategoryTheory

variable {C : Type*} [Category* C]

open GrothendieckTopology

namespace Equivalence

variable {D : Type*} [Category* D]

section Coherent

variable [Precoherent C]

theorem precoherent (e : C ≌ D) : Precoherent D := e.inverse.reflects_precoherent

-- INSTANCE (free from Core): [EssentiallySmall

-- INSTANCE (free from Core): (e

variable (A : Type*) [Category* A]
