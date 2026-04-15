/-
Extracted from Topology/Specialization.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Specialization order

This file defines a type synonym for a topological space considered with its specialisation order.
-/

open CategoryTheory Topology

def Specialization (α : Type*) := α

namespace Specialization

variable {α β γ : Type*}
