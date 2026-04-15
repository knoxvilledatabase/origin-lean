/-
Extracted from Analysis/Normed/Module/Normalize.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Normalized vector

Function that returns unit length vector that points in the same direction
(if the given vector is nonzero vector) or returns zero vector
(if the given vector is zero vector).
-/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def NormedSpace.normalize (x : V) : V := ‖x‖⁻¹ • x

namespace NormedSpace
