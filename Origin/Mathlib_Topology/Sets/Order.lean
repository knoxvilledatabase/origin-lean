/-
Extracted from Topology/Sets/Order.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Clopen upper sets

In this file we define the type of clopen upper sets.
-/

open Set TopologicalSpace

variable {α : Type*} [TopologicalSpace α] [LE α]

/-! ### Compact open sets -/

structure ClopenUpperSet (α : Type*) [TopologicalSpace α] [LE α] extends Clopens α where
  upper' : IsUpperSet carrier

namespace ClopenUpperSet

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

def Simps.coe (s : ClopenUpperSet α) : Set α := s

initialize_simps_projections ClopenUpperSet (carrier → coe, as_prefix coe)

theorem upper (s : ClopenUpperSet α) : IsUpperSet (s : Set α) :=
  s.upper'

theorem isClopen (s : ClopenUpperSet α) : IsClopen (s : Set α) :=
  s.isClopen'
