/-
Extracted from Combinatorics/Quiver/ConnectedComponent.lean
Genuine: 5 of 7 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Combinatorics.Quiver.Subquiver
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.Symmetric

/-!
## Weakly connected components

For a quiver `V`, define the type `WeaklyConnectedComponent V` as the quotient of `V` by
the relation which identifies `a` with `b` if there is a path from `a` to `b` in `Symmetrify V`.
(These zigzags can be seen as a proof-relevant analogue of `EqvGen`.)

Strongly connected components have not yet been defined.
-/

universe v u

namespace Quiver

variable (V : Type*) [Quiver.{u+1} V]

def zigzagSetoid : Setoid V :=
  ⟨fun a b ↦ Nonempty (@Path (Symmetrify V) _ a b), fun _ ↦ ⟨Path.nil⟩, fun ⟨p⟩ ↦
    ⟨p.reverse⟩, fun ⟨p⟩ ⟨q⟩ ↦ ⟨p.comp q⟩⟩

def WeaklyConnectedComponent : Type _ :=
  Quotient (zigzagSetoid V)

namespace WeaklyConnectedComponent

variable {V}

protected def mk : V → WeaklyConnectedComponent V :=
  @Quotient.mk' _ (zigzagSetoid V)

instance : CoeTC V (WeaklyConnectedComponent V) :=
  ⟨WeaklyConnectedComponent.mk⟩

instance [Inhabited V] : Inhabited (WeaklyConnectedComponent V) :=
  ⟨show V from default⟩

protected theorem eq (a b : V) :
    (a : WeaklyConnectedComponent V) = b ↔ Nonempty (@Path (Symmetrify V) _ a b) :=
  Quotient.eq''

end WeaklyConnectedComponent

variable {V}

def wideSubquiverSymmetrify (H : WideSubquiver (Symmetrify V)) : WideSubquiver V :=
  fun _ _ ↦ { e | H _ _ (Sum.inl e) ∨ H _ _ (Sum.inr e) }

end Quiver
