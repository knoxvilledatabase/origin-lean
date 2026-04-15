/-
Extracted from Algebra/Colimit/Ring.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Direct limit of rings, and fields

See Atiyah-Macdonald PP.32-33, Matsumura PP.269-270

Generalizes the notion of "union", or "gluing", of incomparable rings or fields.

It is constructed as a quotient of the free commutative ring instead of a quotient of
the disjoint union so as to make the operations (addition etc.) "computable".

## Main definition

* `Ring.DirectLimit G f`

-/

assert_not_exists Cardinal

suppress_compilation

noncomputable section -- needed for `deriving`

variable {ι : Type*} [Preorder ι] (G : ι → Type*)

open Submodule

namespace Ring

variable [∀ i, CommRing (G i)]

variable (f : ∀ i j, i ≤ j → G i → G j)

open FreeCommRing

def DirectLimit : Type _ :=
  FreeCommRing (Σ i, G i) ⧸
    Ideal.span
      { a |
        (∃ i j H x, of (⟨j, f i j H x⟩ : Σ i, G i) - of ⟨i, x⟩ = a) ∨
          (∃ i, of (⟨i, 1⟩ : Σ i, G i) - 1 = a) ∨
            (∃ i x y, of (⟨i, x + y⟩ : Σ i, G i) - (of ⟨i, x⟩ + of ⟨i, y⟩) = a) ∨
              ∃ i x y, of (⟨i, x * y⟩ : Σ i, G i) - of ⟨i, x⟩ * of ⟨i, y⟩ = a }

deriving Zero, One, AddCommMonoid, Ring, CommRing, Inhabited

namespace DirectLimit

nonrec def of (i) : G i →+* DirectLimit G f :=
  RingHom.mk'
    { toFun := fun x ↦ Ideal.Quotient.mk _ (of (⟨i, x⟩ : Σ i, G i))
      map_one' := Ideal.Quotient.eq.2 <| subset_span <| Or.inr <| Or.inl ⟨i, rfl⟩
      map_mul' := fun x y ↦
        Ideal.Quotient.eq.2 <| subset_span <| Or.inr <| Or.inr <| Or.inr ⟨i, x, y, rfl⟩ }
    fun x y ↦ Ideal.Quotient.eq.2 <| subset_span <| Or.inr <| Or.inr <| Or.inl ⟨i, x, y, rfl⟩

variable {G f}
