/-
Extracted from Algebra/Colimit/Module.lean
Genuine: 4 of 10 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Direct limit of modules and abelian groups

See Atiyah-Macdonald PP.32-33, Matsumura PP.269-270

Generalizes the notion of "union", or "gluing", of incomparable modules over the same ring,
or incomparable abelian groups.

It is constructed as a quotient of the free module instead of a quotient of the disjoint union
so as to make the operations (addition etc.) "computable".

## Main definitions

* `Module.DirectLimit G f`
* `AddCommGroup.DirectLimit G f`

-/

suppress_compilation

noncomputable section -- needed for `deriving`

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

open Submodule

namespace Module

alias DirectedSystem.map_self := DirectedSystem.map_self'

alias DirectedSystem.map_map := DirectedSystem.map_map'

variable [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)] (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

inductive DirectLimit.Eqv [DecidableEq ι] : DirectSum ι G → DirectSum ι G → Prop
  | of_map {i j} (h : i ≤ j) (x : G i) :
    Eqv (DirectSum.lof R ι G i x) (DirectSum.lof R ι G j <| f i j h x)

def DirectLimit.moduleCon [DecidableEq ι] : ModuleCon R (DirectSum ι G) :=
  SMulCon.addConGen' (Eqv f) <| by rintro _ _ _ ⟨⟩; simpa only [← map_smul] using .of_map ..

variable (G)

def DirectLimit [DecidableEq ι] : Type _ := (DirectLimit.moduleCon f).Quotient

variable [DecidableEq ι]

namespace DirectLimit

section Basic

-- INSTANCE (free from Core): addCommMonoid

-- INSTANCE (free from Core): module

-- INSTANCE (free from Core): addCommGroup

-- INSTANCE (free from Core): inhabited

-- INSTANCE (free from Core): unique

variable (R ι)

def of (i) : G i →ₗ[R] DirectLimit G f :=
  .comp { __ := AddCon.mk' _, map_smul' := fun _ _ ↦ rfl } <| DirectSum.lof R ι G i

variable {R ι G f}
