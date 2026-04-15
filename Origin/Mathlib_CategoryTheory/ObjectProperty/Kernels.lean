/-
Extracted from CategoryTheory/ObjectProperty/Kernels.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Objects that are (co)kernels of morphisms

Given a morphism property `W` on a category, we introduce two object properties
`kernels W` and `cokernels W`, consisting of all (co)kernels of morphisms
satisfying `W`.

Given an object property `P`, we also introduce two predicates
`P.IsClosedUnderKernels` and `P.IsClosedUnderCokernels`, stating that all
(co)kernels of morphisms between objects in `P` remain in `P`.

-/

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

namespace MorphismProperty

variable (W : MorphismProperty C)

inductive kernels : ObjectProperty C
  | of_isLimit {X₁ X₂ : C} (f : X₁ ⟶ X₂) (k : KernelFork f) (hk : IsLimit k)
    (hf : W f) : kernels k.pt

lemma nonempty_kernels {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) [HasKernel f] :
    W.kernels.Nonempty :=
  ObjectProperty.nonempty_of_prop (kernels.of_isLimit f _ (kernelIsKernel f) hf)

-- INSTANCE (free from Core): :

inductive cokernels : ObjectProperty C
  | of_isColimit {X₁ X₂ : C} (f : X₁ ⟶ X₂) (k : CokernelCofork f) (hk : IsColimit k)
    (hf : W f) : cokernels k.pt

lemma nonempty_cokernels {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) [HasCokernel f] :
    W.cokernels.Nonempty :=
  ObjectProperty.nonempty_of_prop (cokernels.of_isColimit f _ (cokernelIsCokernel f) hf)

-- INSTANCE (free from Core): :

end MorphismProperty

namespace ObjectProperty

variable (P : ObjectProperty C)
