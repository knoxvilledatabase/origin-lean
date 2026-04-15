/-
Extracted from Order/Category/OmegaCompletePartialOrder.lean
Genuine: 6 of 17 | Dissolved: 0 | Infrastructure: 11
-/
import Origin.Core

/-!
# Category of types with an omega complete partial order

In this file, we bundle the class `OmegaCompletePartialOrder` into a
concrete category and prove that continuous functions also form
an `OmegaCompletePartialOrder`.

## Main definitions

* `ωCPO`
  * an instance of `Category` and `ConcreteCategory`

-/

open CategoryTheory

universe u v

structure ωCPO : Type (u + 1) where
  /-- Construct a bundled ωCPO from the underlying type and typeclass. -/
  of ::
  /-- The underlying type. -/
  carrier : Type u
  [str : OmegaCompletePartialOrder carrier]

attribute [instance] ωCPO.str

namespace ωCPO

open OmegaCompletePartialOrder

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

open CategoryTheory.Limits

namespace HasProducts

def product {J : Type v} (f : J → ωCPO.{v}) : Fan f :=
  Fan.mk (of (∀ j, f j)) fun j => .mk (Pi.evalOrderHom j) fun _ => rfl

def isProduct (J : Type v) (f : J → ωCPO) : IsLimit (product f) where
  lift s :=
    ⟨⟨fun t j => (s.π.app ⟨j⟩) t, fun _ _ h j => (s.π.app ⟨j⟩).monotone h⟩,
      fun x => funext fun j => (s.π.app ⟨j⟩).continuous x⟩
  uniq s m w := by
    ext t; funext j -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext t j`
    change m t j = (s.π.app ⟨j⟩) t
    rw [← w ⟨j⟩]
    rfl
  fac _ _ := rfl

-- INSTANCE (free from Core): (J

end HasProducts

-- INSTANCE (free from Core): omegaCompletePartialOrderEqualizer

namespace HasEqualizers

def equalizerι {α β : Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]
    (f g : α →𝒄 β) : { a : α // f a = g a } →𝒄 α :=
  .mk (OrderHom.Subtype.val _) fun _ => rfl

def equalizer {X Y : ωCPO.{v}} (f g : X ⟶ Y) : Fork f g :=
  Fork.ofι (P := ωCPO.of { a // f a = g a }) (equalizerι f g)
    (ContinuousHom.ext _ _ fun x => x.2)

def isEqualizer {X Y : ωCPO.{v}} (f g : X ⟶ Y) : IsLimit (equalizer f g) :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨{  toFun := fun x => ⟨s.ι x, by apply ContinuousHom.congr_fun s.condition⟩
        monotone' := fun _ _ h => s.ι.monotone h
        map_ωSup' := fun x => Subtype.ext (s.ι.continuous x)
      }, by ext; rfl, fun hm => by
      ext x : 2; apply Subtype.ext ?_ -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext`
      apply ContinuousHom.congr_fun hm⟩

end HasEqualizers

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): {X

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end

end ωCPO
