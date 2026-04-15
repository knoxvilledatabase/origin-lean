/-
Extracted from CategoryTheory/FiberedCategory/Fiber.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!

# Fibers of functors

In this file we define, for a functor `p : 𝒳 ⥤ 𝒴`, the fiber categories `Fiber p S` for every
`S : 𝒮` as follows
- An object in `Fiber p S` is a pair `(a, ha)` where `a : 𝒳` and `ha : p.obj a = S`.
- A morphism in `Fiber p S` is a morphism `φ : a ⟶ b` in 𝒳 such that `p.map φ = 𝟙 S`.

For any category `C` equipped with a functor `F : C ⥤ 𝒳` such that `F ⋙ p` is constant at `S`,
we define a functor `inducedFunctor : C ⥤ Fiber p S` that `F` factors through.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory

open IsHomLift

namespace Functor

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

def Fiber (p : 𝒳 ⥤ 𝒮) (S : 𝒮) := { a : 𝒳 // p.obj a = S }

namespace Fiber

variable {p : 𝒳 ⥤ 𝒮} {S : 𝒮}

-- INSTANCE (free from Core): fiberCategory

def fiberInclusion : Fiber p S ⥤ 𝒳 where
  obj a := a.1
  map φ := φ.1

-- INSTANCE (free from Core): {a
