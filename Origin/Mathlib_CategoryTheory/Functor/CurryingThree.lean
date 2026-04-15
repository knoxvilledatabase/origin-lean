/-
Extracted from CategoryTheory/Functor/CurryingThree.lean
Genuine: 5 of 9 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Currying of functors in three variables

We study the equivalence of categories
`currying₃ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ≌ C₁ × C₂ × C₃ ⥤ E`.

-/

namespace CategoryTheory

namespace Functor

variable {C₁ C₂ C₁₂ C₃ C₂₃ D₁ D₂ D₃ E : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₁₂] [Category* C₂₃]
  [Category* D₁] [Category* D₂] [Category* D₃] [Category* E]

def currying₃ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ≌ C₁ × C₂ × C₃ ⥤ E :=
  currying.trans (currying.trans (prod.associativity C₁ C₂ C₃).congrLeft)

abbrev uncurry₃ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ C₁ × C₂ × C₃ ⥤ E := currying₃.functor

abbrev curry₃ : (C₁ × C₂ × C₃ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ E := currying₃.inverse

def fullyFaithfulUncurry₃ :
    (uncurry₃ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ (C₁ × C₂ × C₃ ⥤ E)).FullyFaithful :=
  currying₃.fullyFaithfulFunctor

def fullyFaithfulCurry₃ :
    (curry₃ : (C₁ × C₂ × C₃ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E)).FullyFaithful :=
  currying₃.fullyFaithfulInverse

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :
