/-
Extracted from CategoryTheory/Enriched/EnrichedCat.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The bicategory of `V`-enriched categories

We define the bicategory `EnrichedCat V` of (bundled) `V`-enriched categories for a fixed monoidal
category `V`.

## Future work

* Define change of base and `ForgetEnrichment` as 2-functors.
* Define the bicategory of enriched ordinary categories.
-/

universe w v u u₁ u₂ u₃

namespace CategoryTheory

open MonoidalCategory

variable (V : Type v) [Category.{w} V] [MonoidalCategory V]

def EnrichedCat := Bundled (EnrichedCategory.{w, v, u} V)

namespace EnrichedCat

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): str

def of (C : Type u) [EnrichedCategory.{w} V C] : EnrichedCat.{w, v, u} V :=
  Bundled.of C

open EnrichedCategory ForgetEnrichment

variable {V} {C : Type u} [EnrichedCategory V C] {D : Type u₁} [EnrichedCategory V D]
  {E : Type u₂} [EnrichedCategory V E] {E' : Type u₃} [EnrichedCategory V E']
