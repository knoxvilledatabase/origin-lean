/-
Extracted from Algebra/Homology/HomologicalComplexBiprod.lean
Genuine: 1 of 6 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-! Binary biproducts of homological complexes

In this file, it is shown that if two homological complex `K` and `L` in
a preadditive category are such that for all `i : ι`, the binary biproduct
`K.X i ⊞ L.X i` exists, then `K ⊞ L` exists, and there is an isomorphism
`biprodXIso K L i : (K ⊞ L).X i ≅ (K.X i) ⊞ (L.X i)`.

-/

open CategoryTheory Limits

namespace HomologicalComplex

variable {C ι : Type*} [Category* C] [Preadditive C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) [∀ i, HasBinaryBiproduct (K.X i) (L.X i)]

-- INSTANCE (free from Core): (i

-- INSTANCE (free from Core): (i

-- INSTANCE (free from Core): (i

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): (i

noncomputable def biprodXIso (i : ι) : (K ⊞ L).X i ≅ (K.X i) ⊞ (L.X i) :=
  (eval C c i).mapBiprod K L
