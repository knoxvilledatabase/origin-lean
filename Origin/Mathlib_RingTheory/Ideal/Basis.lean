/-
Extracted from RingTheory/Ideal/Basis.lean
Genuine: 2 | Conflates: 0 | Dissolved: 3 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.Ideal.Span

/-!
# The basis of ideals

Some results involving `Ideal` and `Basis`.
-/

namespace Ideal

variable {ι R S : Type*} [CommSemiring R] [CommRing S] [IsDomain S] [Algebra R S]

-- DISSOLVED: basisSpanSingleton

-- DISSOLVED: basisSpanSingleton_apply

-- DISSOLVED: constr_basisSpanSingleton

end Ideal

theorem Basis.mem_ideal_iff {ι R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {I : Ideal S}
    (b : Basis ι R I) {x : S} : x ∈ I ↔ ∃ c : ι →₀ R, x = Finsupp.sum c fun i x => x • (b i : S) :=
  (b.map ((I.restrictScalarsEquiv R _ _).restrictScalars R).symm).mem_submodule_iff

theorem Basis.mem_ideal_iff' {ι R S : Type*} [Fintype ι] [CommRing R] [CommRing S] [Algebra R S]
    {I : Ideal S} (b : Basis ι R I) {x : S} : x ∈ I ↔ ∃ c : ι → R, x = ∑ i, c i • (b i : S) :=
  (b.map ((I.restrictScalarsEquiv R _ _).restrictScalars R).symm).mem_submodule_iff'
