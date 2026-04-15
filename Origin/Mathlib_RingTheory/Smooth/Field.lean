/-
Extracted from RingTheory/Smooth/Field.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Smooth algebras over fields

We show that separably generated extensions of fields are smooth.
In particular finitely generated field extensions over perfect fields are smooth.

-/

variable {K L ι : Type*} [Field L] [Field K] [Algebra K L]

open scoped IntermediateField.algebraAdjoinAdjoin in

lemma Algebra.FormallySmooth.adjoin_of_algebraicIndependent {v : ι → L}
    (hb : AlgebraicIndependent K v) :
    Algebra.FormallySmooth K (IntermediateField.adjoin K (Set.range v)) := by
  have : Algebra.FormallySmooth K (adjoin K (Set.range v)) :=
    .of_equiv hb.aevalEquiv
  have : Algebra.FormallySmooth (adjoin K (Set.range v))
      (IntermediateField.adjoin K (Set.range v)) :=
    .of_isLocalization (nonZeroDivisors _)
  exact .comp _ (adjoin K (Set.range v)) _

lemma Algebra.FormallySmooth.of_algebraicIndependent {v : ι → L}
    (hb : AlgebraicIndependent K v) (hb' : IntermediateField.adjoin K (Set.range v) = ⊤) :
    Algebra.FormallySmooth K L := by
  have := Algebra.FormallySmooth.adjoin_of_algebraicIndependent hb
  rw [hb'] at this
  exact .of_equiv IntermediateField.topEquiv

lemma Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable
    {v : ι → L} (hb : AlgebraicIndependent K v)
    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) L] :
    Algebra.FormallySmooth K L := by
  have := FormallySmooth.adjoin_of_algebraicIndependent hb
  have : FormallyEtale (IntermediateField.adjoin K (Set.range v)) L :=
    Algebra.FormallyEtale.of_isSeparable _ L
  exact .comp _ (IntermediateField.adjoin K (Set.range v)) _

-- INSTANCE (free from Core): (priority
