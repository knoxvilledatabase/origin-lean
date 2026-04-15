/-
Extracted from Algebra/Homology/QuasiIso.lean
Genuine: 8 of 10 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Quasi-isomorphisms

A chain map is a quasi-isomorphism if it induces isomorphisms on homology.

-/

open CategoryTheory Limits

universe v u

open HomologicalComplex

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {c : ComplexShape ι} {K L M K' L' : HomologicalComplex C c}

class QuasiIsoAt (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] : Prop where
  quasiIso : ShortComplex.QuasiIso ((shortComplexFunctor C c i).map f)

lemma quasiIsoAt_iff (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] :
    QuasiIsoAt f i ↔
      ShortComplex.QuasiIso ((shortComplexFunctor C c i).map f) := by
  constructor
  · intro h
    exact h.quasiIso
  · intro h
    exact ⟨h⟩

-- INSTANCE (free from Core): quasiIsoAt_of_isIso

lemma quasiIsoAt_iff' (f : K ⟶ L) (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    [K.HasHomology j] [L.HasHomology j] [(K.sc' i j k).HasHomology] [(L.sc' i j k).HasHomology] :
    QuasiIsoAt f j ↔
      ShortComplex.QuasiIso ((shortComplexFunctor' C c i j k).map f) := by
  rw [quasiIsoAt_iff]
  exact ShortComplex.quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoOfNatIso (natIsoSc' C c i j k hi hk) (Arrow.mk f))

lemma quasiIsoAt_of_retract {f : K ⟶ L} {f' : K' ⟶ L'}
    (h : RetractArrow f f') (i : ι) [K.HasHomology i] [L.HasHomology i]
    [K'.HasHomology i] [L'.HasHomology i] [hf' : QuasiIsoAt f' i] :
    QuasiIsoAt f i := by
  rw [quasiIsoAt_iff] at hf' ⊢
  exact ShortComplex.quasiIso_of_retract (h.map (shortComplexFunctor C c i))

lemma quasiIsoAt_iff_isIso_homologyMap (f : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] :
    QuasiIsoAt f i ↔ IsIso (homologyMap f i) := by
  rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
  rfl

lemma quasiIsoAt_iff_exactAt (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
    (hK : K.ExactAt i) :
    QuasiIsoAt f i ↔ L.ExactAt i := by
  simp only [quasiIsoAt_iff, ShortComplex.quasiIso_iff, exactAt_iff,
    ShortComplex.exact_iff_isZero_homology] at hK ⊢
  constructor
  · intro h
    exact IsZero.of_iso hK (@asIso _ _ _ _ _ h).symm
  · intro hL
    exact ⟨⟨0, IsZero.eq_of_src hK _ _, IsZero.eq_of_tgt hL _ _⟩⟩

lemma quasiIsoAt_iff_exactAt' (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
    (hL : L.ExactAt i) :
    QuasiIsoAt f i ↔ K.ExactAt i := by
  simp only [quasiIsoAt_iff, ShortComplex.quasiIso_iff, exactAt_iff,
    ShortComplex.exact_iff_isZero_homology] at hL ⊢
  constructor
  · intro h
    exact IsZero.of_iso hL (@asIso _ _ _ _ _ h)
  · intro hK
    exact ⟨⟨0, IsZero.eq_of_src hK _ _, IsZero.eq_of_tgt hL _ _⟩⟩

lemma exactAt_iff_of_quasiIsoAt (f : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] [QuasiIsoAt f i] :
    K.ExactAt i ↔ L.ExactAt i :=
  ⟨fun hK => (quasiIsoAt_iff_exactAt f i hK).1 inferInstance,
    fun hL => (quasiIsoAt_iff_exactAt' f i hL).1 inferInstance⟩

-- INSTANCE (free from Core): (f
