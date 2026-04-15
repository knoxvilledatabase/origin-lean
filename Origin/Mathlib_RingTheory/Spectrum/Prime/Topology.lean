/-
Extracted from RingTheory/Spectrum/Prime/Topology.lean
Genuine: 23 of 29 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# The Zariski topology on the prime spectrum of a commutative (semi)ring

## Conventions

We denote subsets of (semi)rings with `s`, `s'`, etc...
whereas we denote subsets of prime spectra with `t`, `t'`, etc...

## Inspiration/contributors

The contents of this file draw inspiration from <https://github.com/ramonfmir/lean-scheme>
which has contributions from Ramon Fernandez Mir, Kevin Buzzard, Kenny Lau,
and Chris Hughes (on an earlier repository).

## Main definitions

* `PrimeSpectrum.zariskiTopology`: the Zariski topology on the prime spectrum, whose closed sets
  are zero loci (`zeroLocus`).

* `PrimeSpectrum.basicOpen`: the complement of the zero locus of a single element.
  The `basicOpen`s form a topological basis of the Zariski topology:
  `PrimeSpectrum.isTopologicalBasis_basic_opens`.

* `PrimeSpectrum.comap`: the continuous map between prime spectra induced by a ring homomorphism.

* `IsLocalRing.closedPoint`: the maximal ideal of a local ring is the unique closed point in its
  prime spectrum.

## Main results

* `PrimeSpectrum.instSpectralSpace`: every prime spectrum is a spectral space, i.e. it is
  quasi-compact, sober (in particular T0), quasi-separated, and its compact open subsets form
  a topological basis.

* `PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero`: the prime spectrum of a
  commutative semiring is discrete iff it is finite and the semiring has zero Krull dimension
  or is trivial.

* `PrimeSpectrum.localization_comap_range`, `PrimeSpectrum.localization_comap_isEmbedding`:
  localization at a submonoid of a commutative semiring induces an embedding between the prime
  spectra, with range consisting of prime ideals disjoint from the submonoid.

* `PrimeSpectrum.localization_away_comap_range`: for localization away from an element, the
  range of the embedding is the `basicOpen` associated to the element.

* `PrimeSpectrum.comap_isEmbedding_of_surjective`: a surjective ring homomorphism between
  commutative semirings induces an embedding between the prime spectra.

* `PrimeSpectrum.isClosedEmbedding_comap_of_surjective`: a surjective ring homomorphism between
  commutative rings induces a closed embedding between the prime spectra.

* `PrimeSpectrum.primeSpectrumProdHomeo`: the prime spectrum of a product semiring is homeomorphic
  to the disjoint union of the prime spectra.

* `PrimeSpectrum.stableUnderSpecialization_range_iff`: the range of `PrimeSpectrum.comap _` is
  closed iff it is stable under specialization.

* `PrimeSpectrum.denseRange_comap_iff_minimalPrimes`,
  `PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical`: the range of `comap f` is dense
  iff it contains all minimal primes, iff the kernel of `f` is contained in the nilradical.

* `PrimeSpectrum.isClosedMap_comap_of_isIntegral`: `comap f` is a closed map if `f` is integral.

* `PrimeSpectrum.isIntegral_of_isClosedMap_comap_mapRingHom`: `f : R →+* S` is integral if
  `comap (Polynomial.mapRingHom f : R[X] →+* S[X])` is a closed map.

In the prime spectrum of a commutative semiring:

* `PrimeSpectrum.isClosed_iff_zeroLocus_radical_ideal`, `PrimeSpectrum.isRadical_vanishingIdeal`,
  `PrimeSpectrum.zeroLocus_eq_iff`, `PrimeSpectrum.vanishingIdeal_anti_mono_iff`:
  closed subsets correspond to radical ideals.

* `PrimeSpectrum.isClosed_singleton_iff_isMaximal`: closed points correspond to maximal ideals.

* `PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime`: irreducible closed subsets correspond
  to prime ideals.

* `minimalPrimes.equivIrreducibleComponents`: irreducible components correspond to minimal primes.

* `PrimeSpectrum.mulZeroAddOneEquivClopens`: clopen subsets correspond to pairs of elements
  that add up to 1 and multiply to 0 in the semiring.

* `PrimeSpectrum.isIdempotentElemEquivClopens`: (if the semiring is a ring) clopen subsets
  correspond to idempotents in the ring.

-/

open Topology

noncomputable section

universe u v

variable (R : Type u) (S : Type v)

namespace PrimeSpectrum

section CommSemiring

variable [CommSemiring R] [CommSemiring S]

variable {R S}

-- INSTANCE (free from Core): zariskiTopology

theorem isOpen_iff (U : Set (PrimeSpectrum R)) : IsOpen U ↔ ∃ s, Uᶜ = zeroLocus s := by
  simp only [@eq_comm _ Uᶜ]; rfl

theorem isClosed_iff_zeroLocus (Z : Set (PrimeSpectrum R)) : IsClosed Z ↔ ∃ s, Z = zeroLocus s := by
  rw [← isOpen_compl_iff, isOpen_iff, compl_compl]

theorem isClosed_iff_zeroLocus_ideal (Z : Set (PrimeSpectrum R)) :
    IsClosed Z ↔ ∃ I : Ideal R, Z = zeroLocus I :=
  (isClosed_iff_zeroLocus _).trans
    ⟨fun ⟨s, hs⟩ => ⟨_, (zeroLocus_span s).substr hs⟩, fun ⟨I, hI⟩ => ⟨I, hI⟩⟩

theorem isClosed_iff_zeroLocus_radical_ideal (Z : Set (PrimeSpectrum R)) :
    IsClosed Z ↔ ∃ I : Ideal R, I.IsRadical ∧ Z = zeroLocus I :=
  (isClosed_iff_zeroLocus_ideal _).trans
    ⟨fun ⟨I, hI⟩ => ⟨_, I.radical_isRadical, (zeroLocus_radical I).substr hI⟩, fun ⟨I, _, hI⟩ =>
      ⟨I, hI⟩⟩

theorem isClosed_zeroLocus (s : Set R) : IsClosed (zeroLocus s) := by
  rw [isClosed_iff_zeroLocus]
  exact ⟨s, rfl⟩

theorem zeroLocus_vanishingIdeal_eq_closure (t : Set (PrimeSpectrum R)) :
    zeroLocus (vanishingIdeal t : Set R) = closure t := by
  rcases isClosed_iff_zeroLocus (closure t) |>.mp isClosed_closure with ⟨I, hI⟩
  rw [subset_antisymm_iff, (isClosed_zeroLocus _).closure_subset_iff, hI,
      subset_zeroLocus_iff_subset_vanishingIdeal, (gc R).u_l_u_eq_u,
      ← subset_zeroLocus_iff_subset_vanishingIdeal, ← hI]
  exact ⟨subset_closure, subset_zeroLocus_vanishingIdeal t⟩

theorem vanishingIdeal_closure (t : Set (PrimeSpectrum R)) :
    vanishingIdeal (closure t) = vanishingIdeal t :=
  zeroLocus_vanishingIdeal_eq_closure t ▸ (gc R).u_l_u_eq_u t

theorem closure_singleton (x) : closure ({x} : Set (PrimeSpectrum R)) = zeroLocus x.asIdeal := by
  rw [← zeroLocus_vanishingIdeal_eq_closure, vanishingIdeal_singleton]

theorem isClosed_singleton_iff_isMaximal (x : PrimeSpectrum R) :
    IsClosed ({x} : Set (PrimeSpectrum R)) ↔ x.asIdeal.IsMaximal := by
  rw [← closure_subset_iff_isClosed, ← zeroLocus_vanishingIdeal_eq_closure,
      vanishingIdeal_singleton]
  constructor <;> intro H
  · rcases x.asIdeal.exists_le_maximal x.2.1 with ⟨m, hm, hxm⟩
    exact (congr_arg asIdeal (@H ⟨m, hm.isPrime⟩ hxm)) ▸ hm
  · exact fun p hp ↦ PrimeSpectrum.ext (H.eq_of_le p.2.1 hp).symm

theorem isRadical_vanishingIdeal (s : Set (PrimeSpectrum R)) : (vanishingIdeal s).IsRadical := by
  rw [← vanishingIdeal_closure, ← zeroLocus_vanishingIdeal_eq_closure,
    vanishingIdeal_zeroLocus_eq_radical]
  apply Ideal.radical_isRadical

theorem zeroLocus_eq_iff {I J : Ideal R} :
    zeroLocus (I : Set R) = zeroLocus J ↔ I.radical = J.radical := by
  constructor
  · intro h; simp_rw [← vanishingIdeal_zeroLocus_eq_radical, h]
  · intro h; rw [← zeroLocus_radical, h, zeroLocus_radical]

theorem vanishingIdeal_anti_mono_iff {s t : Set (PrimeSpectrum R)} (ht : IsClosed t) :
    s ⊆ t ↔ vanishingIdeal t ≤ vanishingIdeal s :=
  ⟨vanishingIdeal_anti_mono, fun h => by
    rw [← ht.closure_subset_iff, ← ht.closure_eq]
    convert ← zeroLocus_anti_mono_ideal h <;> apply zeroLocus_vanishingIdeal_eq_closure⟩

theorem vanishingIdeal_strict_anti_mono_iff {s t : Set (PrimeSpectrum R)} (hs : IsClosed s)
    (ht : IsClosed t) : s ⊂ t ↔ vanishingIdeal t < vanishingIdeal s := by
  rw [Set.ssubset_def, vanishingIdeal_anti_mono_iff hs, vanishingIdeal_anti_mono_iff ht,
    lt_iff_le_not_ge]

def closedsEmbedding (R : Type*) [CommSemiring R] :
    (TopologicalSpace.Closeds <| PrimeSpectrum R)ᵒᵈ ↪o Ideal R :=
  OrderEmbedding.ofMapLEIff (fun s => vanishingIdeal ↑(OrderDual.ofDual s)) fun s _ =>
    (vanishingIdeal_anti_mono_iff s.2).symm

local notation "Z(" a ")" => zeroLocus (a : Set R)

theorem isIrreducible_zeroLocus_iff_of_radical (I : Ideal R) (hI : I.IsRadical) :
    IsIrreducible (zeroLocus (I : Set R)) ↔ I.IsPrime := by
  rw [Ideal.isPrime_iff, IsIrreducible]
  apply and_congr
  · rw [Set.nonempty_iff_ne_empty, Ne, zeroLocus_empty_iff_eq_top]
  · trans ∀ x y : Ideal R, Z(I) ⊆ Z(x) ∪ Z(y) → Z(I) ⊆ Z(x) ∨ Z(I) ⊆ Z(y)
    · simp_rw [isPreirreducible_iff_isClosed_union_isClosed, isClosed_iff_zeroLocus_ideal]
      constructor
      · rintro h x y
        exact h _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
      · rintro h _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact h x y
    · simp_rw [← zeroLocus_inf, subset_zeroLocus_iff_le_vanishingIdeal,
        vanishingIdeal_zeroLocus_eq_radical, hI.radical]
      constructor
      · simp_rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← Ideal.span_le, ←
          Ideal.span_singleton_mul_span_singleton]
        refine fun h x y h' => h _ _ ?_
        rw [← hI.radical_le_iff] at h' ⊢
        simpa only [Ideal.radical_inf, Ideal.radical_mul] using h'
      · simp_rw [or_iff_not_imp_left, SetLike.not_le_iff_exists]
        rintro h s t h' ⟨x, hx, hx'⟩ y hy
        exact h (h' ⟨Ideal.mul_mem_right _ _ hx, Ideal.mul_mem_left _ _ hy⟩) hx'

theorem isIrreducible_zeroLocus_iff (I : Ideal R) :
    IsIrreducible (zeroLocus (I : Set R)) ↔ I.radical.IsPrime :=
  zeroLocus_radical I ▸ isIrreducible_zeroLocus_iff_of_radical _ I.radical_isRadical

theorem isIrreducible_iff_vanishingIdeal_isPrime {s : Set (PrimeSpectrum R)} :
    IsIrreducible s ↔ (vanishingIdeal s).IsPrime := by
  rw [← isIrreducible_iff_closure, ← zeroLocus_vanishingIdeal_eq_closure,
    isIrreducible_zeroLocus_iff_of_radical _ (isRadical_vanishingIdeal s)]

lemma vanishingIdeal_isIrreducible :
    vanishingIdeal (R := R) '' {s | IsIrreducible s} = {P | P.IsPrime} :=
  Set.ext fun I ↦ ⟨fun ⟨_, hs, e⟩ ↦ e ▸ isIrreducible_iff_vanishingIdeal_isPrime.mp hs,
    fun h ↦ ⟨zeroLocus I, (isIrreducible_zeroLocus_iff_of_radical _ h.isRadical).mpr h,
      (vanishingIdeal_zeroLocus_eq_radical I).trans h.radical⟩⟩

lemma vanishingIdeal_isClosed_isIrreducible :
    vanishingIdeal (R := R) '' {s | IsClosed s ∧ IsIrreducible s} = {P | P.IsPrime} := by
  refine (subset_antisymm ?_ ?_).trans vanishingIdeal_isIrreducible
  · exact Set.image_mono fun _ ↦ And.right
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨closure s, ⟨isClosed_closure, hs.closure⟩, vanishingIdeal_closure s⟩

lemma irreducibleSpace_iff_isPrime_nilradical :
    IrreducibleSpace (PrimeSpectrum R) ↔ (nilradical R).IsPrime := by
  simp [irreducibleSpace_def, isIrreducible_iff_vanishingIdeal_isPrime]

-- INSTANCE (free from Core): irreducibleSpace

-- INSTANCE (free from Core): quasiSober

-- INSTANCE (free from Core): (I

-- INSTANCE (free from Core): compactSpace

theorem discreteTopology_iff_finite_and_krullDimLE_zero : DiscreteTopology (PrimeSpectrum R) ↔
    Finite (PrimeSpectrum R) ∧ Ring.KrullDimLE 0 R :=
  ⟨fun _ ↦ ⟨finite_of_compact_of_discrete, .mk₀ fun I h ↦ isClosed_singleton_iff_isMaximal ⟨I, h⟩
    |>.mp <| discreteTopology_iff_forall_isClosed.mp ‹_› _⟩, fun ⟨_, _⟩ ↦
    .of_finite_of_isClosed_singleton fun p ↦ (isClosed_singleton_iff_isMaximal p).mpr inferInstance⟩

theorem discreteTopology_iff_finite_isMaximal_and_sInf_le_nilradical :
    letI s := {I : Ideal R | I.IsMaximal}
    DiscreteTopology (PrimeSpectrum R) ↔ Finite s ∧ sInf s ≤ nilradical R := by
  rw [discreteTopology_iff_finite_and_krullDimLE_zero, Ring.krullDimLE_zero_iff,
    (equivSubtype R).finite_iff, ← Set.coe_setOf, Set.finite_coe_iff, Set.finite_coe_iff]
  refine ⟨fun h ↦ ⟨h.1.subset fun _ h ↦ h.isPrime, nilradical_eq_sInf R ▸ sInf_le_sInf h.2⟩,
    fun ⟨fin, le⟩ ↦ ?_⟩
  have hpm (I : Ideal R) (hI : I.IsPrime) : I.IsMaximal := by
    replace le := le.trans (nilradical_le_prime I)
    rw [← fin.coe_toFinset, ← Finset.inf_id_eq_sInf, hI.inf_le'] at le
    have ⟨M, hM, hMI⟩ := le
    rw [fin.mem_toFinset] at hM
    rwa [← hM.eq_of_le hI.1 hMI]
  exact ⟨fin.subset hpm, hpm⟩

theorem discreteTopology_of_toLocalization_surjective
    (surj : Function.Surjective (toPiLocalization R)) :
    DiscreteTopology (PrimeSpectrum R) :=
  discreteTopology_iff_finite_and_krullDimLE_zero.mpr ⟨finite_of_toPiLocalization_surjective
    surj, .mk₀ fun I prime ↦ isMaximal_of_toPiLocalization_surjective surj ⟨I, prime⟩⟩

section Comap

variable {S' : Type*} [CommSemiring S']
