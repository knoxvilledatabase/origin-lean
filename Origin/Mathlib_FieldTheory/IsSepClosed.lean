/-
Extracted from FieldTheory/IsSepClosed.lean
Genuine: 13 | Conflates: 0 | Dissolved: 7 | Infrastructure: 8
-/
import Origin.Core
import Mathlib.FieldTheory.Galois.Basic

/-!
# Separably Closed Field

In this file we define the typeclass for separably closed fields and separable closures,
and prove some of their properties.

## Main Definitions

- `IsSepClosed k` is the typeclass saying `k` is a separably closed field, i.e. every separable
  polynomial in `k` splits.

- `IsSepClosure k K` is the typeclass saying `K` is a separable closure of `k`, where `k` is a
  field. This means that `K` is separably closed and separable over `k`.

- `IsSepClosed.lift` is a map from a separable extension `L` of `K`, into any separably
  closed extension `M` of `K`.

- `IsSepClosure.equiv` is a proof that any two separable closures of the
  same field are isomorphic.

- `IsSepClosure.isAlgClosure_of_perfectField`, `IsSepClosure.of_isAlgClosure_of_perfectField`:
  if `k` is a perfect field, then its separable closure coincides with its algebraic closure.

## Tags

separable closure, separably closed

## Related

- `separableClosure`: maximal separable subextension of `K/k`, consisting of all elements of `K`
  which are separable over `k`.

- `separableClosure.isSepClosure`: if `K` is a separably closed field containing `k`, then the
  maximal separable subextension of `K/k` is a separable closure of `k`.

- In particular, a separable closure (`SeparableClosure`) exists.

- `Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed`: an algebraic extension of a separably
  closed field is purely inseparable.

-/

universe u v w

open Polynomial

variable (k : Type u) [Field k] (K : Type v) [Field K]

class IsSepClosed : Prop where
  splits_of_separable : ∀ p : k[X], p.Separable → (p.Splits <| RingHom.id k)

instance IsSepClosed.of_isAlgClosed [IsAlgClosed k] : IsSepClosed k :=
  ⟨fun p _ ↦ IsAlgClosed.splits p⟩

variable {k} {K}

theorem IsSepClosed.splits_codomain [IsSepClosed K] {f : k →+* K}
    (p : k[X]) (h : p.Separable) : p.Splits f := by
  convert IsSepClosed.splits_of_separable (p.map f) (Separable.map h); simp [splits_map_iff]

theorem IsSepClosed.splits_domain [IsSepClosed k] {f : k →+* K}
    (p : k[X]) (h : p.Separable) : p.Splits f :=
  Polynomial.splits_of_splits_id _ <| IsSepClosed.splits_of_separable _ h

namespace IsSepClosed

-- DISSOLVED: exists_root

-- DISSOLVED: exists_root_C_mul_X_pow_add_C_mul_X_add_C

-- DISSOLVED: exists_root_C_mul_X_pow_add_C_mul_X_add_C'

variable (k) in

instance (priority := 100) isAlgClosed_of_perfectField [IsSepClosed k] [PerfectField k] :
    IsAlgClosed k :=
  IsAlgClosed.of_exists_root k fun p _ h ↦ exists_root p ((degree_pos_of_irreducible h).ne')
    (PerfectField.separable_of_irreducible h)

-- DISSOLVED: exists_pow_nat_eq

-- DISSOLVED: exists_eq_mul_self

theorem roots_eq_zero_iff [IsSepClosed k] {p : k[X]} (hsep : p.Separable) :
    p.roots = 0 ↔ p = Polynomial.C (p.coeff 0) := by
  refine ⟨fun h => ?_, fun hp => by rw [hp, roots_C]⟩
  rcases le_or_lt (degree p) 0 with hd | hd
  · exact eq_C_of_degree_le_zero hd
  · obtain ⟨z, hz⟩ := IsSepClosed.exists_root p hd.ne' hsep
    rw [← mem_roots (ne_zero_of_degree_gt hd), h] at hz
    simp at hz

-- DISSOLVED: exists_eval₂_eq_zero

variable (K)

-- DISSOLVED: exists_aeval_eq_zero

variable (k) {K}

theorem of_exists_root (H : ∀ p : k[X], p.Monic → Irreducible p → Separable p → ∃ x, p.eval x = 0) :
    IsSepClosed k := by
  refine ⟨fun p hsep ↦ Or.inr ?_⟩
  intro q hq hdvd
  simp only [map_id] at hdvd
  have hlc : IsUnit (leadingCoeff q)⁻¹ := IsUnit.inv <| Ne.isUnit <|
    leadingCoeff_ne_zero.2 <| Irreducible.ne_zero hq
  have hsep' : Separable (q * C (leadingCoeff q)⁻¹) :=
    Separable.mul (Separable.of_dvd hsep hdvd) ((separable_C _).2 hlc)
    (by simpa only [← isCoprime_mul_unit_right_right (isUnit_C.2 hlc) q 1, one_mul]
      using isCoprime_one_right (x := q))
  have hirr' := hq
  rw [← irreducible_mul_isUnit (isUnit_C.2 hlc)] at hirr'
  obtain ⟨x, hx⟩ := H (q * C (leadingCoeff q)⁻¹) (monic_mul_leadingCoeff_inv hq.ne_zero) hirr' hsep'
  exact degree_mul_leadingCoeff_inv q hq.ne_zero ▸ degree_eq_one_of_irreducible_of_root hirr' hx

theorem degree_eq_one_of_irreducible [IsSepClosed k] {p : k[X]}
    (hp : Irreducible p) (hsep : p.Separable) : p.degree = 1 :=
  degree_eq_one_of_irreducible_of_splits hp (IsSepClosed.splits_codomain p hsep)

variable (K)

theorem algebraMap_surjective
    [IsSepClosed k] [Algebra k K] [Algebra.IsSeparable k K] :
    Function.Surjective (algebraMap k K) := by
  refine fun x => ⟨-(minpoly k x).coeff 0, ?_⟩
  have hq : (minpoly k x).leadingCoeff = 1 := minpoly.monic (Algebra.IsSeparable.isIntegral k x)
  have hsep : IsSeparable k x := Algebra.IsSeparable.isSeparable k x
  have h : (minpoly k x).degree = 1 :=
    degree_eq_one_of_irreducible k (minpoly.irreducible (Algebra.IsSeparable.isIntegral k x)) hsep
  have : aeval x (minpoly k x) = 0 := minpoly.aeval k x
  rw [eq_X_add_C_of_degree_eq_one h, hq, C_1, one_mul, aeval_add, aeval_X, aeval_C,
    add_eq_zero_iff_eq_neg] at this
  exact (RingHom.map_neg (algebraMap k K) ((minpoly k x).coeff 0)).symm ▸ this.symm

end IsSepClosed

theorem IntermediateField.eq_bot_of_isSepClosed_of_isSeparable [IsSepClosed k] [Algebra k K]
    (L : IntermediateField k K) [Algebra.IsSeparable k L] : L = ⊥ := bot_unique fun x hx ↦ by
  obtain ⟨y, hy⟩ := IsSepClosed.algebraMap_surjective k L ⟨x, hx⟩
  exact ⟨y, congr_arg (algebraMap L K) hy⟩

variable (k) (K)

class IsSepClosure [Algebra k K] : Prop where
  sep_closed : IsSepClosed K
  separable : Algebra.IsSeparable k K

instance IsSepClosure.self_of_isSepClosed [IsSepClosed k] : IsSepClosure k k :=
  ⟨by assumption, Algebra.isSeparable_self k⟩

instance (priority := 100) IsSepClosure.isAlgClosure_of_perfectField_top
    [Algebra k K] [IsSepClosure k K] [PerfectField K] : IsAlgClosure k K :=
  haveI : IsSepClosed K := IsSepClosure.sep_closed k
  ⟨inferInstance, IsSepClosure.separable.isAlgebraic⟩

instance (priority := 100) IsSepClosure.isAlgClosure_of_perfectField
    [Algebra k K] [IsSepClosure k K] [PerfectField k] : IsAlgClosure k K :=
  have halg : Algebra.IsAlgebraic k K := IsSepClosure.separable.isAlgebraic
  haveI := halg.perfectField; inferInstance

instance (priority := 100) IsSepClosure.of_isAlgClosure_of_perfectField
    [Algebra k K] [IsAlgClosure k K] [PerfectField k] : IsSepClosure k K :=
  ⟨haveI := IsAlgClosure.isAlgClosed (R := k) (K := K); inferInstance,
    (IsAlgClosure.isAlgebraic (R := k) (K := K)).isSeparable_of_perfectField⟩

variable {k} {K}

theorem isSepClosure_iff [Algebra k K] :
    IsSepClosure k K ↔ IsSepClosed K ∧ Algebra.IsSeparable k K :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

namespace IsSepClosure

instance isSeparable [Algebra k K] [IsSepClosure k K] : Algebra.IsSeparable k K :=
  IsSepClosure.separable

instance (priority := 100) isGalois [Algebra k K] [IsSepClosure k K] : IsGalois k K where
  to_isSeparable := IsSepClosure.separable
  to_normal.toIsAlgebraic :=  inferInstance
  to_normal.splits' x := (IsSepClosure.sep_closed k).splits_codomain _
    (Algebra.IsSeparable.isSeparable k x)

end IsSepClosure

namespace IsSepClosed

variable {K : Type u} (L : Type v) {M : Type w} [Field K] [Field L] [Algebra K L] [Field M]
  [Algebra K M] [IsSepClosed M]

theorem surjective_restrictDomain_of_isSeparable {E : Type*}
    [Field E] [Algebra K E] [Algebra L E] [IsScalarTower K L E] [Algebra.IsSeparable L E] :
    Function.Surjective fun φ : E →ₐ[K] M ↦ φ.restrictDomain L :=
  fun f ↦ IntermediateField.exists_algHom_of_splits' (E := E) f
    fun s ↦ ⟨Algebra.IsSeparable.isIntegral L s,
      IsSepClosed.splits_codomain _ <| Algebra.IsSeparable.isSeparable L s⟩

alias surjective_comp_algebraMap_of_isSeparable := surjective_restrictDomain_of_isSeparable

variable [Algebra.IsSeparable K L] {L}

noncomputable irreducible_def lift : L →ₐ[K] M :=
  Classical.choice <| IntermediateField.nonempty_algHom_of_adjoin_splits
    (fun x _ ↦ ⟨Algebra.IsSeparable.isIntegral K x,
      splits_codomain _ (Algebra.IsSeparable.isSeparable K x)⟩)
    (IntermediateField.adjoin_univ K L)

end IsSepClosed

namespace IsSepClosure

variable (K : Type u) [Field K] (L : Type v) (M : Type w) [Field L] [Field M]

variable [Algebra K M] [IsSepClosure K M]

variable [Algebra K L] [IsSepClosure K L]

noncomputable def equiv : L ≃ₐ[K] M :=
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10754): added to replace local instance above
  haveI : IsSepClosed L := IsSepClosure.sep_closed K
  haveI : IsSepClosed M := IsSepClosure.sep_closed K
  AlgEquiv.ofBijective _ (Normal.toIsAlgebraic.algHom_bijective₂
    (IsSepClosed.lift : L →ₐ[K] M) (IsSepClosed.lift : M →ₐ[K] L)).1

end IsSepClosure
