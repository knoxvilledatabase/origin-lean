/-
Extracted from FieldTheory/PurelyInseparable/Basic.lean
Genuine: 13 of 15 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!

# Basic results about purely inseparable extensions

This file contains basic definitions and results about purely inseparable extensions.

## Main definitions

- `IsPurelyInseparable`: typeclass for purely inseparable field extensions: an algebraic extension
  `E / F` is purely inseparable if and only if the minimal polynomial of every element of `E ∖ F`
  is not separable.

## Main results

- `IsPurelyInseparable.surjective_algebraMap_of_isSeparable`,
  `IsPurelyInseparable.bijective_algebraMap_of_isSeparable`,
  `IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable`:
  if `E / F` is both purely inseparable and separable, then `algebraMap F E` is surjective
  (hence bijective). In particular, if an intermediate field of `E / F` is both purely inseparable
  and separable, then it is equal to `F`.

- `isPurelyInseparable_iff_pow_mem`: a field extension `E / F` of exponential characteristic `q` is
  purely inseparable if and only if for every element `x` of `E`, there exists a natural number `n`
  such that `x ^ (q ^ n)` is contained in `F`.

- `IsPurelyInseparable.trans`: if `E / F` and `K / E` are both purely inseparable extensions, then
  `K / F` is also purely inseparable.

- `isPurelyInseparable_iff_natSepDegree_eq_one`: `E / F` is purely inseparable if and only if for
  every element `x` of `E`, its minimal polynomial has separable degree one.

- `isPurelyInseparable_iff_minpoly_eq_X_pow_sub_C`: a field extension `E / F` of exponential
  characteristic `q` is purely inseparable if and only if for every element `x` of `E`, the minimal
  polynomial of `x` over `F` is of form `X ^ (q ^ n) - y` for some natural number `n` and some
  element `y` of `F`.

- `isPurelyInseparable_iff_minpoly_eq_X_sub_C_pow`: a field extension `E / F` of exponential
  characteristic `q` is purely inseparable if and only if for every element `x` of `E`, the minimal
  polynomial of `x` over `F` is of form `(X - x) ^ (q ^ n)` for some natural number `n`.

- `isPurelyInseparable_iff_finSepDegree_eq_one`: an extension is purely inseparable
  if and only if it has finite separable degree (`Field.finSepDegree`) one.

- `IsPurelyInseparable.normal`: a purely inseparable extension is normal.

- `separableClosure.isPurelyInseparable`: if `E / F` is algebraic, then `E` is purely inseparable
  over the separable closure of `F` in `E`.

- `separableClosure_le_iff`: if `E / F` is algebraic, then an intermediate field of `E / F` contains
  the separable closure of `F` in `E` if and only if `E` is purely inseparable over it.

- `eq_separableClosure_iff`: if `E / F` is algebraic, then an intermediate field of `E / F` is equal
  to the separable closure of `F` in `E` if and only if it is separable over `F`, and `E`
  is purely inseparable over it.

- `IsPurelyInseparable.injective_comp_algebraMap`: if `E / F` is purely inseparable, then for any
  reduced ring `L`, the map `(E →+* L) → (F →+* L)` induced by `algebraMap F E` is injective.
  In particular, a purely inseparable field extension is an epimorphism in the category of fields.

- `IsPurelyInseparable.of_injective_comp_algebraMap`: if `L` is an algebraically closed field
  containing `E`, such that the map `(E →+* L) → (F →+* L)` induced by `algebraMap F E` is
  injective, then `E / F` is purely inseparable. As a corollary, epimorphisms in the category of
  fields must be purely inseparable extensions.

- `Field.finSepDegree_eq`: if `E / F` is algebraic, then the `Field.finSepDegree F E` is equal to
  `Field.sepDegree F E` as a natural number. This means that the cardinality of `Field.Emb F E`
  and the degree of `(separableClosure F E) / F` are both finite or infinite, and when they are
  finite, they coincide.

- `Field.finSepDegree_mul_finInsepDegree`: the finite separable degree multiply by the finite
  inseparable degree is equal to the (finite) field extension degree.

## Tags

separable degree, degree, separable closure, purely inseparable

-/

open Module Polynomial IntermediateField Field

noncomputable section

universe u v w

section General

variable (F E : Type*) [CommRing F] [Ring E] [Algebra F E]

variable (K : Type*) [Ring K] [Algebra F K]

class IsPurelyInseparable : Prop where
  isIntegral : Algebra.IsIntegral F E
  inseparable' (x : E) : IsSeparable F x → x ∈ (algebraMap F E).range

attribute [instance] IsPurelyInseparable.isIntegral

variable {E} in

theorem IsPurelyInseparable.isIntegral' [IsPurelyInseparable F E] (x : E) : IsIntegral F x :=
  Algebra.IsIntegral.isIntegral _

theorem IsPurelyInseparable.isAlgebraic [Nontrivial F] [IsPurelyInseparable F E] :
    Algebra.IsAlgebraic F E := inferInstance

variable {E}

theorem IsPurelyInseparable.inseparable [IsPurelyInseparable F E] :
    ∀ x : E, IsSeparable F x → x ∈ (algebraMap F E).range :=
  IsPurelyInseparable.inseparable'

variable {F}

theorem isPurelyInseparable_iff : IsPurelyInseparable F E ↔ ∀ x : E,
    IsIntegral F x ∧ (IsSeparable F x → x ∈ (algebraMap F E).range) :=
  ⟨fun h x ↦ ⟨h.isIntegral' _ x, h.inseparable' x⟩, fun h ↦ ⟨⟨fun x ↦ (h x).1⟩, fun x ↦ (h x).2⟩⟩

variable {K}

theorem AlgEquiv.isPurelyInseparable (e : K ≃ₐ[F] E) [IsPurelyInseparable F K] :
    IsPurelyInseparable F E := by
  refine ⟨⟨fun _ ↦ by rw [← isIntegral_algEquiv e.symm]; exact IsPurelyInseparable.isIntegral' F _⟩,
    fun x h ↦ ?_⟩
  rw [IsSeparable, ← minpoly.algEquiv_eq e.symm] at h
  simpa only [RingHom.mem_range, algebraMap_eq_apply] using IsPurelyInseparable.inseparable F _ h

theorem AlgEquiv.isPurelyInseparable_iff (e : K ≃ₐ[F] E) :
    IsPurelyInseparable F K ↔ IsPurelyInseparable F E :=
  ⟨fun _ ↦ e.isPurelyInseparable, fun _ ↦ e.symm.isPurelyInseparable⟩

-- INSTANCE (free from Core): Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed

variable (F E K)

theorem IsPurelyInseparable.surjective_algebraMap_of_isSeparable
    [IsPurelyInseparable F E] [Algebra.IsSeparable F E] : Function.Surjective (algebraMap F E) :=
  fun x ↦ IsPurelyInseparable.inseparable F x (Algebra.IsSeparable.isSeparable F x)

theorem IsPurelyInseparable.bijective_algebraMap_of_isSeparable
    [Nontrivial E] [IsDomain F] [IsTorsionFree F E]
    [IsPurelyInseparable F E] [Algebra.IsSeparable F E] : Function.Bijective (algebraMap F E) :=
  ⟨FaithfulSMul.algebraMap_injective F E, surjective_algebraMap_of_isSeparable F E⟩

variable {F E} in

theorem Subalgebra.eq_bot_of_isPurelyInseparable_of_isSeparable (L : Subalgebra F E)
    [IsPurelyInseparable F L] [Algebra.IsSeparable F L] : L = ⊥ := bot_unique fun x hx ↦ by
  obtain ⟨y, hy⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable F L ⟨x, hx⟩
  exact ⟨y, congr_arg (Subalgebra.val _) hy⟩

theorem IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E] (L : IntermediateField F E)
    [IsPurelyInseparable F L] [Algebra.IsSeparable F L] : L = ⊥ := bot_unique fun x hx ↦ by
  obtain ⟨y, hy⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable F L ⟨x, hx⟩
  exact ⟨y, congr_arg (algebraMap L E) hy⟩

theorem separableClosure.eq_bot_of_isPurelyInseparable
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E] [IsPurelyInseparable F E] :
    separableClosure F E = ⊥ :=
  bot_unique fun x h ↦ IsPurelyInseparable.inseparable F x (mem_separableClosure_iff.1 h)

theorem separableClosure.eq_bot_iff
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E] :
    separableClosure F E = ⊥ ↔ IsPurelyInseparable F E :=
  ⟨fun h ↦ isPurelyInseparable_iff.2 fun x ↦ ⟨Algebra.IsIntegral.isIntegral x, fun hs ↦ by
    simpa only [h] using mem_separableClosure_iff.2 hs⟩, fun _ ↦ eq_bot_of_isPurelyInseparable F E⟩

-- INSTANCE (free from Core): isPurelyInseparable_self

variable (F : Type u) {E : Type v} [Field F] [Ring E] [IsDomain E] [Algebra F E]

variable (q : ℕ) [ExpChar F q] (x : E)
