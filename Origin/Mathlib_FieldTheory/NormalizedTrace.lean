/-
Extracted from FieldTheory/NormalizedTrace.lean
Genuine: 7 of 9 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!

# Normalized trace

This file defines the *normalized trace* map; that is, an `F`-linear map from the algebraic closure
of `F` to `F` defined as the trace of an element from its adjoin extension divided by its degree.

To avoid heavy imports, we define it here as a map from an arbitrary algebraic (equivalently
integral) extension of `F`.

## Main definitions

- `normalizedTrace`: the trace of an element from the simple adjoin divided by the degree;
  it is a non-trivial `F`-linear map from an arbitrary algebraic extension `K` to `F`.

## Main results

- `normalizedTrace_intermediateField`: for a tower `K / E / F` of algebraic extensions,
  `normalizedTrace F E` agrees with `normalizedTrace F K` on `E`.
- `normalizedTrace_trans`: for a tower `K / E / F` of algebraic extensions, the normalized trace
  from `K` to `E` composed with the normalized trace from `E` to `F` equals the normalized trace
  from `K` to `F`.
- `normalizedTrace_self`: `normalizedTrace F F` is the identity map.

-/

namespace Algebra

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

open IntermediateField

set_option backward.privateInPublic true in

private noncomputable def normalizedTraceAux (a : K) : F :=
  (Module.finrank F F⟮a⟯ : F)⁻¹ • trace F F⟮a⟯ (AdjoinSimple.gen F a)

private theorem normalizedTraceAux_map {E : Type*} [Field E] [Algebra F E] (f : E →ₐ[F] K) (a : E) :
    normalizedTraceAux F K (f a) = normalizedTraceAux F E a := by
  let e := (F⟮a⟯.equivMap f).trans (equivOfEq <| Set.image_singleton ▸ adjoin_map F {a} f)
  simp_rw [normalizedTraceAux, ← LinearEquiv.finrank_eq e.toLinearEquiv]
  congr
  exact trace_eq_of_algEquiv e <| AdjoinSimple.gen F a

private theorem normalizedTraceAux_intermediateField {E : IntermediateField F K} (a : E) :
    normalizedTraceAux F K a = normalizedTraceAux F E a :=
  normalizedTraceAux_map F K E.val a

variable [CharZero F]

variable {K} in

private theorem normalizedTraceAux_eq_of_finiteDimensional [FiniteDimensional F K] (a : K) :
    normalizedTraceAux F K a = (Module.finrank F K : F)⁻¹ • trace F K a := by
  have h := (Nat.cast_ne_zero (R := F)).mpr <|
    Nat.pos_iff_ne_zero.mp <| Module.finrank_pos (R := F⟮a⟯) (M := K)
  rw [smul_eq_mul, mul_comm, ← div_eq_mul_inv, trace_eq_trace_adjoin F a,
    ← Module.finrank_mul_finrank F F⟮a⟯ K, nsmul_eq_mul, Nat.cast_mul, mul_comm,
    mul_div_mul_right _ _ h, div_eq_mul_inv, mul_comm, ← smul_eq_mul, normalizedTraceAux_def]

variable [Algebra.IsIntegral F K]

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

noncomputable def normalizedTrace : K →ₗ[F] F where
  toFun := normalizedTraceAux F K
  map_add' a b := by
    let E := F⟮a⟯ ⊔ F⟮b⟯
    have : FiniteDimensional F F⟮a⟯ := adjoin.finiteDimensional (IsIntegral.isIntegral a)
    have : FiniteDimensional F F⟮b⟯ := adjoin.finiteDimensional (IsIntegral.isIntegral b)
    have ha : a ∈ E := (le_sup_left : F⟮a⟯ ≤ E) <| mem_adjoin_simple_self F a
    have hb : b ∈ E := (le_sup_right : F⟮b⟯ ≤ E) <| mem_adjoin_simple_self F b
    have hab : a + b ∈ E := IntermediateField.add_mem E ha hb
    let a' : E := ⟨a, ha⟩
    let b' : E := ⟨b, hb⟩
    let ab' : E := ⟨a + b, hab⟩
    rw [normalizedTraceAux_intermediateField F K a',
      normalizedTraceAux_intermediateField F K b',
      normalizedTraceAux_intermediateField F K ab',
      normalizedTraceAux_eq_of_finiteDimensional F a',
      normalizedTraceAux_eq_of_finiteDimensional F b',
      normalizedTraceAux_eq_of_finiteDimensional F ab',
      ← smul_add, ← map_add, AddMemClass.mk_add_mk]
  map_smul' m a := by
    dsimp only [AddHom.toFun_eq_coe, AddHom.coe_mk, RingHom.id_apply]
    let E := F⟮a⟯
    have : FiniteDimensional F F⟮a⟯ := adjoin.finiteDimensional (IsIntegral.isIntegral a)
    have ha : a ∈ E := mem_adjoin_simple_self F a
    have hma : m • a ∈ E := smul_mem E ha
    let a' : E := ⟨a, ha⟩
    let ma' : E := ⟨m • a, hma⟩
    rw [normalizedTraceAux_intermediateField F K a',
      normalizedTraceAux_intermediateField F K ma',
      normalizedTraceAux_eq_of_finiteDimensional F a',
      normalizedTraceAux_eq_of_finiteDimensional F ma',
      smul_comm, ← map_smul _ m, SetLike.mk_smul_mk]

variable {K} in

theorem normalizedTrace_minpoly (a : K) :
    normalizedTrace F K a = ((minpoly F a).natDegree : F)⁻¹ • -(minpoly F a).nextCoeff :=
  have ha : IsIntegral F a := IsIntegral.isIntegral a
  IntermediateField.adjoin.finrank ha ▸ trace_adjoinSimpleGen ha ▸ normalizedTrace_def F K a

variable {F} in

theorem normalizedTrace_self_apply (a : F) : normalizedTrace F F a = a := by
  dsimp [normalizedTrace]
  rw [normalizedTraceAux_eq_of_finiteDimensional F a, Module.finrank_self F,
    Nat.cast_one, inv_one, one_smul, trace_self_apply]
