/-
Extracted from Topology/Instances/TrivSqZeroExt.lean
Genuine: 18 of 34 | Dissolved: 0 | Infrastructure: 16
-/
import Origin.Core
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Topology on `TrivSqZeroExt R M`

The type `TrivSqZeroExt R M` inherits the topology from `R × M`.

Note that this is not the topology induced by the seminorm on the dual numbers suggested by
[this Math.SE answer](https://math.stackexchange.com/a/1056378/1896), which instead induces
the topology pulled back through the projection map `TrivSqZeroExt.fst : tsze R M → R`.
Obviously, that topology is not Hausdorff and using it would result in `exp` converging to more than
one value.

## Main results

* `TrivSqZeroExt.topologicalRing`: the ring operations are continuous

-/

open Topology

variable {α S R M : Type*}

local notation "tsze" => TrivSqZeroExt

namespace TrivSqZeroExt

section Topology

variable [TopologicalSpace R] [TopologicalSpace M]

instance instTopologicalSpace : TopologicalSpace (tsze R M) :=
  TopologicalSpace.induced fst ‹_› ⊓ TopologicalSpace.induced snd ‹_›

instance [T2Space R] [T2Space M] : T2Space (tsze R M) :=
  Prod.t2Space

theorem nhds_def (x : tsze R M) : 𝓝 x = 𝓝 x.fst ×ˢ 𝓝 x.snd := nhds_prod_eq

theorem nhds_inl [Zero M] (x : R) : 𝓝 (inl x : tsze R M) = 𝓝 x ×ˢ 𝓝 0 :=
  nhds_def _

theorem nhds_inr [Zero R] (m : M) : 𝓝 (inr m : tsze R M) = 𝓝 0 ×ˢ 𝓝 m :=
  nhds_def _

nonrec theorem continuous_fst : Continuous (fst : tsze R M → R) :=
  continuous_fst

nonrec theorem continuous_snd : Continuous (snd : tsze R M → M) :=
  continuous_snd

theorem continuous_inl [Zero M] : Continuous (inl : R → tsze R M) :=
  continuous_id.prod_mk continuous_const

theorem continuous_inr [Zero R] : Continuous (inr : M → tsze R M) :=
  continuous_const.prod_mk continuous_id

theorem IsEmbedding.inl [Zero M] : IsEmbedding (inl : R → tsze R M) :=
  .of_comp continuous_inl continuous_fst .id

alias embedding_inl := IsEmbedding.inl

theorem IsEmbedding.inr [Zero R] : IsEmbedding (inr : M → tsze R M) :=
  .of_comp continuous_inr continuous_snd .id

alias embedding_inr := IsEmbedding.inr

variable (R M)

@[simps]
def fstCLM [CommSemiring R] [AddCommMonoid M] [Module R M] : tsze R M →L[R] R :=
  { ContinuousLinearMap.fst R R M with toFun := fst }

@[simps]
def sndCLM [CommSemiring R] [AddCommMonoid M] [Module R M] : tsze R M →L[R] M :=
  { ContinuousLinearMap.snd R R M with
    toFun := snd
    cont := continuous_snd }

@[simps]
def inlCLM [CommSemiring R] [AddCommMonoid M] [Module R M] : R →L[R] tsze R M :=
  { ContinuousLinearMap.inl R R M with toFun := inl }

@[simps]
def inrCLM [CommSemiring R] [AddCommMonoid M] [Module R M] : M →L[R] tsze R M :=
  { ContinuousLinearMap.inr R R M with toFun := inr }

variable {R M}

instance [Add R] [Add M] [ContinuousAdd R] [ContinuousAdd M] : ContinuousAdd (tsze R M) :=
  Prod.continuousAdd

instance [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] [ContinuousMul R] [ContinuousSMul R M]
    [ContinuousSMul Rᵐᵒᵖ M] [ContinuousAdd M] : ContinuousMul (tsze R M) :=
  ⟨((continuous_fst.comp continuous_fst).mul (continuous_fst.comp continuous_snd)).prod_mk <|
      ((continuous_fst.comp continuous_fst).smul (continuous_snd.comp continuous_snd)).add
        ((MulOpposite.continuous_op.comp <| continuous_fst.comp <| continuous_snd).smul
          (continuous_snd.comp continuous_fst))⟩

instance [Neg R] [Neg M] [ContinuousNeg R] [ContinuousNeg M] : ContinuousNeg (tsze R M) :=
  Prod.continuousNeg

theorem topologicalSemiring [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
    [TopologicalSemiring R] [ContinuousAdd M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M] :
    TopologicalSemiring (tsze R M) := { }

instance [Ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [TopologicalRing R]
    [TopologicalAddGroup M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M] :
    TopologicalRing (tsze R M) where

instance [SMul S R] [SMul S M] [ContinuousConstSMul S R] [ContinuousConstSMul S M] :
    ContinuousConstSMul S (tsze R M) :=
  Prod.continuousConstSMul

instance [TopologicalSpace S] [SMul S R] [SMul S M] [ContinuousSMul S R] [ContinuousSMul S M] :
    ContinuousSMul S (tsze R M) :=
  Prod.continuousSMul

variable (M)

theorem hasSum_inl [AddCommMonoid R] [AddCommMonoid M] {f : α → R} {a : R} (h : HasSum f a) :
    HasSum (fun x ↦ inl (f x)) (inl a : tsze R M) :=
  h.map (⟨⟨inl, inl_zero _⟩, inl_add _⟩ : R →+ tsze R M) continuous_inl

theorem hasSum_inr [AddCommMonoid R] [AddCommMonoid M] {f : α → M} {a : M} (h : HasSum f a) :
    HasSum (fun x ↦ inr (f x)) (inr a : tsze R M) :=
  h.map (⟨⟨inr, inr_zero _⟩, inr_add _⟩ : M →+ tsze R M) continuous_inr

theorem hasSum_fst [AddCommMonoid R] [AddCommMonoid M] {f : α → tsze R M} {a : tsze R M}
    (h : HasSum f a) : HasSum (fun x ↦ fst (f x)) (fst a) :=
  h.map (⟨⟨fst, fst_zero⟩, fst_add⟩ : tsze R M →+ R) continuous_fst

theorem hasSum_snd [AddCommMonoid R] [AddCommMonoid M] {f : α → tsze R M} {a : tsze R M}
    (h : HasSum f a) : HasSum (fun x ↦ snd (f x)) (snd a) :=
  h.map (⟨⟨snd, snd_zero⟩, snd_add⟩ : tsze R M →+ M) continuous_snd

end Topology

section Uniformity

variable [UniformSpace R] [UniformSpace M]

instance instUniformSpace : UniformSpace (tsze R M) where
  toTopologicalSpace := instTopologicalSpace
  __ := instUniformSpaceProd

instance [CompleteSpace R] [CompleteSpace M] : CompleteSpace (tsze R M) :=
  inferInstanceAs <| CompleteSpace (R × M)

instance [AddGroup R] [AddGroup M] [UniformAddGroup R] [UniformAddGroup M] :
    UniformAddGroup (tsze R M) :=
  inferInstanceAs <| UniformAddGroup (R × M)

open Uniformity

theorem uniformity_def :
    𝓤 (tsze R M) =
      ((𝓤 R).comap fun p => (p.1.fst, p.2.fst)) ⊓ ((𝓤 M).comap fun p => (p.1.snd, p.2.snd)) :=
  rfl

nonrec theorem uniformContinuous_fst : UniformContinuous (fst : tsze R M → R) :=
  uniformContinuous_fst

nonrec theorem uniformContinuous_snd : UniformContinuous (snd : tsze R M → M) :=
  uniformContinuous_snd

theorem uniformContinuous_inl [Zero M] : UniformContinuous (inl : R → tsze R M) :=
  uniformContinuous_id.prod_mk uniformContinuous_const

theorem uniformContinuous_inr [Zero R] : UniformContinuous (inr : M → tsze R M) :=
  uniformContinuous_const.prod_mk uniformContinuous_id

end Uniformity

end TrivSqZeroExt
