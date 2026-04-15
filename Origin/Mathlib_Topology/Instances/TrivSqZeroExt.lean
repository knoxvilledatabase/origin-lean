/-
Extracted from Topology/Instances/TrivSqZeroExt.lean
Genuine: 9 of 11 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

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

-- INSTANCE (free from Core): instTopologicalSpace

-- INSTANCE (free from Core): [T2Space

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
  continuous_id.prodMk continuous_const

theorem continuous_inr [Zero R] : Continuous (inr : M → tsze R M) :=
  continuous_const.prodMk continuous_id

theorem IsEmbedding.inl [Zero M] : IsEmbedding (inl : R → tsze R M) :=
  .of_comp continuous_inl continuous_fst .id

theorem IsEmbedding.inr [Zero R] : IsEmbedding (inr : M → tsze R M) :=
  .of_comp continuous_inr continuous_snd .id

variable (R M)
