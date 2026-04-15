/-
Extracted from Topology/Algebra/UniformField.lean
Genuine: 4 of 13 | Dissolved: 3 | Infrastructure: 6
-/
import Origin.Core
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.UniformRing

/-!
# Completion of topological fields

The goal of this file is to prove the main part of Proposition 7 of Bourbaki GT III 6.8 :

The completion `hat K` of a Hausdorff topological field is a field if the image under
the mapping `x ↦ x⁻¹` of every Cauchy filter (with respect to the additive uniform structure)
which does not have a cluster point at `0` is a Cauchy filter
(with respect to the additive uniform structure).

Bourbaki does not give any detail here, he refers to the general discussion of extending
functions defined on a dense subset with values in a complete Hausdorff space. In particular
the subtlety about clustering at zero is totally left to readers.

Note that the separated completion of a non-separated topological field is the zero ring, hence
the separation assumption is needed. Indeed the kernel of the completion map is the closure of
zero which is an ideal. Hence it's either zero (and the field is separated) or the full field,
which implies one is sent to zero and the completion ring is trivial.

The main definition is `CompletableTopField` which packages the assumptions as a Prop-valued
type class and the main results are the instances `UniformSpace.Completion.Field` and
`UniformSpace.Completion.TopologicalDivisionRing`.
-/

noncomputable section

open uniformity Topology

open Set UniformSpace UniformSpace.Completion Filter

variable (K : Type*) [Field K] [UniformSpace K]

local notation "hat" => Completion

class CompletableTopField extends T0Space K : Prop where
  nice : ∀ F : Filter K, Cauchy F → 𝓝 0 ⊓ F = ⊥ → Cauchy (map (fun x => x⁻¹) F)

namespace UniformSpace

namespace Completion

instance (priority := 100) [T0Space K] : Nontrivial (hat K) :=
  ⟨⟨0, 1, fun h => zero_ne_one <| (isUniformEmbedding_coe K).injective h⟩⟩

variable {K}

def hatInv : hat K → hat K :=
  isDenseInducing_coe.extend fun x : K => (↑x⁻¹ : hat K)

-- DISSOLVED: continuous_hatInv

open Classical in

instance instInvCompletion : Inv (hat K) :=
  ⟨fun x => if x = 0 then 0 else hatInv x⟩

variable [TopologicalDivisionRing K]

-- DISSOLVED: hatInv_extends

variable [CompletableTopField K]

@[norm_cast]
theorem coe_inv (x : K) : (x : hat K)⁻¹ = ((x⁻¹ : K) : hat K) := by
  by_cases h : x = 0
  · rw [h, inv_zero]
    dsimp [Inv.inv]
    norm_cast
    simp
  · conv_lhs => dsimp [Inv.inv]
    rw [if_neg]
    · exact hatInv_extends h
    · exact fun H => h (isDenseEmbedding_coe.injective H)

variable [UniformAddGroup K]

-- DISSOLVED: mul_hatInv_cancel

instance instField : Field (hat K) where
  exists_pair_ne := ⟨0, 1, fun h => zero_ne_one ((isUniformEmbedding_coe K).injective h)⟩
  mul_inv_cancel := fun x x_ne => by simp only [Inv.inv, if_neg x_ne, mul_hatInv_cancel x_ne]
  inv_zero := by simp only [Inv.inv, ite_true]
  -- TODO: use a better defeq
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

instance : TopologicalDivisionRing (hat K) :=
  { Completion.topologicalRing with
    continuousAt_inv₀ := by
      intro x x_ne
      have : { y | hatInv y = y⁻¹ } ∈ 𝓝 x :=
        haveI : {(0 : hat K)}ᶜ ⊆ { y : hat K | hatInv y = y⁻¹ } := by
          intro y y_ne
          rw [mem_compl_singleton_iff] at y_ne
          dsimp [Inv.inv]
          rw [if_neg y_ne]
        mem_of_superset (compl_singleton_mem_nhds x_ne) this
      exact ContinuousAt.congr (continuous_hatInv x_ne) this }

end Completion

end UniformSpace

variable (L : Type*) [Field L] [UniformSpace L] [CompletableTopField L]

instance Subfield.completableTopField (K : Subfield L) : CompletableTopField K where
  nice F F_cau inf_F := by
    let i : K →+* L := K.subtype
    have hi : IsUniformInducing i := isUniformEmbedding_subtype_val.isUniformInducing
    rw [← hi.cauchy_map_iff] at F_cau ⊢
    rw [map_comm (show (i ∘ fun x => x⁻¹) = (fun x => x⁻¹) ∘ i by ext; rfl)]
    apply CompletableTopField.nice _ F_cau
    rw [← Filter.push_pull', ← map_zero i, ← hi.isInducing.nhds_eq_comap, inf_F, Filter.map_bot]

instance (priority := 100) completableTopField_of_complete (L : Type*) [Field L] [UniformSpace L]
    [TopologicalDivisionRing L] [T0Space L] [CompleteSpace L] : CompletableTopField L where
  nice F cau_F hF := by
    haveI : NeBot F := cau_F.1
    rcases CompleteSpace.complete cau_F with ⟨x, hx⟩
    have hx' : x ≠ 0 := by
      rintro rfl
      rw [inf_eq_right.mpr hx] at hF
      exact cau_F.1.ne hF
    exact Filter.Tendsto.cauchy_map <|
      calc
        map (fun x => x⁻¹) F ≤ map (fun x => x⁻¹) (𝓝 x) := map_mono hx
        _ ≤ 𝓝 x⁻¹ := continuousAt_inv₀ hx'

variable {α β : Type*} [Field β] [b : UniformSpace β] [CompletableTopField β]
  [Field α]

theorem IsUniformInducing.completableTopField
    [UniformSpace α] [T0Space α]
    {f : α →+* β} (hf : IsUniformInducing f) :
    CompletableTopField α := by
  refine CompletableTopField.mk (fun F F_cau inf_F => ?_)
  rw [← IsUniformInducing.cauchy_map_iff hf] at F_cau ⊢
  have h_comm : (f ∘ fun x => x⁻¹) = (fun x => x⁻¹) ∘ f := by
    ext; simp only [Function.comp_apply, map_inv₀, Subfield.coe_inv]
  rw [Filter.map_comm h_comm]
  apply CompletableTopField.nice _ F_cau
  rw [← Filter.push_pull', ← map_zero f, ← hf.isInducing.nhds_eq_comap, inf_F, Filter.map_bot]
