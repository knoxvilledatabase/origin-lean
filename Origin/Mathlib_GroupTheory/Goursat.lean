/-
Extracted from GroupTheory/Goursat.lean
Genuine: 10 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Group.Graph
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Goursat's lemma for subgroups

This file proves Goursat's lemma for subgroups.

If `I` is a subgroup of `G × H` which projects fully on both factors, then there exist normal
subgroups `G' ≤ G` and `H' ≤ H` such that `G' × H' ≤ I` and the image of `I` in `G ⧸ G' × H ⧸ H'` is
the graph of an isomorphism `G ⧸ G' ≃ H ⧸ H'`.

`G'` and `H'` can be explicitly constructed as `Subgroup.goursatFst I` and `Subgroup.goursatSnd I`
respectively.
-/

open Function Set

namespace Subgroup

variable {G H : Type*} [Group G] [Group H] {I : Subgroup (G × H)}
  (hI₁ : Surjective (Prod.fst ∘ I.subtype)) (hI₂ : Surjective (Prod.snd ∘ I.subtype))

variable (I) in

@[to_additive
"For `I` a subgroup of `G × H`, `I.goursatFst` is the kernel of the projection map `I → H`,
considered as a subgroup of `G`.
This is the first subgroup appearing in Goursat's lemma. See `AddSubgroup.goursat`."]
def goursatFst : Subgroup G :=
  ((MonoidHom.snd G H).comp I.subtype).ker.map ((MonoidHom.fst G H).comp I.subtype)

variable (I) in

@[to_additive
"For `I` a subgroup of `G × H`, `I.goursatSnd` is the kernel of the projection map `I → G`,
considered as a subgroup of `H`.
This is the second subgroup appearing in Goursat's lemma. See `AddSubgroup.goursat`."]
def goursatSnd : Subgroup H :=
  ((MonoidHom.fst G H).comp I.subtype).ker.map ((MonoidHom.snd G H).comp I.subtype)

@[to_additive (attr := simp)]
lemma mem_goursatFst {g : G} : g ∈ I.goursatFst ↔ (g, 1) ∈ I := by simp [goursatFst]

@[to_additive (attr := simp)]
lemma mem_goursatSnd {h : H} : h ∈ I.goursatSnd ↔ (1, h) ∈ I := by simp [goursatSnd]

include hI₁ in

@[to_additive] lemma normal_goursatFst : I.goursatFst.Normal := .map inferInstance _ hI₁

include hI₂ in

@[to_additive] lemma normal_goursatSnd : I.goursatSnd.Normal := .map inferInstance _ hI₂

include hI₁ hI₂ in

@[to_additive]
lemma mk_goursatFst_eq_iff_mk_goursatSnd_eq {x y : G × H} (hx : x ∈ I) (hy : y ∈ I) :
    (x.1 : G ⧸ I.goursatFst) = y.1 ↔ (x.2 : H ⧸ I.goursatSnd) = y.2 := by
  have := normal_goursatFst hI₁
  have := normal_goursatSnd hI₂
  rw [eq_comm]
  simp [QuotientGroup.eq_iff_div_mem]
  constructor <;> intro h
  · simpa [Prod.mul_def, Prod.div_def] using div_mem (mul_mem h hx) hy
  · simpa [Prod.mul_def, Prod.div_def] using div_mem (mul_mem h hy) hx

lemma goursatFst_prod_goursatSnd_le : I.goursatFst.prod I.goursatSnd ≤ I := by
  rintro ⟨g, h⟩ ⟨hg, hh⟩
  simpa using mul_mem (mem_goursatFst.1 hg) (mem_goursatSnd.1 hh)

@[to_additive
"**Goursat's lemma** for a subgroup of with surjective projections.
If `I` is a subgroup of `G × H` which projects fully on both factors, then there exist normal
subgroups `M ≤ G` and `N ≤ H` such that `G' × H' ≤ I` and the image of `I` in `G ⧸ M × H ⧸ N` is the
graph of an isomorphism `G ⧸ M ≃ H ⧸ N'`.
`G'` and `H'` can be explicitly constructed as `I.goursatFst` and `I.goursatSnd` respectively."]
lemma goursat_surjective :
    have := normal_goursatFst hI₁
    have := normal_goursatSnd hI₂
    ∃ e : G ⧸ I.goursatFst ≃* H ⧸ I.goursatSnd,
      (((QuotientGroup.mk' _).prodMap (QuotientGroup.mk' _)).comp I.subtype).range =
        e.toMonoidHom.graph := by
  have := normal_goursatFst hI₁
  have := normal_goursatSnd hI₂
  exact (((QuotientGroup.mk' I.goursatFst).prodMap
    (QuotientGroup.mk' I.goursatSnd)).comp I.subtype).exists_mulEquiv_range_eq_graph
    ((QuotientGroup.mk'_surjective _).comp hI₁) ((QuotientGroup.mk'_surjective _).comp hI₂)
    fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ mk_goursatFst_eq_iff_mk_goursatSnd_eq hI₁ hI₂ hx hy

@[to_additive
"**Goursat's lemma** for an arbitrary subgroup.
If `I` is a subgroup of `G × H`, then there exist subgroups `G' ≤ G`, `H' ≤ H` and normal subgroups
`M ≤ G'` and `N ≤ H'` such that `M × N ≤ I` and the image of `I` in `G' ⧸ M × H' ⧸ N` is the graph
of an isomorphism `G ⧸ G' ≃ H ⧸ H'`."]
lemma goursat :
    ∃ (G' : Subgroup G) (H' : Subgroup H) (M : Subgroup G') (N : Subgroup H') (_ : M.Normal)
      (_ : N.Normal) (e : G' ⧸ M ≃* H' ⧸ N),
      I = (e.toMonoidHom.graph.comap <| (QuotientGroup.mk' M).prodMap (QuotientGroup.mk' N)).map
        (G'.subtype.prodMap H'.subtype) := by
  let G' := I.map (MonoidHom.fst ..)
  let H' := I.map (MonoidHom.snd ..)
  let P : I →* G' := (MonoidHom.fst ..).subgroupMap I
  let Q : I →* H' := (MonoidHom.snd ..).subgroupMap I
  let I' : Subgroup (G' × H') := (P.prod Q).range
  have hI₁' : Surjective (Prod.fst ∘ I'.subtype) := by
    simp only [← MonoidHom.coe_fst, ← MonoidHom.coe_comp, ← MonoidHom.range_eq_top,
      MonoidHom.range_comp, Subgroup.range_subtype, I']
    simp only [← MonoidHom.range_comp, MonoidHom.fst_comp_prod, MonoidHom.range_eq_top]
    exact (MonoidHom.fst ..).subgroupMap_surjective I
  have hI₂' : Surjective (Prod.snd ∘ I'.subtype) := by
    simp only [← MonoidHom.coe_snd, ← MonoidHom.coe_comp, ← MonoidHom.range_eq_top,
      MonoidHom.range_comp, Subgroup.range_subtype, I']
    simp only [← MonoidHom.range_comp, MonoidHom.fst_comp_prod, MonoidHom.range_eq_top]
    exact (MonoidHom.snd ..).subgroupMap_surjective I
  have := normal_goursatFst hI₁'
  have := normal_goursatSnd hI₂'
  obtain ⟨e, he⟩ := goursat_surjective hI₁' hI₂'
  refine ⟨I.map (MonoidHom.fst ..), I.map (MonoidHom.snd ..),
    I'.goursatFst, I'.goursatSnd, inferInstance, inferInstance, e, ?_⟩
  rw [← he]
  simp only [MonoidHom.range_comp, Subgroup.range_subtype, I']
  rw [comap_map_eq_self]
  · ext ⟨g, h⟩
    constructor
    · intro hgh
      simpa only [mem_map, MonoidHom.mem_range, MonoidHom.prod_apply, Subtype.exists, Prod.exists,
        MonoidHom.coe_prodMap, coeSubtype, Prod.mk.injEq, Prod.map_apply, MonoidHom.coe_snd,
        exists_eq_right, exists_and_right, exists_eq_right_right, MonoidHom.coe_fst]
        using ⟨⟨h, hgh⟩, ⟨g, hgh⟩, g, h, hgh, ⟨rfl, rfl⟩⟩
    · simp only [mem_map, MonoidHom.mem_range, MonoidHom.prod_apply, Subtype.exists, Prod.exists,
        MonoidHom.coe_prodMap, coeSubtype, Prod.mk.injEq, Prod.map_apply, MonoidHom.coe_snd,
        exists_eq_right, exists_and_right, exists_eq_right_right, MonoidHom.coe_fst,
        forall_exists_index, and_imp]
      rintro h₁ hgh₁ g₁ hg₁h g₂ h₂ hg₂h₂ hP hQ
      simp only [Subtype.ext_iff] at hP hQ
      rwa [← hP, ← hQ]
  · rintro ⟨⟨g, _⟩, ⟨h, _⟩⟩ hgh
    simp only [MonoidHom.prodMap, MonoidHom.mem_ker, MonoidHom.prod_apply, MonoidHom.coe_comp,
      QuotientGroup.coe_mk', MonoidHom.coe_fst, comp_apply, MonoidHom.coe_snd, Prod.mk_eq_one,
      QuotientGroup.eq_one_iff, mem_goursatFst, MonoidHom.mem_range, Prod.mk.injEq, Subtype.exists,
      Prod.exists, mem_goursatSnd] at hgh
    rcases hgh with ⟨⟨g₁, h₁, hg₁h₁, hPQ₁⟩, ⟨g₂, h₂, hg₂h₂, hPQ₂⟩⟩
    simp only [Subtype.ext_iff] at hPQ₁ hPQ₂
    rcases hPQ₁ with ⟨rfl, rfl⟩
    rcases hPQ₂ with ⟨rfl, rfl⟩
    simp only [MonoidHom.mem_range, MonoidHom.prod_apply, Prod.mk.injEq, Subtype.exists,
      Prod.exists]
    refine ⟨g₁, h₂, ?_, rfl, rfl⟩
    simpa only [OneMemClass.coe_one, Prod.mk_mul_mk, mul_one, one_mul] using mul_mem hg₁h₁ hg₂h₂

end Subgroup
