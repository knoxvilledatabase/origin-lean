/-
Extracted from LinearAlgebra/Projection.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Projection to a subspace

In this file we define
* `Submodule.linearProjOfIsCompl (p q : Submodule R E) (h : IsCompl p q)`:
  the projection of a module `E` to a submodule `p` along its complement `q`;
  it is the unique linear map `f : E → p` such that `f x = x` for `x ∈ p` and `f x = 0` for `x ∈ q`.
* `Submodule.isComplEquivProj p`: equivalence between submodules `q`
  such that `IsCompl p q` and projections `f : E → p`, `∀ x ∈ p, f x = x`.

We also provide some lemmas justifying correctness of our definitions.

## Tags

projection, complement subspace
-/

noncomputable section Ring

variable {R : Type*} [Ring R] {E : Type*} [AddCommGroup E] [Module R E]

variable {F : Type*} [AddCommGroup F] [Module R F] {G : Type*} [AddCommGroup G] [Module R G]

variable (p q : Submodule R E)

variable {S : Type*} [Semiring S] {M : Type*} [AddCommMonoid M] [Module S M] (m : Submodule S M)

namespace LinearMap

variable {p}

open Submodule

theorem ker_id_sub_eq_of_proj {f : E →ₗ[R] p} (hf : ∀ x : p, f x = x) :
    ker (id - p.subtype.comp f) = p := by
  ext x
  simp only [comp_apply, mem_ker, subtype_apply, sub_apply, id_apply, sub_eq_zero]
  exact ⟨fun h => h.symm ▸ Submodule.coe_mem _, fun hx => by rw [hf ⟨x, hx⟩, Subtype.coe_mk]⟩

theorem range_eq_of_proj {f : E →ₗ[R] p} (hf : ∀ x : p, f x = x) : range f = ⊤ :=
  range_eq_top.2 fun x => ⟨x, hf x⟩

theorem isCompl_of_proj {f : E →ₗ[R] p} (hf : ∀ x : p, f x = x) : IsCompl p (ker f) := by
  constructor
  · rw [disjoint_iff_inf_le]
    rintro x ⟨hpx, hfx⟩
    rw [SetLike.mem_coe, mem_ker, hf ⟨x, hpx⟩, mk_eq_zero] at hfx
    simp only [hfx, zero_mem]
  · rw [codisjoint_iff_le_sup]
    intro x _
    rw [mem_sup']
    refine ⟨f x, ⟨x - f x, ?_⟩, add_sub_cancel _ _⟩
    rw [mem_ker, map_sub, hf, sub_self]

end LinearMap

namespace Submodule

open LinearMap

def quotientEquivOfIsCompl (h : IsCompl p q) : (E ⧸ p) ≃ₗ[R] q :=
  LinearEquiv.symm <|
    LinearEquiv.ofBijective (p.mkQ.comp q.subtype)
      ⟨by rw [← ker_eq_bot, ker_comp, ker_mkQ, disjoint_iff_comap_eq_bot.1 h.symm.disjoint], by
        rw [← range_eq_top, range_comp, range_subtype, map_mkQ_eq_top, h.sup_eq_top]⟩
