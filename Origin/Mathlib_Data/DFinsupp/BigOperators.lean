/-
Extracted from Data/DFinsupp/BigOperators.lean
Genuine: 28 | Conflates: 0 | Dissolved: 19 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Data.DFinsupp.Ext

/-!
# Dependent functions with finite support

For a non-dependent version see `Mathlib.Data.Finsupp.Defs`.

## Notation

This file introduces the notation `Π₀ a, β a` as notation for `DFinsupp β`, mirroring the `α →₀ β`
notation used for `Finsupp`. This works for nested binders too, with `Π₀ a b, γ a b` as notation
for `DFinsupp (fun a ↦ DFinsupp (γ a))`.

## Implementation notes

The support is internally represented (in the primed `DFinsupp.support'`) as a `Multiset` that
represents a superset of the true support of the function, quotiented by the always-true relation so
that this does not impact equality. This approach has computational benefits over storing a
`Finset`; it allows us to add together two finitely-supported functions without
having to evaluate the resulting function to recompute its support (which would required
decidability of `b = 0` for `b : β i`).

The true support of the function can still be recovered with `DFinsupp.support`; but these
decidability obligations are now postponed to when the support is actually needed. As a consequence,
there are two ways to sum a `DFinsupp`: with `DFinsupp.sum` which works over an arbitrary function
but requires recomputation of the support and therefore a `Decidable` argument; and with
`DFinsupp.sumAddHom` which requires an additive morphism, using its properties to show that
summing over a superset of the support is sufficient.

`Finsupp` takes an altogether different approach here; it uses `Classical.Decidable` and declares
the `Add` instance as noncomputable. This design difference is independent of the fact that
`DFinsupp` is dependently-typed and `Finsupp` is not; in future, we may want to align these two
definitions, or introduce two more definitions for the other combinations of decisions.
-/

universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}

namespace DFinsupp

section Algebra

def evalAddMonoidHom [∀ i, AddZeroClass (β i)] (i : ι) : (Π₀ i, β i) →+ β i :=
  (Pi.evalAddMonoidHom β i).comp coeFnAddMonoidHom

@[simp, norm_cast]
theorem coe_finset_sum {α} [∀ i, AddCommMonoid (β i)] (s : Finset α) (g : α → Π₀ i, β i) :
    ⇑(∑ a ∈ s, g a) = ∑ a ∈ s, ⇑(g a) :=
  map_sum coeFnAddMonoidHom g s

@[simp]
theorem finset_sum_apply {α} [∀ i, AddCommMonoid (β i)] (s : Finset α) (g : α → Π₀ i, β i) (i : ι) :
    (∑ a ∈ s, g a) i = ∑ a ∈ s, g a i :=
  map_sum (evalAddMonoidHom i) g s

end Algebra

section ProdAndSum

variable [DecidableEq ι]

-- DISSOLVED: prod

@[to_additive (attr := simp)]
theorem _root_.map_dfinsupp_prod
    {R S H : Type*} [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [CommMonoid R] [CommMonoid S] [FunLike H R S] [MonoidHomClass H R S] (h : H) (f : Π₀ i, β i)
    (g : ∀ i, β i → R) : h (f.prod g) = f.prod fun a b => h (g a b) :=
  map_prod _ _ _

-- DISSOLVED: prod_mapRange_index

-- DISSOLVED: prod_zero_index

-- DISSOLVED: prod_single_index

-- DISSOLVED: prod_neg_index

-- DISSOLVED: prod_comm

-- DISSOLVED: sum_apply

-- DISSOLVED: support_sum

@[to_additive (attr := simp)]
theorem prod_one [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ]
    {f : Π₀ i, β i} : (f.prod fun _ _ => (1 : γ)) = 1 :=
  Finset.prod_const_one

@[to_additive (attr := simp)]
theorem prod_mul [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ]
    {f : Π₀ i, β i} {h₁ h₂ : ∀ i, β i → γ} :
    (f.prod fun i b => h₁ i b * h₂ i b) = f.prod h₁ * f.prod h₂ :=
  Finset.prod_mul_distrib

@[to_additive (attr := simp)]
theorem prod_inv [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommGroup γ]
    {f : Π₀ i, β i} {h : ∀ i, β i → γ} : (f.prod fun i b => (h i b)⁻¹) = (f.prod h)⁻¹ :=
  (map_prod (invMonoidHom : γ →* γ) _ f.support).symm

-- DISSOLVED: prod_eq_one

-- DISSOLVED: smul_sum

-- DISSOLVED: prod_add_index

@[to_additive (attr := simp)]
theorem prod_eq_prod_fintype [Fintype ι] [∀ i, Zero (β i)] [∀ (i : ι) (x : β i), Decidable (x ≠ 0)]
    -- Porting note: `f` was a typeclass argument
    [CommMonoid γ] (v : Π₀ i, β i) {f : ∀ i, β i → γ} (hf : ∀ i, f i 0 = 1) :
    v.prod f = ∏ i, f i (DFinsupp.equivFunOnFintype v i) := by
  suffices (∏ i ∈ v.support, f i (v i)) = ∏ i, f i (v i) by simp [DFinsupp.prod, this]
  apply Finset.prod_subset v.support.subset_univ
  intro i _ hi
  rw [mem_support_iff, not_not] at hi
  rw [hi, hf]

section CommMonoidWithZero

variable [Π i, Zero (β i)] [CommMonoidWithZero γ] [Nontrivial γ] [NoZeroDivisors γ]
  [Π i, DecidableEq (β i)] {f : Π₀ i, β i} {g : Π i, β i → γ}

@[simp]
lemma prod_eq_zero_iff : f.prod g = 0 ↔ ∃ i ∈ f.support, g i (f i) = 0 := Finset.prod_eq_zero_iff

-- DISSOLVED: prod_ne_zero_iff

end CommMonoidWithZero

def sumAddHom [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (φ : ∀ i, β i →+ γ) :
    (Π₀ i, β i) →+ γ where
  toFun f :=
    (f.support'.lift fun s => ∑ i ∈ Multiset.toFinset s.1, φ i (f i)) <| by
      rintro ⟨sx, hx⟩ ⟨sy, hy⟩
      dsimp only [Subtype.coe_mk, toFun_eq_coe] at *
      have H1 : sx.toFinset ∩ sy.toFinset ⊆ sx.toFinset := Finset.inter_subset_left
      have H2 : sx.toFinset ∩ sy.toFinset ⊆ sy.toFinset := Finset.inter_subset_right
      refine
        (Finset.sum_subset H1 ?_).symm.trans
          ((Finset.sum_congr rfl ?_).trans (Finset.sum_subset H2 ?_))
      · intro i H1 H2
        rw [Finset.mem_inter] at H2
        simp only [Multiset.mem_toFinset] at H1 H2
        convert AddMonoidHom.map_zero (φ i)
        exact (hy i).resolve_left (mt (And.intro H1) H2)
      · intro i _
        rfl
      · intro i H1 H2
        rw [Finset.mem_inter] at H2
        simp only [Multiset.mem_toFinset] at H1 H2
        convert AddMonoidHom.map_zero (φ i)
        exact (hx i).resolve_left (mt (fun H3 => And.intro H3 H1) H2)
  map_add' := by
    rintro ⟨f, sf, hf⟩ ⟨g, sg, hg⟩
    change (∑ i ∈ _, _) = (∑ i ∈ _, _) + ∑ i ∈ _, _
    simp only [coe_add, coe_mk', Subtype.coe_mk, Pi.add_apply, map_add, Finset.sum_add_distrib]
    congr 1
    · refine (Finset.sum_subset ?_ ?_).symm
      · intro i
        simp only [Multiset.mem_toFinset, Multiset.mem_add]
        exact Or.inl
      · intro i _ H2
        simp only [Multiset.mem_toFinset, Multiset.mem_add] at H2
        rw [(hf i).resolve_left H2, AddMonoidHom.map_zero]
    · refine (Finset.sum_subset ?_ ?_).symm
      · intro i
        simp only [Multiset.mem_toFinset, Multiset.mem_add]
        exact Or.inr
      · intro i _ H2
        simp only [Multiset.mem_toFinset, Multiset.mem_add] at H2
        rw [(hg i).resolve_left H2, AddMonoidHom.map_zero]
  map_zero' := by
    simp only [toFun_eq_coe, coe_zero, Pi.zero_apply, map_zero, Finset.sum_const_zero]; rfl

@[simp]
theorem sumAddHom_single [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (φ : ∀ i, β i →+ γ) (i)
    (x : β i) : sumAddHom φ (single i x) = φ i x := by
  dsimp [sumAddHom, single, Trunc.lift_mk]
  rw [Multiset.toFinset_singleton, Finset.sum_singleton, Pi.single_eq_same]

@[simp]
theorem sumAddHom_comp_single [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (f : ∀ i, β i →+ γ)
    (i : ι) : (sumAddHom f).comp (singleAddHom β i) = f i :=
  AddMonoidHom.ext fun x => sumAddHom_single f i x

-- DISSOLVED: sumAddHom_apply

theorem sumAddHom_comm {ι₁ ι₂ : Sort _} {β₁ : ι₁ → Type*} {β₂ : ι₂ → Type*} {γ : Type*}
    [DecidableEq ι₁] [DecidableEq ι₂] [∀ i, AddZeroClass (β₁ i)] [∀ i, AddZeroClass (β₂ i)]
    [AddCommMonoid γ] (f₁ : Π₀ i, β₁ i) (f₂ : Π₀ i, β₂ i) (h : ∀ i j, β₁ i →+ β₂ j →+ γ) :
    sumAddHom (fun i₂ => sumAddHom (fun i₁ => h i₁ i₂) f₁) f₂ =
      sumAddHom (fun i₁ => sumAddHom (fun i₂ => (h i₁ i₂).flip) f₂) f₁ := by
  obtain ⟨⟨f₁, s₁, h₁⟩, ⟨f₂, s₂, h₂⟩⟩ := f₁, f₂
  simp only [sumAddHom, AddMonoidHom.finset_sum_apply, Quotient.liftOn_mk, AddMonoidHom.coe_mk,
    AddMonoidHom.flip_apply, Trunc.lift, toFun_eq_coe, ZeroHom.coe_mk, coe_mk']
  exact Finset.sum_comm

@[simps apply symm_apply]
def liftAddHom [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] :
    (∀ i, β i →+ γ) ≃+ ((Π₀ i, β i) →+ γ) where
  toFun := sumAddHom
  invFun F i := F.comp (singleAddHom β i)
  left_inv x := by ext; simp
  right_inv ψ := by ext; simp
  map_add' F G := by ext; simp

@[simp, nolint simpNF] -- Porting note: linter claims that simp can prove this, but it can not
theorem liftAddHom_singleAddHom [∀ i, AddCommMonoid (β i)] :
    liftAddHom (β := β) (singleAddHom β) = AddMonoidHom.id (Π₀ i, β i) :=
  (liftAddHom (β := β)).toEquiv.apply_eq_iff_eq_symm_apply.2 rfl

theorem liftAddHom_apply_single [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (f : ∀ i, β i →+ γ)
    (i : ι) (x : β i) : liftAddHom (β := β) f (single i x) = f i x := by simp

theorem liftAddHom_comp_single [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (f : ∀ i, β i →+ γ)
    (i : ι) : (liftAddHom (β := β) f).comp (singleAddHom β i) = f i := by simp

theorem comp_liftAddHom {δ : Type*} [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] [AddCommMonoid δ]
    (g : γ →+ δ) (f : ∀ i, β i →+ γ) :
    g.comp (liftAddHom (β := β) f) = liftAddHom (β := β) fun a => g.comp (f a) :=
  (liftAddHom (β := β)).symm_apply_eq.1 <|
    funext fun a => by
      rw [liftAddHom_symm_apply, AddMonoidHom.comp_assoc, liftAddHom_comp_single]

@[simp]
theorem sumAddHom_zero [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] :
    (sumAddHom fun i => (0 : β i →+ γ)) = 0 :=
  map_zero (liftAddHom (β := β))

@[simp]
theorem sumAddHom_add [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (g : ∀ i, β i →+ γ)
    (h : ∀ i, β i →+ γ) : (sumAddHom fun i => g i + h i) = sumAddHom g + sumAddHom h :=
  map_add (liftAddHom (β := β)) _ _

@[simp]
theorem sumAddHom_singleAddHom [∀ i, AddCommMonoid (β i)] :
    sumAddHom (singleAddHom β) = AddMonoidHom.id _ :=
  liftAddHom_singleAddHom

theorem comp_sumAddHom {δ : Type*} [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] [AddCommMonoid δ]
    (g : γ →+ δ) (f : ∀ i, β i →+ γ) : g.comp (sumAddHom f) = sumAddHom fun a => g.comp (f a) :=
  comp_liftAddHom _ _

-- DISSOLVED: sum_sub_index

-- DISSOLVED: prod_finset_sum_index

-- DISSOLVED: prod_sum_index

-- DISSOLVED: sum_single

-- DISSOLVED: prod_subtypeDomain_index

theorem subtypeDomain_sum {ι} {β : ι → Type v} [∀ i, AddCommMonoid (β i)] {s : Finset γ}
    {h : γ → Π₀ i, β i} {p : ι → Prop} [DecidablePred p] :
    (∑ c ∈ s, h c).subtypeDomain p = ∑ c ∈ s, (h c).subtypeDomain p :=
  map_sum (subtypeDomainAddMonoidHom β p) _ s

-- DISSOLVED: subtypeDomain_finsupp_sum

end ProdAndSum

end DFinsupp

/-! ### Product and sum lemmas for bundled morphisms.

In this section, we provide analogues of `AddMonoidHom.map_sum`, `AddMonoidHom.coe_finset_sum`,
and `AddMonoidHom.finset_sum_apply` for `DFinsupp.sum` and `DFinsupp.sumAddHom` instead of
`Finset.sum`.

We provide these for `AddMonoidHom`, `MonoidHom`, `RingHom`, `AddEquiv`, and `MulEquiv`.

Lemmas for `LinearMap` and `LinearEquiv` are in another file.
-/

section

variable [DecidableEq ι]

namespace MonoidHom

variable {R S : Type*}

variable [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]

@[to_additive (attr := simp, norm_cast)]
theorem coe_dfinsupp_prod [Monoid R] [CommMonoid S] (f : Π₀ i, β i) (g : ∀ i, β i → R →* S) :
    ⇑(f.prod g) = f.prod fun a b => ⇑(g a b) :=
  coe_finset_prod _ _

@[to_additive]
theorem dfinsupp_prod_apply [Monoid R] [CommMonoid S] (f : Π₀ i, β i) (g : ∀ i, β i → R →* S)
    (r : R) : (f.prod g) r = f.prod fun a b => (g a b) r :=
  finset_prod_apply _ _ _

end MonoidHom

/-! The above lemmas, repeated for `DFinsupp.sumAddHom`. -/

namespace AddMonoidHom

variable {R S : Type*}

open DFinsupp

@[simp]
theorem map_dfinsupp_sumAddHom [AddCommMonoid R] [AddCommMonoid S] [∀ i, AddZeroClass (β i)]
    (h : R →+ S) (f : Π₀ i, β i) (g : ∀ i, β i →+ R) :
    h (sumAddHom g f) = sumAddHom (fun i => h.comp (g i)) f :=
  DFunLike.congr_fun (comp_liftAddHom h g) f

theorem dfinsupp_sumAddHom_apply [AddZeroClass R] [AddCommMonoid S] [∀ i, AddZeroClass (β i)]
    (f : Π₀ i, β i) (g : ∀ i, β i →+ R →+ S) (r : R) :
    (sumAddHom g f) r = sumAddHom (fun i => (eval r).comp (g i)) f :=
  map_dfinsupp_sumAddHom (eval r) f g

@[simp, norm_cast]
theorem coe_dfinsupp_sumAddHom [AddZeroClass R] [AddCommMonoid S] [∀ i, AddZeroClass (β i)]
    (f : Π₀ i, β i) (g : ∀ i, β i →+ R →+ S) :
    ⇑(sumAddHom g f) = sumAddHom (fun i => (coeFn R S).comp (g i)) f :=
  map_dfinsupp_sumAddHom (coeFn R S) f g

end AddMonoidHom

namespace RingHom

variable {R S : Type*}

open DFinsupp

@[simp]
theorem map_dfinsupp_sumAddHom [NonAssocSemiring R] [NonAssocSemiring S] [∀ i, AddZeroClass (β i)]
    (h : R →+* S) (f : Π₀ i, β i) (g : ∀ i, β i →+ R) :
    h (sumAddHom g f) = sumAddHom (fun i => h.toAddMonoidHom.comp (g i)) f :=
  DFunLike.congr_fun (comp_liftAddHom h.toAddMonoidHom g) f

end RingHom

namespace AddEquiv

variable {R S : Type*}

open DFinsupp

@[simp]
theorem map_dfinsupp_sumAddHom [AddCommMonoid R] [AddCommMonoid S] [∀ i, AddZeroClass (β i)]
    (h : R ≃+ S) (f : Π₀ i, β i) (g : ∀ i, β i →+ R) :
    h (sumAddHom g f) = sumAddHom (fun i => h.toAddMonoidHom.comp (g i)) f :=
  DFunLike.congr_fun (comp_liftAddHom h.toAddMonoidHom g) f

end AddEquiv

end
