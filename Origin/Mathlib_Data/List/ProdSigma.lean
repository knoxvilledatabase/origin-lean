/-
Extracted from Data/List/ProdSigma.lean
Genuine: 6 | Conflates: 0 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core
import Mathlib.Data.List.Basic
import Mathlib.Data.Sigma.Basic

/-!
# Lists in product and sigma types

This file proves basic properties of `List.product` and `List.sigma`, which are list constructions
living in `Prod` and `Sigma` types respectively. Their definitions can be found in
[`Data.List.Defs`](./defs). Beware, this is not about `List.prod`, the multiplicative product.
-/

variable {α β : Type*}

namespace List

/-! ### product -/

@[simp]
theorem nil_product (l : List β) : (@nil α) ×ˢ l = [] :=
  rfl

@[simp]
theorem product_cons (a : α) (l₁ : List α) (l₂ : List β) :
    (a :: l₁) ×ˢ l₂ = map (fun b => (a, b)) l₂ ++ (l₁ ×ˢ l₂) :=
  rfl

@[simp]
theorem product_nil : ∀ l : List α, l ×ˢ (@nil β) = []
  | [] => rfl
  | _ :: l => by simp [product_cons, product_nil l]

@[simp]
theorem mem_product {l₁ : List α} {l₂ : List β} {a : α} {b : β} :
    (a, b) ∈ l₁ ×ˢ l₂ ↔ a ∈ l₁ ∧ b ∈ l₂ := by
  simp_all [SProd.sprod, product, mem_flatMap, mem_map, Prod.ext_iff, exists_prop, and_left_comm,
    exists_and_left, exists_eq_left, exists_eq_right]

theorem length_product (l₁ : List α) (l₂ : List β) :
    length (l₁ ×ˢ l₂) = length l₁ * length l₂ := by
  induction' l₁ with x l₁ IH
  · exact (Nat.zero_mul _).symm
  · simp only [length, product_cons, length_append, IH, Nat.add_mul, Nat.one_mul, length_map,
      Nat.add_comm]

/-! ### sigma -/

variable {σ : α → Type*}

@[simp]
theorem nil_sigma (l : ∀ a, List (σ a)) : (@nil α).sigma l = [] :=
  rfl

@[simp]
theorem sigma_cons (a : α) (l₁ : List α) (l₂ : ∀ a, List (σ a)) :
    (a :: l₁).sigma l₂ = map (Sigma.mk a) (l₂ a) ++ l₁.sigma l₂ :=
  rfl

@[simp]
theorem sigma_nil : ∀ l : List α, (l.sigma fun a => @nil (σ a)) = []
  | [] => rfl
  | _ :: l => by simp [sigma_cons, sigma_nil l]

@[simp]
theorem mem_sigma {l₁ : List α} {l₂ : ∀ a, List (σ a)} {a : α} {b : σ a} :
    Sigma.mk a b ∈ l₁.sigma l₂ ↔ a ∈ l₁ ∧ b ∈ l₂ a := by
  simp [List.sigma, mem_flatMap, mem_map, exists_prop, exists_and_left, and_left_comm,
    exists_eq_left, heq_iff_eq, exists_eq_right]

set_option linter.deprecated false in

theorem length_sigma' (l₁ : List α) (l₂ : ∀ a, List (σ a)) :
    length (l₁.sigma l₂) = Nat.sum (l₁.map fun a ↦ length (l₂ a)) := by
  induction' l₁ with x l₁ IH
  · rfl
  · simp only [map, sigma_cons, length_append, length_map, IH, Nat.sum_cons]

end List
