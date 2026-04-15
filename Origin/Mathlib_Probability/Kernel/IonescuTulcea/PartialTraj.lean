/-
Extracted from Probability/Kernel/IonescuTulcea/PartialTraj.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Consecutive composition of kernels

This file is the first step towards Ionescu-Tulcea theorem, which allows for instance to construct
the product of an infinite family of probability measures. The idea of the statement is as follows:
consider a family of kernels `κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))`.
One can interpret `κ n` as a kernel which takes as an input the trajectory of a point started in
`X 0` and moving `X 0 → X 1 → X 2 → ... → X n` and which outputs the distribution of the next
position of the point in `X (n + 1)`. If `a b : ℕ` and `a < b`, we can compose the kernels,
and `κ a ⊗ₖ κ (a + 1) ⊗ₖ ... ⊗ₖ κ b` takes the trajectory up to time `a` as input and outputs
the distribution of the trajectory in `X (a + 1) × ... × X (b + 1)`.

The Ionescu-Tulcea theorem then tells us that these compositions can be extended into a kernel
`η : Kernel (Π i : Iic a, X i) → Π n > a, X n` which given the trajectory up to time `a` outputs
the distribution of the infinite trajectory started in `X (a + 1)`. In other words this theorem
makes sense of composing infinitely many kernels together.

To be able to even state the theorem we want to take the composition-product
(see `ProbabilityTheory.Kernel.compProd`) of consecutive kernels.
This however is not straightforward.

Consider `n : ℕ`. We cannot write `(κ n) ⊗ₖ (κ (n + 1))` directly, we need to first
introduce an equivalence to see `κ (n + 1)` as a kernel with codomain
`(Π i : Iic n, X i) × X (n + 1)`, and we get a `Kernel (Π i : Iic n, X i) (X (n + 1) × (X (n + 2))`.
However we want to do multiple composition at once, i.e. write
`(κ n) ⊗ₖ ... ⊗ₖ (κ m)` for `n < m`. This requires even more equivalences to make sense of, and at
the end of the day we get kernels which still cannot be composed together.

To tackle this issue, we decide here to only consider kernels of the form
`Kernel (Π i : Iic a, X i) (Π i : Iic b, X i)`. In other words these kernels take as input
a trajectory up to time `a` and output the distribution of the full trajectory up to time `b`.
This is captured in the definition `partialTraj κ a b`
(`partialTraj` stands for "partial trajectory").
The advantage of this approach is that it allows us to write for instance
`partialTraj κ b c ∘ₖ partialTraj κ a b = partialTraj κ a c` (see `partialTraj_comp_partialTraj`.)

In this file we therefore define this family of kernels and prove some properties of it.
In particular we provide at the end of the file some results to compute the integral of a function
against `partialTraj κ a b`, taking inspiration from `MeasureTheory.lmarginal`.

## Main definitions

* `partialTraj κ a b`: Given the trajectory of a point up to time `a`, returns the distribution
  of the trajectory up to time `b`.
* `lmarginalPartialTraj κ a b f`: The integral of `f` against `partialTraj κ a b`.
  This is essentially the integral of `f` against `κ (a + 1) ⊗ₖ ... ⊗ₖ κ b` but seen as depending
  on all the variables, mimicking `MeasureTheory.lmarginal`. This allows to write
  `lmarginalPartialTraj κ b c (lmarginalPartialTraj κ a b f)`.

## Main statements

* `partialTraj_comp_partialTraj`: if `a ≤ b` and `b ≤ c` then
  `partialTraj κ b c ∘ₖ partialTraj κ a b = partialTraj κ a c`.
* `map_partialTraj_succ_self a`: the pushforward of `partialTraj κ a (a + 1)` along the point at
  time `a + 1` is the kernel `κ a`.
* `lmarginalPartialTraj_self` : if `a ≤ b` and `b ≤ c` then
  `lmarginalPartialTraj κ b c (lmarginalPartialTraj κ a b f) = lmarginalPartialTraj κ a c`.

## Tags

Ionescu-Tulcea theorem, composition of kernels
-/

open Finset Function MeasureTheory Preorder ProbabilityTheory

open scoped ENNReal

variable {X : ℕ → Type*} {mX : ∀ n, MeasurableSpace (X n)} {a b c : ℕ}
  {κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))}

section partialTraj

/-! ### Definition of `partialTraj` -/

namespace ProbabilityTheory.Kernel

open MeasurableEquiv

variable (κ) in

noncomputable def partialTraj (a b : ℕ) : Kernel (Π i : Iic a, X i) (Π i : Iic b, X i) :=
  if h : b ≤ a then deterministic (frestrictLe₂ h) (measurable_frestrictLe₂ h)
  else @Nat.leRec a (fun b _ ↦ Kernel (Π i : Iic a, X i) (Π i : Iic b, X i)) Kernel.id
    (fun k _ κ_k ↦ ((Kernel.id ×ₖ ((κ k).map (piSingleton k))) ∘ₖ κ_k).map (IicProdIoc k (k + 1)))
    b (Nat.le_of_not_ge h)

section Basic

lemma partialTraj_le (hba : b ≤ a) :
    partialTraj κ a b = deterministic (frestrictLe₂ hba) (measurable_frestrictLe₂ _) := by
  rw [partialTraj, dif_pos hba]
