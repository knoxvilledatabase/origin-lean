/-
Extracted from Data/FunLike/Fintype.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.Finite.Prod

/-!
# Finiteness of `DFunLike` types

We show a type `F` with a `DFunLike F α β` is finite if both `α` and `β` are finite.
This corresponds to the following two pairs of declarations:

 * `DFunLike.fintype` is a definition stating all `DFunLike`s are finite if their domain and
   codomain are.
 * `DFunLike.finite` is a lemma stating all `DFunLike`s are finite if their domain and
   codomain are.
 * `FunLike.fintype` is a non-dependent version of `DFunLike.fintype` and
 * `FunLike.finite` is a non-dependent version of `DFunLike.finite`, because dependent instances
   are harder to infer.

You can use these to produce instances for specific `DFunLike` types.
(Although there might be options for `Fintype` instances with better definitional behaviour.)
They can't be instances themselves since they can cause loops.
-/

section Type'

variable (F G : Type*) {α γ : Type*} {β : α → Type*} [DFunLike F α β] [FunLike G α γ]

noncomputable def DFunLike.fintype [DecidableEq α] [Fintype α] [∀ i, Fintype (β i)] : Fintype F :=
  Fintype.ofInjective _ DFunLike.coe_injective

noncomputable def FunLike.fintype [DecidableEq α] [Fintype α] [Fintype γ] : Fintype G :=
  DFunLike.fintype G

end Type'

section Sort'

variable (F G : Sort*) {α γ : Sort*} {β : α → Sort*} [DFunLike F α β] [FunLike G α γ]

theorem DFunLike.finite [Finite α] [∀ i, Finite (β i)] : Finite F :=
  Finite.of_injective _ DFunLike.coe_injective

theorem FunLike.finite [Finite α] [Finite γ] : Finite G :=
  DFunLike.finite G

end Sort'

instance (priority := 100) FunLike.toDecidableEq {F α β : Type*}
    [DecidableEq β] [Fintype α] [FunLike F α β] : DecidableEq F :=
  fun a b ↦ decidable_of_iff ((a : α → β) = b) DFunLike.coe_injective.eq_iff
