/-
Extracted from LinearAlgebra/FreeModule/Basic.lean
Genuine: 11 of 16 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Free modules

We introduce a class `Module.Free R M`, for `R` a `Semiring` and `M` an `R`-module and we provide
several basic instances for this class.

Use `Finsupp.linearCombination_id_surjective` to prove that any module is the quotient of a free
module.

## Main definition

* `Module.Free R M` : the class of free `R`-modules.
-/

assert_not_exists DirectSum Matrix TensorProduct

universe u v w z

variable {ι : Type*} (R : Type u) (M : Type v) (N : Type z)

namespace Module

section Basic

variable [Semiring R] [AddCommMonoid M] [Module R M]

class Free (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] : Prop where
  exists_basis (R M) : Nonempty <| (I : Type v) × Basis I R M

lemma Free.exists_set [Free R M] : ∃ S : Set M, Nonempty (Basis S R M) :=
  let ⟨_I, b⟩ := exists_basis R M; ⟨Set.range b, ⟨b.reindexRange⟩⟩

theorem free_iff_set : Free R M ↔ ∃ S : Set M, Nonempty (Basis S R M) :=
  ⟨fun _ ↦ Free.exists_set .., fun ⟨S, hS⟩ ↦ ⟨nonempty_sigma.2 ⟨S, hS⟩⟩⟩

theorem free_def [Small.{w, v} M] : Free R M ↔ ∃ I : Type w, Nonempty (Basis I R M) where
  mp h :=
    ⟨Shrink (Set.range h.exists_basis.some.2),
      ⟨(Basis.reindexRange h.exists_basis.some.2).reindex (equivShrink _)⟩⟩
  mpr h := ⟨(nonempty_sigma.2 h).map fun ⟨_, b⟩ => ⟨Set.range b, b.reindexRange⟩⟩

variable {R M}

theorem Free.of_basis {ι : Type w} (b : Basis ι R M) : Free R M :=
  (free_def R M).2 ⟨Set.range b, ⟨b.reindexRange⟩⟩

end Basic

namespace Free

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M] [Module.Free R M]

variable [AddCommMonoid N] [Module R N]

def ChooseBasisIndex : Type _ :=
  ((Module.free_iff_set R M).mp ‹_›).choose

-- INSTANCE (free from Core): :

noncomputable def chooseBasis : Basis (ChooseBasisIndex R M) R M :=
  ((Module.free_iff_set R M).mp ‹_›).choose_spec.some

noncomputable def constr {S : Type z} [Semiring S] [Module S N] [SMulCommClass R S N] :
    (ChooseBasisIndex R M → N) ≃ₗ[S] M →ₗ[R] N :=
  Basis.constr (chooseBasis R M) S

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): [Nontrivial

theorem infinite [Infinite R] [Nontrivial M] : Infinite M :=
  (Equiv.infinite_iff (chooseBasis R M).repr.toEquiv).mpr Finsupp.infinite_of_right

-- INSTANCE (free from Core): [Module.Free

variable {R M N}

theorem of_equiv' {P : Type v} [AddCommMonoid P] [Module R P] (_ : Module.Free R P)
    (e : P ≃ₗ[R] N) : Module.Free R N :=
  of_equiv e

lemma iff_of_equiv {R R' M M'} [Semiring R] [AddCommMonoid M] [Module R M]
    [Semiring R'] [AddCommMonoid M'] [Module R' M']
    {σ : R →+* R'} {σ' : R' →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e₂ : M ≃ₛₗ[σ] M') :
    Module.Free R M ↔ Module.Free R' M' :=
  ⟨fun _ ↦ of_equiv e₂, fun _ ↦ of_equiv e₂.symm⟩
