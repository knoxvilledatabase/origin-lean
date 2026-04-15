/-
Extracted from Algebra/Lie/Weights/IsSimple.lean
Genuine: 6 of 8 | Dissolved: 1 | Infrastructure: 1
-/
import Origin.Core

/-!
# Lie ideals, invariant root submodules, and simple Lie algebras

Given a semisimple Lie algebra, the lattice of ideals is order isomorphic to the lattice of
Weyl-group-invariant submodules of the corresponding root system. In this file we provide
`LieIdeal.toInvtRootSubmodule`, which constructs the invariant submodule associated to an ideal,
and `LieAlgebra.IsKilling.invtSubmoduleToLieIdeal`, which constructs the ideal associated to an
invariant submodule.

## Main definitions
* `LieIdeal.rootSet`: the set of roots whose root space is contained in a given Lie ideal.
* `LieIdeal.rootSpan`: the submodule of `Dual K H` spanned by `LieIdeal.rootSet`.
* `LieIdeal.toInvtRootSubmodule`: the invariant root submodule associated to an ideal.
* `LieAlgebra.IsKilling.invtSubmoduleToLieIdeal`: constructs a Lie ideal from an invariant
  submodule of the dual space.
* `LieAlgebra.IsKilling.lieIdealOrderIso`: the order isomorphism between Lie ideals and
  invariant root submodules.

## Main results
* `LieAlgebra.IsKilling.restr_inf_cartan_eq_iSup_corootSubmodule`: the intersection of a Lie ideal
  and a Cartan subalgebra is the span of the coroots whose roots have root spaces in the ideal.
* `LieAlgebra.IsKilling.isSimple_iff_isIrreducible`: a Killing Lie algebra is simple if and only
  if its root system is irreducible.
-/

namespace LieIdeal

open LieAlgebra LieAlgebra.IsKilling LieModule Module

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

lemma corootSubmodule_le (I : LieIdeal K L) {α : Weight K H L}
    (hα : rootSpace H α ≤ I.restr H) :
    corootSubmodule α ≤ I.restr H := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (LieSubmodule.mem_map _).mp hx
  have : (⟨a.val, a.property⟩ : H) ∈ corootSpace α := ha
  rw [mem_corootSpace] at this
  refine (Submodule.span_le.mpr ?_) this
  rintro _ ⟨y, hy, _, -, rfl⟩
  exact lie_mem_left K L I y _ (hα hy)

def rootSet (I : LieIdeal K L) : Set H.root := { α | rootSpace H α.1 ≤ I.restr H }

variable [CharZero K] [IsKilling K L] [IsTriangularizable K H L]

noncomputable def rootSpan (I : LieIdeal K L) : Submodule K (Dual K H) :=
  Submodule.span K ((rootSystem H).root '' I.rootSet)

-- DISSOLVED: rootSpace_le_of_apply_coroot_ne_zero

lemma reflectionPerm_mem_rootSet_iff (I : LieIdeal K L) (α β : H.root) :
    (rootSystem H).reflectionPerm β α ∈ I.rootSet ↔ α ∈ I.rootSet := by
  let S := rootSystem H
  suffices h : ∀ γ δ : H.root, δ ∈ I.rootSet → S.reflectionPerm γ δ ∈ I.rootSet by
    exact ⟨fun hα => S.reflectionPerm_self β α ▸ h β _ hα, h β α⟩
  intro γ δ hδ
  simp only [mem_rootSet] at hδ ⊢
  by_cases hp : S.pairing δ γ = 0
  · rwa [S.reflectionPerm_eq_of_pairing_eq_zero hp]
  · have hγ := I.rootSpace_le_of_apply_coroot_ne_zero hδ
      (mt S.pairing_eq_zero_iff.mpr hp)
    have h_neg : S.pairing (S.reflectionPerm γ δ) γ ≠ 0 := by
      rwa [← S.pairing_reflectionPerm γ δ γ, S.pairing_reflectionPerm_self_right, neg_ne_zero]
    exact I.rootSpace_le_of_apply_coroot_ne_zero hγ h_neg

lemma rootSpan_mem_invtRootSubmodule (I : LieIdeal K L) :
    I.rootSpan ∈ (rootSystem H).invtRootSubmodule := by
  rw [RootPairing.mem_invtRootSubmodule_iff]
  intro β
  rw [Module.End.mem_invtSubmodule, rootSpan, Submodule.span_le]
  rintro - ⟨α, hα, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe, ← RootPairing.root_reflectionPerm]
  exact Submodule.subset_span ⟨_, (I.reflectionPerm_mem_rootSet_iff α β).mpr hα, rfl⟩

noncomputable def toInvtRootSubmodule (I : LieIdeal K L) :
    (rootSystem H).invtRootSubmodule :=
  ⟨I.rootSpan, I.rootSpan_mem_invtRootSubmodule⟩
