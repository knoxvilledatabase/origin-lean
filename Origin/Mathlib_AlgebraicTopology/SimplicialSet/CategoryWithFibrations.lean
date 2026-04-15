/-
Extracted from AlgebraicTopology/SimplicialSet/CategoryWithFibrations.lean
Genuine: 8 of 15 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core

/-!
# Cofibrations and fibrations in the category of simplicial sets

We endow `SSet` with `CategoryWithCofibrations` and `CategoryWithFibrations`
instances. Cofibrations are monomorphisms, and fibrations are morphisms
having the right lifting property with respect to horn inclusions.

We have an instance `mono_of_cofibration` (but only a lemma `cofibration_of_mono`).
Then, when stating lemmas about cofibrations of simplicial sets, it is advisable
to use the assumption `[Mono f]` instead of `[Cofibration f]`.

-/

open CategoryTheory HomotopicalAlgebra MorphismProperty Simplicial

universe u

namespace SSet

namespace modelCategoryQuillen

def I : MorphismProperty SSet.{u} :=
  .ofHoms (fun n ↦ ∂Δ[n].ι)

lemma boundary_ι_mem_I (n : ℕ) :
    I (boundary.{u} n).ι := by constructor

def J : MorphismProperty SSet.{u} :=
  ⨆ n, .ofHoms (fun (i : Fin (n + 2)) ↦ Λ[n + 1, i].ι)

lemma horn_ι_mem_J (n : ℕ) (i : Fin (n + 2)) :
    J (horn.{u} (n + 1) i).ι := by
  simp only [J, iSup_iff]
  exact ⟨n, ⟨i⟩⟩

lemma I_le_monomorphisms : I.{u} ≤ monomorphisms _ := by
  rintro _ _ _ ⟨n⟩
  exact monomorphisms.infer_property _

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable {X Y : SSet.{u}} (f : X ⟶ Y)

lemma cofibration_iff : Cofibration f ↔ Mono f := by
  rw [HomotopicalAlgebra.cofibration_iff]
  rfl

lemma fibration_iff : Fibration f ↔ J.rlp f := by
  rw [HomotopicalAlgebra.fibration_iff]
  rfl

-- INSTANCE (free from Core): mono_of_cofibration

lemma cofibration_of_mono [Mono f] : Cofibration f := by rwa [cofibration_iff]

-- INSTANCE (free from Core): [hf

end

end modelCategoryQuillen

end SSet
