/-
Extracted from CategoryTheory/Galois/Full.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Fiber functors are (faithfully) full

Any (fiber) functor `F : C ⥤ FintypeCat` factors via the forgetful functor
from finite `Aut F`-sets to finite sets. The induced functor
`H : C ⥤ Action FintypeCat (Aut F)` is faithfully full. The faithfulness
follows easily from the faithfulness of `F`. In this file we show that `H` is also full.

## Main results

- `PreGaloisCategory.exists_lift_of_mono`: If `Y` is a sub-`Aut F`-set of `F.obj X`, there exists
  a sub-object `Z` of `X` such that `F.obj Z ≅ Y` as `Aut F`-sets.
- `PreGaloisCategory.functorToAction_full`: The induced functor `H` from above is full.

The main input for this is that the induced functor `H : C ⥤ Action FintypeCat (Aut F)`
preserves connectedness, which translates to the fact that `Aut F` acts transitively on
the fibers of connected objects.

-/

universe u

namespace CategoryTheory

namespace PreGaloisCategory

open Limits Functor

variable {C : Type*} [Category* C] (F : C ⥤ FintypeCat.{u}) [GaloisCategory C] [FiberFunctor F]

lemma exists_lift_of_mono_of_isConnected (X : C) (Y : Action FintypeCat.{u} (Aut F))
    (i : Y ⟶ (functorToAction F).obj X) [Mono i] [IsConnected Y] : ∃ (Z : C) (f : Z ⟶ X)
    (u : Y ≅ (functorToAction F).obj Z),
    IsConnected Z ∧ Mono f ∧ i = u.hom ≫ (functorToAction F).map f := by
  obtain ⟨y⟩ := nonempty_fiber_of_isConnected (forget₂ _ FintypeCat) Y
  obtain ⟨Z, f, z, hz, hc, hm⟩ := fiber_in_connected_component F X (i.hom y)
  have : IsConnected ((functorToAction F).obj Z) := PreservesIsConnected.preserves
  obtain ⟨u, hu⟩ := connected_component_unique
    (forget₂ (Action FintypeCat (Aut F)) FintypeCat) (B := (functorToAction F).obj Z)
    y z i ((functorToAction F).map f) hz.symm
  refine ⟨Z, f, u, hc, hm, ?_⟩
  apply evaluation_injective_of_isConnected
    (forget₂ (Action FintypeCat (Aut F)) FintypeCat) Y ((functorToAction F).obj X) y
  suffices h : i.hom y = F.map f z by simpa [hu]
  exact hz.symm

set_option backward.isDefEq.respectTransparency false in

lemma exists_lift_of_mono (X : C) (Y : Action FintypeCat.{u} (Aut F))
    (i : Y ⟶ (functorToAction F).obj X) [Mono i] : ∃ (Z : C) (f : Z ⟶ X)
    (u : Y ≅ (functorToAction F).obj Z), Mono f ∧ u.hom ≫ (functorToAction F).map f = i := by
  obtain ⟨ι, hf, f, t, hc⟩ := has_decomp_connected_components' Y
  let i' (j : ι) : f j ⟶ (functorToAction F).obj X := Sigma.ι f j ≫ t.hom ≫ i
  choose gZ gf gu _ _ h using fun i ↦ exists_lift_of_mono_of_isConnected F X (f i) (i' i)
  let is2 : (functorToAction F).obj (∐ gZ) ≅ ∐ fun i => (functorToAction F).obj (gZ i) :=
    PreservesCoproduct.iso (functorToAction F) gZ
  let u' : ∐ f ≅ ∐ fun i => (functorToAction F).obj (gZ i) := Sigma.mapIso gu
  have heq : (functorToAction F).map (Sigma.desc gf) = (t.symm ≪≫ u' ≪≫ is2.symm).inv ≫ i := by
    simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc]
    rw [← Iso.inv_comp_eq]
    refine Sigma.hom_ext _ _ (fun j ↦ ?_)
    suffices (functorToAction F).map (gf j) = (gu j).inv ≫ i' j by
      simpa [is2, u']
    simp only [h, Iso.inv_hom_id_assoc]
  refine ⟨∐ gZ, Sigma.desc gf, t.symm ≪≫ u' ≪≫ is2.symm, ?_, by simp [heq]⟩
  · exact mono_of_mono_map (functorToAction F) (heq ▸ mono_comp _ _)

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): functorToAction_full

end PreGaloisCategory

end CategoryTheory
