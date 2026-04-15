/-
Extracted from Logic/Function/FiberPartition.lean
Genuine: 13 of 13 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Data.Set.Basic

/-!

This file defines the type `f.Fiber` of fibers of a function `f : Y → Z`, and provides some API
to work with and construct terms of this type.

Note: this API is designed to be useful when defining the counit of the adjunction between
the functor which takes a set to the condensed set corresponding to locally constant maps to that
set, and the forgetful functor from the category of condensed sets to the category of sets
(see PR https://github.com/leanprover-community/mathlib4/pull/14027).
-/

variable {X Y Z : Type*}

namespace Function

def Fiber (f : Y → Z) : Type _ := Set.range (fun (x : Set.range f) ↦ f ⁻¹' {x.val})

namespace Fiber

noncomputable def image (f : Y → Z) (a : Fiber f) : Z := a.2.choose.1

lemma eq_fiber_image  (f : Y → Z) (a : Fiber f) : a.1 = f ⁻¹' {a.image} := a.2.choose_spec.symm

def mk (f : Y → Z) (y : Y) : Fiber f := ⟨f ⁻¹' {f y}, by simp⟩

def mkSelf (f : Y → Z) (y : Y) : (mk f y).val := ⟨y, rfl⟩

lemma map_eq_image (f : Y → Z) (a : Fiber f) (x : a.1) : f x = a.image := by
  have := a.2.choose_spec
  rw [← Set.mem_singleton_iff, ← Set.mem_preimage]
  convert x.prop

lemma mk_image (f : Y → Z) (y : Y) : (Fiber.mk f y).image = f y :=
  (map_eq_image (x := mkSelf f y)).symm

lemma mem_iff_eq_image (f : Y → Z) (y : Y) (a : Fiber f) : y ∈ a.val ↔ f y = a.image :=
  ⟨fun h ↦ a.map_eq_image _ ⟨y, h⟩, fun h ↦ by rw [a.eq_fiber_image]; exact h⟩

noncomputable def preimage (f : Y → Z) (a : Fiber f) : Y := a.2.choose.2.choose

lemma map_preimage_eq_image (f : Y → Z) (a : Fiber f) : f a.preimage = a.image :=
  a.2.choose.2.choose_spec

lemma fiber_nonempty (f : Y → Z) (a : Fiber f) : Set.Nonempty a.val := by
  refine ⟨preimage f a, ?_⟩
  rw [mem_iff_eq_image, ← map_preimage_eq_image]

lemma map_preimage_eq_image_map {W : Type*} (f : Y → Z) (g : Z → W) (a : Fiber (g ∘ f)) :
    g (f a.preimage) = a.image := by rw [← map_preimage_eq_image, comp_apply]

lemma image_eq_image_mk (f : Y → Z) (g : X → Y) (a : Fiber (f ∘ g)) :
    a.image = (Fiber.mk f (g (a.preimage _))).image := by
  rw [← map_preimage_eq_image_map _ _ a, mk_image]

end Function.Fiber
