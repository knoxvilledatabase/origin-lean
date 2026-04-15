/-
Extracted from Topology/Category/Profinite/Product.lean
Genuine: 10 of 12 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Compact subsets of products as limits in `Profinite`

This file exhibits a compact subset `C` of a product `(i : ι) → X i` of totally disconnected
Hausdorff spaces as a cofiltered limit in `Profinite` indexed by `Finset ι`.

## Main definitions

- `Profinite.indexFunctor` is the functor `(Finset ι)ᵒᵖ ⥤ Profinite` indexing the limit. It maps
  `J` to the restriction of `C` to `J`
- `Profinite.indexCone` is a cone on `Profinite.indexFunctor` with cone point `C`

## Main results

- `Profinite.isIso_indexCone_lift` says that the natural map from the cone point of the explicit
  limit cone in `Profinite` on `indexFunctor` to the cone point of `indexCone` is an
  isomorphism
- `Profinite.asLimitindexConeIso` is the induced isomorphism of cones.
- `Profinite.indexCone_isLimit` says that `indexCone` is a limit cone.

-/

universe u

namespace Profinite

variable {ι : Type u} {X : ι → Type} [∀ i, TopologicalSpace (X i)] (C : Set ((i : ι) → X i))
    (J K : ι → Prop)

namespace IndexFunctor

open ContinuousMap

def obj : Set ((i : {i : ι // J i}) → X i) := ContinuousMap.precomp (Subtype.val (p := J)) '' C

def π_app : C(C, obj C J) :=
  ⟨Set.MapsTo.restrict (precomp (Subtype.val (p := J))) _ _ (Set.mapsTo_image _ _),
    Continuous.restrict _ (Pi.continuous_precomp' _)⟩

variable {J K}

def map (h : ∀ i, J i → K i) : C(obj C K, obj C J) :=
  ⟨Set.MapsTo.restrict (precomp (Set.inclusion h)) _ _ (fun _ hx ↦ by
    obtain ⟨y, hy⟩ := hx
    rw [← hy.2]
    exact ⟨y, hy.1, rfl⟩), Continuous.restrict _ (Pi.continuous_precomp' _)⟩

theorem surjective_π_app :
    Function.Surjective (π_app C J) := by
  intro x
  obtain ⟨y, hy⟩ := x.prop
  exact ⟨⟨y, hy.1⟩, Subtype.ext hy.2⟩

variable {C}

theorem eq_of_forall_π_app_eq (a b : C)
    (h : ∀ (J : Finset ι), π_app C (· ∈ J) a = π_app C (· ∈ J) b) : a = b := by
  ext i
  specialize h ({i} : Finset ι)
  rw [Subtype.ext_iff] at h
  simp only [π_app, ContinuousMap.precomp, ContinuousMap.coe_mk,
    Set.MapsTo.val_restrict_apply] at h
  exact congr_fun h ⟨i, Finset.mem_singleton.mpr rfl⟩

end IndexFunctor

variable [∀ i, T2Space (X i)] [∀ i, TotallyDisconnectedSpace (X i)]

variable {C}

open CategoryTheory Limits Opposite IndexFunctor

noncomputable

def indexFunctor (hC : IsCompact C) : (Finset ι)ᵒᵖ ⥤ Profinite.{u} where
  obj J := @Profinite.of (obj C (· ∈ (unop J))) _
    (by rw [← isCompact_iff_compactSpace]; exact hC.image (Pi.continuous_precomp' _)) _ _
  map h := ConcreteCategory.ofHom (map C (leOfHom h.unop))

noncomputable

def indexCone (hC : IsCompact C) : Cone (indexFunctor hC) where
  pt := @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _
  π := { app := fun J ↦ ConcreteCategory.ofHom (π_app C (· ∈ unop J)) }

variable (hC : IsCompact C)

-- INSTANCE (free from Core): isIso_indexCone_lift

set_option backward.isDefEq.respectTransparency false in

noncomputable

def isoindexConeLift :
    @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _ ≅
    (Profinite.limitCone.{u, u} (indexFunctor hC)).pt :=
  asIso <| (Profinite.limitConeIsLimit.{u, u} _).lift (indexCone hC)

noncomputable

def asLimitindexConeIso : indexCone hC ≅ Profinite.limitCone.{u, u} _ :=
  Limits.Cone.ext (isoindexConeLift hC) fun _ => rfl

noncomputable

def indexCone_isLimit : CategoryTheory.Limits.IsLimit (indexCone hC) :=
  Limits.IsLimit.ofIsoLimit (Profinite.limitConeIsLimit _) (asLimitindexConeIso hC).symm

end Profinite
