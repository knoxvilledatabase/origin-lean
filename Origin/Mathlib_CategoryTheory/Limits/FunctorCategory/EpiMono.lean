/-
Extracted from CategoryTheory/Limits/FunctorCategory/EpiMono.lean
Genuine: 2 of 7 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Monomorphisms and epimorphisms in functor categories

A natural transformation `f : F ⟶ G` between functors `K ⥤ C`
is a mono (resp. epi) iff for all `k : K`, `f.app k` is,
at least when `C` has pullbacks (resp. pushouts),
see `NatTrans.mono_iff_mono_app` and `NatTrans.epi_iff_epi_app`.

-/

universe v v' v'' u u' u''

namespace CategoryTheory

open Limits Functor

variable {K : Type u} [Category.{v} K] {C : Type u'} [Category.{v'} C]
  {D : Type u''} [Category.{v''} D] {F G : K ⥤ C} (f : F ⟶ G)

variable [HasPullbacks C]

-- INSTANCE (free from Core): [Mono

lemma NatTrans.mono_iff_mono_app : Mono f ↔ ∀ (k : K), Mono (f.app k) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ mono_of_mono_app _⟩

-- INSTANCE (free from Core): [Mono

-- INSTANCE (free from Core): (F

end

variable [HasPushouts C]

-- INSTANCE (free from Core): [Epi

lemma NatTrans.epi_iff_epi_app : Epi f ↔ ∀ (k : K), Epi (f.app k) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ epi_of_epi_app _⟩

-- INSTANCE (free from Core): [Epi

end

end CategoryTheory
