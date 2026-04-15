/-
Extracted from Algebra/Category/ModuleCat/EpiMono.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Monomorphisms in `Module R`

This file shows that an `R`-linear map is a monomorphism in the category of `R`-modules
if and only if it is injective, and similarly an epimorphism if and only if it is surjective.
-/

universe v u

open CategoryTheory

namespace ModuleCat

variable {R : Type u} [Ring R] {X Y : ModuleCat.{v} R} (f : X ⟶ Y)

variable {M : Type v} [AddCommGroup M] [Module R M]

theorem ker_eq_bot_of_mono [Mono f] : LinearMap.ker f.hom = ⊥ :=
  LinearMap.ker_eq_bot_of_cancel fun u v h => ModuleCat.hom_ext_iff.mp <|
    (@cancel_mono _ _ _ _ _ f _ (↟u) (↟v)).1 <| ModuleCat.hom_ext_iff.mpr h

theorem range_eq_top_of_epi [Epi f] : LinearMap.range f.hom = ⊤ :=
  LinearMap.range_eq_top_of_cancel fun u v h => ModuleCat.hom_ext_iff.mp <|
    (@cancel_epi _ _ _ _ _ f _ (↟u) (↟v)).1 <| ModuleCat.hom_ext_iff.mpr h

theorem mono_iff_ker_eq_bot : Mono f ↔ LinearMap.ker f.hom = ⊥ :=
  ⟨fun _ => ker_eq_bot_of_mono _, fun hf =>
    ConcreteCategory.mono_of_injective _ <| by convert LinearMap.ker_eq_bot.1 hf⟩

theorem mono_iff_injective : Mono f ↔ Function.Injective f := by
  rw [mono_iff_ker_eq_bot, LinearMap.ker_eq_bot]

theorem epi_iff_range_eq_top : Epi f ↔ LinearMap.range f.hom = ⊤ :=
  ⟨fun _ => range_eq_top_of_epi _, fun hf =>
    ConcreteCategory.epi_of_surjective _ <| by convert LinearMap.range_eq_top.1 hf⟩

theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := by
  rw [epi_iff_range_eq_top, LinearMap.range_eq_top]
