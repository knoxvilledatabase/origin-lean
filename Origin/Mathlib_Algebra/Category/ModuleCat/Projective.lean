/-
Extracted from Algebra/Category/ModuleCat/Projective.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# The category of `R`-modules has enough projectives.
-/

universe v u w

open CategoryTheory Module ModuleCat

variable {R : Type u} [Ring R] (P : ModuleCat.{v} R)

-- INSTANCE (free from Core): ModuleCat.projective_of_categoryTheory_projective

-- INSTANCE (free from Core): ModuleCat.projective_of_module_projective

theorem IsProjective.iff_projective [Small.{v} R] (P : Type v) [AddCommGroup P] [Module R P] :
    Module.Projective R P ↔ Projective (of R P) :=
  ⟨fun _ => (of R P).projective_of_categoryTheory_projective,
    fun _ => (of R P).projective_of_module_projective⟩

namespace ModuleCat

variable {M : ModuleCat.{v} R}

theorem projective_of_free {ι : Type w} (b : Basis ι R M) : Projective M :=
  have : Module.Projective R M := Module.Projective.of_basis b
  M.projective_of_categoryTheory_projective

-- INSTANCE (free from Core): enoughProjectives

end ModuleCat
