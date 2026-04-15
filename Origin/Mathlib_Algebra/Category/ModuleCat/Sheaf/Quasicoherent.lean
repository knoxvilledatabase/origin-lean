/-
Extracted from Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean
Genuine: 6 of 9 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

/-!
# Quasicoherent sheaves

A sheaf of modules is quasi-coherent if it admits locally a presentation as the
cokernel of a morphism between coproducts of copies of the sheaf of rings.
When these coproducts are finite, we say that the sheaf is of finite presentation.

## References

* https://stacks.math.columbia.edu/tag/01BD

-/

universe u v' u'

open CategoryTheory Limits

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}

variable {R : Sheaf J RingCat.{u}}

namespace SheafOfModules

variable (M : SheafOfModules.{u} R)

section

variable [HasWeakSheafify J AddCommGrp.{u}] [J.WEqualsLocallyBijective AddCommGrp.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]

structure Presentation where
  /-- generators -/
  generators : M.GeneratingSections
  /-- relations -/
  relations : (kernel generators.π).GeneratingSections

end

variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  [∀ X, HasWeakSheafify (J.over X) AddCommGrp.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrp.{u}]

structure QuasicoherentData where
  /-- the index type of the covering -/
  I : Type u'
  /-- a family of objects which cover the terminal object -/
  X : I → C
  coversTop : J.CoversTop X
  /-- a presentation of the sheaf of modules `M.over (X i)` for any `i : I` -/
  presentation (i : I) : (M.over (X i)).Presentation

namespace QuasicoherentData

variable {M}

@[simps]
def localGeneratorsData (q : M.QuasicoherentData) : M.LocalGeneratorsData where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (q.presentation i).generators

end QuasicoherentData

class IsQuasicoherent : Prop where
  nonempty_quasicoherentData : Nonempty M.QuasicoherentData

class IsFinitePresentation : Prop where
  exists_quasicoherentData :
    ∃ (σ : M.QuasicoherentData), ∀ (i : σ.I), (Finite (σ.presentation i).generators.I ∧
      Finite (σ.presentation i).relations.I)

section

variable [h : M.IsFinitePresentation]

noncomputable def quasicoherentDataOfIsFinitePresentation : M.QuasicoherentData :=
  h.exists_quasicoherentData.choose

instance (i : M.quasicoherentDataOfIsFinitePresentation.I) :
    Finite (M.quasicoherentDataOfIsFinitePresentation.presentation i).generators.I :=
  have : _ ∧ Finite (M.quasicoherentDataOfIsFinitePresentation.presentation i).relations.I :=
    h.exists_quasicoherentData.choose_spec i
  this.1

instance (i : M.quasicoherentDataOfIsFinitePresentation.I) :
    Finite (M.quasicoherentDataOfIsFinitePresentation.presentation i).relations.I :=
  have : _ ∧ Finite (M.quasicoherentDataOfIsFinitePresentation.presentation i).relations.I :=
    h.exists_quasicoherentData.choose_spec i
  this.2

end

instance [M.IsFinitePresentation] : M.IsFiniteType where
  exists_localGeneratorsData :=
    ⟨M.quasicoherentDataOfIsFinitePresentation.localGeneratorsData,
      by intro; dsimp; infer_instance⟩

end SheafOfModules
