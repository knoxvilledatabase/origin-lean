/-
Extracted from Algebra/Category/ModuleCat/Monoidal/Basic.lean
Genuine: 9 of 9 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The monoidal category structure on R-modules

Mostly this uses existing machinery in `LinearAlgebra.TensorProduct`.
We just need to provide a few small missing pieces to build the
`MonoidalCategory` instance.
The `SymmetricCategory` instance is in `Algebra.Category.ModuleCat.Monoidal.Symmetric`
to reduce imports.

Note the universe level of the modules must be at least the universe level of the ring,
so that we have a monoidal unit.
For now, we simplify by insisting both universe levels are the same.

We construct the monoidal closed structure on `ModuleCat R` in
`Algebra.Category.ModuleCat.Monoidal.Closed`.

If you're happy using the bundled `ModuleCat R`, it may be possible to mostly
use this as an interface and not need to interact much with the implementation details.
-/

universe v w x u

open CategoryTheory

namespace SemimoduleCat

variable {R : Type u} [CommSemiring R]

namespace MonoidalCategory

open TensorProduct

attribute [local ext] TensorProduct.ext

def tensorObj (M N : SemimoduleCat R) : SemimoduleCat R :=
  SemimoduleCat.of R (M ⊗[R] N)

def tensorHom {M N M' N' : SemimoduleCat R} (f : M ⟶ N) (g : M' ⟶ N') :
    tensorObj M M' ⟶ tensorObj N N' :=
  ofHom <| TensorProduct.map f.hom g.hom

def whiskerLeft (M : SemimoduleCat R) {N₁ N₂ : SemimoduleCat R} (f : N₁ ⟶ N₂) :
    tensorObj M N₁ ⟶ tensorObj M N₂ :=
  ofHom <| f.hom.lTensor M

def whiskerRight {M₁ M₂ : SemimoduleCat R} (f : M₁ ⟶ M₂) (N : SemimoduleCat R) :
    tensorObj M₁ N ⟶ tensorObj M₂ N :=
  ofHom <| f.hom.rTensor N

theorem id_tensorHom_id (M N : SemimoduleCat R) :
    tensorHom (𝟙 M) (𝟙 N) = 𝟙 (SemimoduleCat.of R (M ⊗ N)) := by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): even with high priority `ext` fails to find this.
  apply TensorProduct.ext
  rfl

theorem tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : SemimoduleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ = tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): even with high priority `ext` fails to find this.
  apply TensorProduct.ext
  rfl

def associator (M : SemimoduleCat.{v} R) (N : SemimoduleCat.{w} R) (K : SemimoduleCat.{x} R) :
    tensorObj (tensorObj M N) K ≅ tensorObj M (tensorObj N K) :=
  (TensorProduct.assoc R M N K).toModuleIsoₛ

def leftUnitor (M : SemimoduleCat.{u} R) : SemimoduleCat.of R (R ⊗[R] M) ≅ M :=
  (TensorProduct.lid R M).toModuleIsoₛ

def rightUnitor (M : SemimoduleCat.{u} R) : SemimoduleCat.of R (M ⊗[R] R) ≅ M :=
  (TensorProduct.rid R M).toModuleIsoₛ
