/-
Extracted from LinearAlgebra/QuadraticForm/TensorProduct/Isometries.lean
Genuine: 15 | Conflates: 0 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

noncomputable section

/-!
# Linear equivalences of tensor products as isometries

These results are separate from the definition of `QuadraticForm.tmul` as that file is very slow.

## Main definitions

* `QuadraticForm.Isometry.tmul`: `TensorProduct.map` as a `QuadraticForm.Isometry`
* `QuadraticForm.tensorComm`: `TensorProduct.comm` as a `QuadraticForm.IsometryEquiv`
* `QuadraticForm.tensorAssoc`: `TensorProduct.assoc` as a `QuadraticForm.IsometryEquiv`
* `QuadraticForm.tensorRId`: `TensorProduct.rid` as a `QuadraticForm.IsometryEquiv`
* `QuadraticForm.tensorLId`: `TensorProduct.lid` as a `QuadraticForm.IsometryEquiv`
-/

universe uR uM₁ uM₂ uM₃ uM₄

variable {R : Type uR} {M₁ : Type uM₁} {M₂ : Type uM₂} {M₃ : Type uM₃} {M₄ : Type uM₄}

open scoped TensorProduct

open QuadraticMap

namespace QuadraticForm

variable [CommRing R]

variable [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup M₄]

variable [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄] [Invertible (2 : R)]

@[simp]
theorem tmul_comp_tensorMap
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    {Q₃ : QuadraticForm R M₃} {Q₄ : QuadraticForm R M₄}
    (f : Q₁ →qᵢ Q₂) (g : Q₃ →qᵢ Q₄) :
    (Q₂.tmul Q₄).comp (TensorProduct.map f.toLinearMap g.toLinearMap) = Q₁.tmul Q₃ := by
  have h₁ : Q₁ = Q₂.comp f.toLinearMap := QuadraticMap.ext fun x => (f.map_app x).symm
  have h₃ : Q₃ = Q₄.comp g.toLinearMap := QuadraticMap.ext fun x => (g.map_app x).symm
  refine (QuadraticMap.associated_rightInverse R).injective ?_
  ext m₁ m₃ m₁' m₃'
  simp [-associated_apply, h₁, h₃, associated_tmul]

@[simp]
theorem tmul_tensorMap_apply
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    {Q₃ : QuadraticForm R M₃} {Q₄ : QuadraticForm R M₄}
    (f : Q₁ →qᵢ Q₂) (g : Q₃ →qᵢ Q₄) (x : M₁ ⊗[R] M₃) :
    Q₂.tmul Q₄ (TensorProduct.map f.toLinearMap g.toLinearMap x) = Q₁.tmul Q₃ x :=
  DFunLike.congr_fun (tmul_comp_tensorMap f g) x

namespace Isometry

def _root_.QuadraticMap.Isometry.tmul
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    {Q₃ : QuadraticForm R M₃} {Q₄ : QuadraticForm R M₄}
    (f : Q₁ →qᵢ Q₂) (g : Q₃ →qᵢ Q₄) : (Q₁.tmul Q₃) →qᵢ (Q₂.tmul Q₄) where
  toLinearMap := TensorProduct.map f.toLinearMap g.toLinearMap
  map_app' := tmul_tensorMap_apply f g

end Isometry

section tensorComm

@[simp]
theorem tmul_comp_tensorComm (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
    (Q₂.tmul Q₁).comp (TensorProduct.comm R M₁ M₂) = Q₁.tmul Q₂ := by
  refine (QuadraticMap.associated_rightInverse R).injective ?_
  ext m₁ m₂ m₁' m₂'
  dsimp [-associated_apply]
  simp only [associated_tmul, QuadraticMap.associated_comp]
  exact mul_comm _ _

@[simp]
theorem tmul_tensorComm_apply
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (x : M₁ ⊗[R] M₂) :
    Q₂.tmul Q₁ (TensorProduct.comm R M₁ M₂ x) = Q₁.tmul Q₂ x :=
  DFunLike.congr_fun (tmul_comp_tensorComm Q₁ Q₂) x

@[simps toLinearEquiv]
def tensorComm (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
    (Q₁.tmul Q₂).IsometryEquiv (Q₂.tmul Q₁) where
  toLinearEquiv := TensorProduct.comm R M₁ M₂
  map_app' := tmul_tensorComm_apply Q₁ Q₂

end tensorComm

section tensorAssoc

@[simp]
theorem tmul_comp_tensorAssoc
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃) :
    (Q₁.tmul (Q₂.tmul Q₃)).comp (TensorProduct.assoc R M₁ M₂ M₃) = (Q₁.tmul Q₂).tmul Q₃ := by
  refine (QuadraticMap.associated_rightInverse R).injective ?_
  ext m₁ m₂ m₁' m₂' m₁'' m₂''
  dsimp [-associated_apply]
  simp only [associated_tmul, QuadraticMap.associated_comp]
  exact mul_assoc _ _ _

@[simp]
theorem tmul_tensorAssoc_apply
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃)
    (x : (M₁ ⊗[R] M₂) ⊗[R] M₃) :
    Q₁.tmul (Q₂.tmul Q₃) (TensorProduct.assoc R M₁ M₂ M₃ x) = (Q₁.tmul Q₂).tmul Q₃ x :=
  DFunLike.congr_fun (tmul_comp_tensorAssoc Q₁ Q₂ Q₃) x

@[simps toLinearEquiv]
def tensorAssoc (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃) :
    ((Q₁.tmul Q₂).tmul Q₃).IsometryEquiv (Q₁.tmul (Q₂.tmul Q₃)) where
  toLinearEquiv := TensorProduct.assoc R M₁ M₂ M₃
  map_app' := tmul_tensorAssoc_apply Q₁ Q₂ Q₃

end tensorAssoc

section tensorRId

theorem comp_tensorRId_eq (Q₁ : QuadraticForm R M₁) :
    Q₁.comp (TensorProduct.rid R M₁) = Q₁.tmul (sq (R := R)) := by
  refine (QuadraticMap.associated_rightInverse R).injective ?_
  ext m₁ m₁'
  dsimp [-associated_apply]
  simp only [associated_tmul, QuadraticMap.associated_comp]
  simp [-associated_apply, one_mul]

@[simp]
theorem tmul_tensorRId_apply
    (Q₁ : QuadraticForm R M₁) (x : M₁ ⊗[R] R) :
    Q₁ (TensorProduct.rid R M₁ x) = Q₁.tmul (sq (R := R)) x :=
  DFunLike.congr_fun (comp_tensorRId_eq Q₁) x

@[simps toLinearEquiv]
def tensorRId (Q₁ : QuadraticForm R M₁) :
    (Q₁.tmul (sq (R := R))).IsometryEquiv Q₁ where
  toLinearEquiv := TensorProduct.rid R M₁
  map_app' := tmul_tensorRId_apply Q₁

end tensorRId

section tensorLId

theorem comp_tensorLId_eq (Q₂ : QuadraticForm R M₂) :
    Q₂.comp (TensorProduct.lid R M₂) = QuadraticForm.tmul (sq (R := R)) Q₂ := by
  refine (QuadraticMap.associated_rightInverse R).injective ?_
  ext m₂ m₂'
  dsimp [-associated_apply]
  simp only [associated_tmul, QuadraticMap.associated_comp]
  simp [-associated_apply, mul_one]

@[simp]
theorem tmul_tensorLId_apply
    (Q₂ : QuadraticForm R M₂) (x : R ⊗[R] M₂) :
    Q₂ (TensorProduct.lid R M₂ x) = QuadraticForm.tmul (sq (R := R)) Q₂ x :=
  DFunLike.congr_fun (comp_tensorLId_eq Q₂) x

@[simps toLinearEquiv]
def tensorLId (Q₂ : QuadraticForm R M₂) :
    (QuadraticForm.tmul (sq (R := R)) Q₂).IsometryEquiv Q₂ where
  toLinearEquiv := TensorProduct.lid R M₂
  map_app' := tmul_tensorLId_apply Q₂

end tensorLId

end QuadraticForm
