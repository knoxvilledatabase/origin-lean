/-
Extracted from LinearAlgebra/TensorProduct/Tower.lean
Genuine: 43 | Conflates: 0 | Dissolved: 0 | Infrastructure: 25
-/
import Origin.Core
import Mathlib.Algebra.Algebra.Tower
import Mathlib.LinearAlgebra.TensorProduct.Basic

noncomputable section

/-!
# The `A`-module structure on `M ⊗[R] N`

When `M` is both an `R`-module and an `A`-module, and `Algebra R A`, then many of the morphisms
preserve the actions by `A`.

The `Module` instance itself is provided elsewhere as `TensorProduct.leftModule`. This file provides
more general versions of the definitions already in `LinearAlgebra/TensorProduct`.

In this file, we use the convention that `M`, `N`, `P`, `Q` are all `R`-modules, but only `M` and
`P` are simultaneously `A`-modules.

## Main definitions

 * `TensorProduct.AlgebraTensorModule.curry`
 * `TensorProduct.AlgebraTensorModule.uncurry`
 * `TensorProduct.AlgebraTensorModule.lcurry`
 * `TensorProduct.AlgebraTensorModule.lift`
 * `TensorProduct.AlgebraTensorModule.lift.equiv`
 * `TensorProduct.AlgebraTensorModule.mk`
 * `TensorProduct.AlgebraTensorModule.map`
 * `TensorProduct.AlgebraTensorModule.mapBilinear`
 * `TensorProduct.AlgebraTensorModule.congr`
 * `TensorProduct.AlgebraTensorModule.rid`
 * `TensorProduct.AlgebraTensorModule.homTensorHomMap`
 * `TensorProduct.AlgebraTensorModule.assoc`
 * `TensorProduct.AlgebraTensorModule.leftComm`
 * `TensorProduct.AlgebraTensorModule.rightComm`
 * `TensorProduct.AlgebraTensorModule.tensorTensorTensorComm`

## Implementation notes

We could thus consider replacing the less general definitions with these ones. If we do this, we
probably should still implement the less general ones as abbreviations to the more general ones with
fewer type arguments.
-/

namespace TensorProduct

namespace AlgebraTensorModule

universe uR uA uB uM uN uP uQ uP' uQ'

variable {R : Type uR} {A : Type uA} {B : Type uB}

variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ} {P' : Type uP'} {Q' : Type uQ'}

open LinearMap

open Algebra (lsmul)

section Semiring

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

variable [AddCommMonoid M] [Module R M] [Module A M]

variable [IsScalarTower R A M]

variable [AddCommMonoid N] [Module R N]

variable [AddCommMonoid P] [Module R P] [Module A P]

variable [IsScalarTower R A P]

variable [AddCommMonoid Q] [Module R Q]

variable [AddCommMonoid P'] [Module R P'] [Module A P'] [Module B P']

variable [IsScalarTower R A P'] [IsScalarTower R B P'] [SMulCommClass A B P']

variable [AddCommMonoid Q'] [Module R Q']

@[simps]
nonrec def curry (f : M ⊗[R] N →ₗ[A] P) : M →ₗ[A] N →ₗ[R] P :=
  { curry (f.restrictScalars R) with
    toFun := curry (f.restrictScalars R)
    map_smul' := fun c x => LinearMap.ext fun y => f.map_smul c (x ⊗ₜ y) }

@[ext high]
nonrec theorem curry_injective : Function.Injective (curry : (M ⊗ N →ₗ[A] P) → M →ₗ[A] N →ₗ[R] P) :=
  fun _ _ h =>
  LinearMap.restrictScalars_injective R <|
    curry_injective <| (congr_arg (LinearMap.restrictScalars R) h : _)

theorem ext {g h : M ⊗[R] N →ₗ[A] P} (H : ∀ x y, g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h :=
  curry_injective <| LinearMap.ext₂ H

nonrec def lift (f : M →ₗ[A] N →ₗ[R] P) : M ⊗[R] N →ₗ[A] P :=
  { lift (f.restrictScalars R) with
    map_smul' := fun c =>
      show
        ∀ x : M ⊗[R] N,
          (lift (f.restrictScalars R)).comp (lsmul R R _ c) x =
            (lsmul R R _ c).comp (lift (f.restrictScalars R)) x
        from
        LinearMap.ext_iff.1 <|
          TensorProduct.ext' fun x y => by
            simp only [comp_apply, Algebra.lsmul_coe, smul_tmul', lift.tmul,
              coe_restrictScalars, f.map_smul, smul_apply] }

@[simp]
theorem lift_tmul (f : M →ₗ[A] N →ₗ[R] P) (x : M) (y : N) : lift f (x ⊗ₜ y) = f x y :=
  rfl

variable (R A B M N P Q)

section

variable [Module B P] [IsScalarTower R B P] [SMulCommClass A B P]

@[simps]
def uncurry : (M →ₗ[A] N →ₗ[R] P) →ₗ[B] M ⊗[R] N →ₗ[A] P where
  toFun := lift
  map_add' _ _ := ext fun x y => by simp only [lift_tmul, add_apply]
  map_smul' _ _ := ext fun x y => by simp only [lift_tmul, smul_apply, RingHom.id_apply]

@[simps]
def lcurry : (M ⊗[R] N →ₗ[A] P) →ₗ[B] M →ₗ[A] N →ₗ[R] P where
  toFun := curry
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lift.equiv : (M →ₗ[A] N →ₗ[R] P) ≃ₗ[B] M ⊗[R] N →ₗ[A] P :=
  LinearEquiv.ofLinear (uncurry R A B M N P) (lcurry R A B M N P)
    (LinearMap.ext fun _ => ext fun x y => lift_tmul _ x y)
    (LinearMap.ext fun f => LinearMap.ext fun x => LinearMap.ext fun y => lift_tmul f x y)

@[simps! apply]
nonrec def mk : M →ₗ[A] N →ₗ[R] M ⊗[R] N :=
  { mk R M N with map_smul' := fun _ _ => rfl }

variable {R A B M N P Q}

def map (f : M →ₗ[A] P) (g : N →ₗ[R] Q) : M ⊗[R] N →ₗ[A] P ⊗[R] Q :=
  lift <|
    { toFun := fun h => h ∘ₗ g,
      map_add' := fun h₁ h₂ => LinearMap.add_comp g h₂ h₁,
      map_smul' := fun c h => LinearMap.smul_comp c h g } ∘ₗ mk R A P Q ∘ₗ f

@[simp] theorem map_tmul (f : M →ₗ[A] P) (g : N →ₗ[R] Q) (m : M) (n : N) :
    map f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
  rfl

@[simp]
theorem map_id : map (id : M →ₗ[A] M) (id : N →ₗ[R] N) = .id :=
  ext fun _ _ => rfl

theorem map_comp (f₂ : P →ₗ[A] P') (f₁ : M →ₗ[A] P) (g₂ : Q →ₗ[R] Q') (g₁ : N →ₗ[R] Q) :
    map (f₂.comp f₁) (g₂.comp g₁) = (map f₂ g₂).comp (map f₁ g₁) :=
  ext fun _ _ => rfl

@[simp]
protected theorem map_one : map (1 : M →ₗ[A] M) (1 : N →ₗ[R] N) = 1 := map_id

protected theorem map_mul (f₁ f₂ : M →ₗ[A] M) (g₁ g₂ : N →ₗ[R] N) :
    map (f₁ * f₂) (g₁ * g₂) = map f₁ g₁ * map f₂ g₂ := map_comp _ _ _ _

theorem map_add_left (f₁ f₂ : M →ₗ[A] P) (g : N →ₗ[R] Q) :
    map (f₁ + f₂) g = map f₁ g + map f₂ g := by
  ext
  simp_rw [curry_apply, TensorProduct.curry_apply, restrictScalars_apply, add_apply, map_tmul,
    add_apply, add_tmul]

theorem map_add_right (f : M →ₗ[A] P) (g₁ g₂ : N →ₗ[R] Q) :
    map f (g₁ + g₂) = map f g₁ + map f g₂ := by
  ext
  simp_rw [curry_apply, TensorProduct.curry_apply, restrictScalars_apply, add_apply, map_tmul,
    add_apply, tmul_add]

theorem map_smul_right (r : R) (f : M →ₗ[A] P) (g : N →ₗ[R] Q) : map f (r • g) = r • map f g := by
  ext
  simp_rw [curry_apply, TensorProduct.curry_apply, restrictScalars_apply, smul_apply, map_tmul,
    smul_apply, tmul_smul]

theorem map_smul_left (b : B) (f : M →ₗ[A] P) (g : N →ₗ[R] Q) : map (b • f) g = b • map f g := by
  ext
  simp_rw [curry_apply, TensorProduct.curry_apply, restrictScalars_apply, smul_apply, map_tmul,
    smul_apply, smul_tmul']

variable (A M) in

def lTensor : (N →ₗ[R] Q) →ₗ[R] M ⊗[R] N →ₗ[A] M ⊗[R] Q where
  toFun f := map LinearMap.id f
  map_add' f₁ f₂ := map_add_right _ f₁ f₂
  map_smul' _ _ := map_smul_right _ _ _

@[simp] lemma lTensor_id : lTensor A M (id : N →ₗ[R] N) = .id :=
  ext fun _ _ => rfl

lemma lTensor_comp (f₂ : Q →ₗ[R] Q') (f₁ : N →ₗ[R] Q) :
    lTensor A M (f₂.comp f₁) = (lTensor A M f₂).comp (lTensor A M f₁) :=
  ext fun _ _ => rfl

@[simp]
lemma lTensor_one : lTensor A M (1 : N →ₗ[R] N) = 1 := map_id

lemma lTensor_mul (f₁ f₂ : N →ₗ[R] N) :
    lTensor A M (f₁ * f₂) = lTensor A M f₁ * lTensor A M f₂ := lTensor_comp _ _

variable (R A B M N P Q)

def mapBilinear : (M →ₗ[A] P) →ₗ[B] (N →ₗ[R] Q) →ₗ[R] (M ⊗[R] N →ₗ[A] P ⊗[R] Q) :=
  LinearMap.mk₂' _ _ map map_add_left map_smul_left map_add_right map_smul_right

variable {R A B M N P Q}

variable (R A B M N P Q)

def homTensorHomMap : ((M →ₗ[A] P) ⊗[R] (N →ₗ[R] Q)) →ₗ[B] (M ⊗[R] N →ₗ[A] P ⊗[R] Q) :=
  lift <| mapBilinear R A B M N P Q

variable {R A B M N P Q}

def congr (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) : (M ⊗[R] N) ≃ₗ[A] (P ⊗[R] Q) :=
  LinearEquiv.ofLinear (map f g) (map f.symm g.symm)
    (ext fun _m _n => congr_arg₂ (· ⊗ₜ ·) (f.apply_symm_apply _) (g.apply_symm_apply _))
    (ext fun _m _n => congr_arg₂ (· ⊗ₜ ·) (f.symm_apply_apply _) (g.symm_apply_apply _))

@[simp]
theorem congr_refl : congr (.refl A M) (.refl R N) = .refl A _ :=
  LinearEquiv.toLinearMap_injective <| map_id

theorem congr_trans (f₁ : M ≃ₗ[A] P) (f₂ : P ≃ₗ[A] P') (g₁ : N ≃ₗ[R] Q) (g₂ : Q ≃ₗ[R] Q') :
    congr (f₁.trans f₂) (g₁.trans g₂) = (congr f₁ g₁).trans (congr f₂ g₂) :=
  LinearEquiv.toLinearMap_injective <| map_comp _ _ _ _

@[simp]
theorem congr_one : congr (1 : M ≃ₗ[A] M) (1 : N ≃ₗ[R] N) = 1 := congr_refl

theorem congr_mul (f₁ f₂ : M ≃ₗ[A] M) (g₁ g₂ : N ≃ₗ[R] N) :
    congr (f₁ * f₂) (g₁ * g₂) = congr f₁ g₁ * congr f₂ g₂ := congr_trans _ _ _ _

variable (R A M)

protected def rid : M ⊗[R] R ≃ₗ[A] M :=
  LinearEquiv.ofLinear
    (lift <| Algebra.lsmul _ _ _ |>.toLinearMap |>.flip)
    (mk R A M R |>.flip 1)
    (LinearMap.ext <| one_smul _)
    (ext fun _ _ => smul_tmul _ _ _ |>.trans <| congr_arg _ <| mul_one _)

theorem rid_eq_rid : AlgebraTensorModule.rid R R M = TensorProduct.rid R M :=
  LinearEquiv.toLinearMap_injective <| TensorProduct.ext' fun _ _ => rfl

variable {R M} in

variable {M} in

end

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [Semiring B] [Algebra R A] [Algebra R B]

variable [AddCommMonoid M] [Module R M] [Module A M] [Module B M]

variable [IsScalarTower R A M] [IsScalarTower R B M] [SMulCommClass A B M]

variable [AddCommMonoid N] [Module R N]

variable [AddCommMonoid P] [Module A P]

variable [AddCommMonoid P'] [Module A P']

variable [AddCommMonoid Q] [Module R Q]

variable (R A B M N P P' Q)

attribute [local ext high] TensorProduct.ext

section assoc

variable [Module R P] [IsScalarTower R A P]

variable [Algebra A B] [IsScalarTower A B M]

def assoc : (M ⊗[A] P) ⊗[R] Q ≃ₗ[B] M ⊗[A] (P ⊗[R] Q) :=
  LinearEquiv.ofLinear
    (lift <| lift <| lcurry R A B P Q _ ∘ₗ mk A B M (P ⊗[R] Q))
    (lift <| uncurry R A B P Q _ ∘ₗ curry (mk R B _ Q))
    (by ext; rfl)
    (by ext; rfl)

variable {M P N Q}

theorem rTensor_tensor [Module R P'] [IsScalarTower R A P'] (g : P →ₗ[A] P') :
    rTensor (M ⊗[R] N) g =
      assoc R A A P' M N ∘ₗ map (rTensor M g) id ∘ₗ (assoc R A A P M N).symm.toLinearMap :=
  TensorProduct.ext <| LinearMap.ext fun _ ↦ ext fun _ _ ↦ rfl

end assoc

section cancelBaseChange

variable [Algebra A B] [IsScalarTower A B M]

def cancelBaseChange : M ⊗[A] (A ⊗[R] N) ≃ₗ[B] M ⊗[R] N :=
  letI g : (M ⊗[A] A) ⊗[R] N ≃ₗ[B] M ⊗[R] N := congr (AlgebraTensorModule.rid A B M) (.refl R N)
  (assoc R A B M A N).symm ≪≫ₗ g

def distribBaseChange : A ⊗[R] (M ⊗[R] N) ≃ₗ[A] (A ⊗[R] M) ⊗[A] (A ⊗[R] N) :=
  (cancelBaseChange _ _ _ _ _ ≪≫ₗ assoc _ _ _ _ _ _).symm

variable {M P N Q}

end cancelBaseChange

section leftComm

variable [Module R P] [IsScalarTower R A P]

def leftComm : M ⊗[A] (P ⊗[R] Q) ≃ₗ[A] P ⊗[A] (M ⊗[R] Q) :=
  let e₁ := (assoc R A A M P Q).symm
  let e₂ := congr (TensorProduct.comm A M P) (1 : Q ≃ₗ[R] Q)
  let e₃ := assoc R A A P M Q
  e₁ ≪≫ₗ e₂ ≪≫ₗ e₃

variable {M N P Q}

end leftComm

section rightComm

def rightComm : (M ⊗[A] P) ⊗[R] Q ≃ₗ[A] (M ⊗[R] Q) ⊗[A] P :=
  LinearEquiv.ofLinear
    (lift <| TensorProduct.lift <| LinearMap.flip <|
      lcurry R A A M Q ((M ⊗[R] Q) ⊗[A] P) ∘ₗ (mk A A (M ⊗[R] Q) P).flip)
    (TensorProduct.lift <| lift <| LinearMap.flip <|
      (TensorProduct.lcurry A M P ((M ⊗[A] P) ⊗[R] Q)).restrictScalars R
        ∘ₗ (mk R A (M ⊗[A] P) Q).flip)
    -- explicit `Eq.refl`s here help with performance, but also make it clear that the `ext` are
    -- letting us prove the result as an equality of pure tensors.
    (TensorProduct.ext <| ext fun m q => LinearMap.ext fun p => Eq.refl <|
      (m ⊗ₜ[R] q) ⊗ₜ[A] p)
    (curry_injective <| TensorProduct.ext' fun m p => LinearMap.ext fun q => Eq.refl <|
      (m ⊗ₜ[A] p) ⊗ₜ[R] q)

variable {M N P Q}

end rightComm

section tensorTensorTensorComm

variable [Module R P] [IsScalarTower R A P]

def tensorTensorTensorComm :
    (M ⊗[R] N) ⊗[A] (P ⊗[R] Q) ≃ₗ[A] (M ⊗[A] P) ⊗[R] (N ⊗[R] Q) :=

(assoc R A A (M ⊗[R] N) P Q).symm

  ≪≫ₗ congr (rightComm R A M P N).symm (1 : Q ≃ₗ[R] Q)

  ≪≫ₗ assoc R _ _ (M ⊗[A] P) N Q

variable {M N P Q}

end tensorTensorTensorComm

end CommSemiring

end AlgebraTensorModule

end TensorProduct

namespace Submodule

open TensorProduct

variable {R M : Type*} (A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] (p : Submodule R M)

def baseChange : Submodule A (A ⊗[R] M) :=
  span A <| p.map (TensorProduct.mk R A M 1)

@[simp]
lemma baseChange_bot : (⊥ : Submodule R M).baseChange A = ⊥ := by simp [baseChange]

@[simp]
lemma baseChange_top : (⊤ : Submodule R M).baseChange A = ⊤ := by
  rw [baseChange, map_top, eq_top_iff']
  intro x
  refine x.induction_on (by simp) (fun a y ↦ ?_) (fun _ _ ↦ Submodule.add_mem _)
  rw [← mul_one a, ← smul_eq_mul, ← smul_tmul']
  refine smul_mem _ _ (subset_span ?_)
  simp

variable {A p} in

lemma tmul_mem_baseChange_of_mem (a : A) {m : M} (hm : m ∈ p) :
    a ⊗ₜ[R] m ∈ p.baseChange A := by
  rw [← mul_one a, ← smul_eq_mul, ← smul_tmul']
  exact smul_mem (baseChange A p) a (subset_span ⟨m, hm, rfl⟩)

@[simp]
lemma baseChange_span (s : Set M) :
    (span R s).baseChange A = span A (TensorProduct.mk R A M 1 '' s) := by
  simp only [baseChange, map_coe]
  refine le_antisymm (span_le.mpr ?_) (span_mono <| Set.image_subset _ subset_span)
  rintro - ⟨m : M, hm : m ∈ span R s, rfl⟩
  apply span_induction (p := fun m' _ ↦ (1 : A) ⊗ₜ[R] m' ∈ span A (TensorProduct.mk R A M 1 '' s))
    (hx := hm)
  · intro m hm
    exact subset_span ⟨m, hm, rfl⟩
  · simp
  · intro m₁ m₂ _ _ hm₁ hm₂
    rw [tmul_add]
    exact Submodule.add_mem _ hm₁ hm₂
  · intro r m' _ hm'
    rw [tmul_smul, ← one_smul A ((1 : A) ⊗ₜ[R] m'), ← smul_assoc]
    exact smul_mem _ (r • 1) hm'

end Submodule
