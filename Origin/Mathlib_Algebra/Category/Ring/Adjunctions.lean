/-
Extracted from Algebra/Category/Ring/Adjunctions.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
Multivariable polynomials on a type is the left adjoint of the
forgetful functor from commutative rings to types.
-/

noncomputable section

universe u

open MvPolynomial

open CategoryTheory

namespace CommRingCat

def free : Type u ⥤ CommRingCat.{u} where
  obj α := of (MvPolynomial α ℤ)
  map {X Y} f := (↑(rename f : _ →ₐ[ℤ] _) : MvPolynomial X ℤ →+* MvPolynomial Y ℤ)
  -- TODO these next two fields can be done by `tidy`, but the calls in `dsimp` and `simp` it
  -- generates are too slow.
  map_id _ := RingHom.ext <| rename_id
  map_comp f g := RingHom.ext fun p => (rename_rename f g p).symm

@[simp]
theorem free_obj_coe {α : Type u} : (free.obj α : Type u) = MvPolynomial α ℤ :=
  rfl

@[simp, nolint simpNF]
theorem free_map_coe {α β : Type u} {f : α → β} : ⇑(free.map f) = ⇑(rename f) :=
  rfl

def adj : free ⊣ forget CommRingCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => homEquiv
      homEquiv_naturality_left_symm := fun {_ _ Y} f g =>
        RingHom.ext fun x => eval₂_cast_comp f (Int.castRingHom Y) g x }

instance : (forget CommRingCat.{u}).IsRightAdjoint :=
  ⟨_, ⟨adj⟩⟩

end CommRingCat
