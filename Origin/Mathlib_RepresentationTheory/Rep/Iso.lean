/-
Extracted from RepresentationTheory/Rep/Iso.lean
Genuine: 13 of 26 | Dissolved: 0 | Infrastructure: 13
-/
import Origin.Core

/-!
# Equivalence between `Rep k G` and `ModuleCat k[G]`

In this file we show that the category of `k`-linear representations of a monoid `G` is
equivalent to the category of modules over the monoid algebra `k[G]`.
-/

universe w w' u u' v v'

namespace Rep

open CategoryTheory

suppress_compilation

section Group

variable (k G H : Type u) [Group G] [Monoid H] [MulAction G H] [CommRing k] (n : ℕ)

open MonoidalCategory Finsupp Representation.IntertwiningMap

abbrev diagonalSuccIsoTensorTrivial :
    diagonal k G (n + 1) ≅ leftRegular k G ⊗ trivial k G ((Fin n → G) →₀ k) :=
  linearizationOfMulActionIso k G (Fin (n + 1) → G) ≪≫ (linearization k G).mapIso
    (Action.diagonalSuccIsoTensorTrivial G n) ≪≫
    (Functor.Monoidal.μIso (linearization k G) _ _).symm ≪≫
    tensorIso (linearizationOfMulActionIso k G G) (linearizationTrivialIso k G (Fin n → G))

abbrev diagonalSuccIsoFree : diagonal k G (n + 1) ≅ free k G (Fin n → G) :=
  diagonalSuccIsoTensorTrivial k G n ≪≫ leftRegularTensorTrivialIsoFree k G (Fin n → G)

variable (A : Rep k G)

abbrev diagonalHomEquiv :
    (Rep.diagonal k G (n + 1) ⟶ A) ≃ₗ[k] (Fin n → G) → A :=
  Linear.homCongr k (diagonalSuccIsoFree k G n) (Iso.refl _) ≪≫ₗ
    freeLiftLEquiv k G (Fin n → G) A

end Group

/-!
### The categorical equivalence `Rep k G ≌ Module.{u} k[G]`.
-/

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

open MonoidAlgebra

theorem to_Module_monoidAlgebra_map_aux {k G : Type*} [CommRing k] [Monoid G] (V W : Type*)
    [AddCommGroup V] [AddCommGroup W] [Module k V] [Module k W] (ρ : G →* V →ₗ[k] V)
    (σ : G →* W →ₗ[k] W) (f : V →ₗ[k] W) (w : ∀ g : G, f.comp (ρ g) = (σ g).comp f)
    (r : k[G]) (x : V) :
    f (MonoidAlgebra.lift k (V →ₗ[k] V) G ρ r x) =
      MonoidAlgebra.lift k (W →ₗ[k] W) G σ r (f x) := by
  apply MonoidAlgebra.induction_on r
  · intro g
    simp only [one_smul, MonoidAlgebra.lift_single, MonoidAlgebra.of_apply]
    exact LinearMap.congr_fun (w g) x
  · intro g h gw hw; simp only [map_add, LinearMap.add_apply, hw, gw]
  · intro r g w
    simp only [map_smul, w, LinearMap.smul_apply]

set_option backward.isDefEq.respectTransparency false in

def toModuleMonoidAlgebraMap {V W : Rep.{w} k G} (f : V ⟶ W) :
    ModuleCat.of k[G] V.ρ.asModule ⟶ ModuleCat.of k[G] W.ρ.asModule :=
  ModuleCat.ofHom
    { f.hom.toLinearMap with
      map_smul' := fun r x => to_Module_monoidAlgebra_map_aux V.V W.V V.ρ W.ρ
        f.hom.toLinearMap f.hom.2 r x }

set_option backward.isDefEq.respectTransparency false in

def toModuleMonoidAlgebra : Rep.{w} k G ⥤ ModuleCat k[G] where
  obj V := ModuleCat.of _ V.ρ.asModule
  map f := toModuleMonoidAlgebraMap f

set_option backward.isDefEq.respectTransparency false in

def ofModuleMonoidAlgebra : ModuleCat k[G] ⥤ Rep.{w} k G where
  obj M := Rep.of (Representation.ofModule M)
  map f := ofHom {
    __ := f.hom
    map_smul' r x := f.hom.map_smul (algebraMap k _ r) x
    isIntertwining' g := by ext; apply f.hom.map_smul
  }

def counitIsoAddEquiv {M : ModuleCat.{w} k[G]} :
    (ofModuleMonoidAlgebra ⋙ toModuleMonoidAlgebra).obj M ≃+ M := by
  dsimp [ofModuleMonoidAlgebra, toModuleMonoidAlgebra]
  exact (Representation.ofModule M).asModuleEquiv.toAddEquiv.trans
    (RestrictScalars.addEquiv k k[G] _)

def unitIsoAddEquiv {V : Rep.{w} k G} : V ≃+ (toModuleMonoidAlgebra ⋙
    ofModuleMonoidAlgebra).obj V := by
  dsimp [ofModuleMonoidAlgebra, toModuleMonoidAlgebra]
  exact V.ρ.asModuleEquiv.symm.toAddEquiv.trans (RestrictScalars.addEquiv _ _ _).symm

set_option backward.isDefEq.respectTransparency false in

def counitIso (M : ModuleCat.{w} k[G]) :
    (ofModuleMonoidAlgebra ⋙ toModuleMonoidAlgebra).obj M ≅ M :=
  LinearEquiv.toModuleIso
    { counitIsoAddEquiv with
      map_smul' := fun r x => by
        simp [counitIsoAddEquiv] }

set_option backward.isDefEq.respectTransparency false in

theorem unit_iso_comm (V : Rep.{w} k G) (g : G) (x : V) :
    unitIsoAddEquiv ((V.ρ g).toFun x) = ((ofModuleMonoidAlgebra.obj
      (toModuleMonoidAlgebra.obj V)).ρ g).toFun (unitIsoAddEquiv x) := by
  simp [unitIsoAddEquiv, ofModuleMonoidAlgebra, toModuleMonoidAlgebra]

set_option backward.isDefEq.respectTransparency false in

def unitIso (V : Rep.{w} k G) : V ≅ (toModuleMonoidAlgebra ⋙ ofModuleMonoidAlgebra).obj V :=
  mkIso <| .mk
  { unitIsoAddEquiv (k := k) (G := G) with
    map_smul' r x := show (RestrictScalars.addEquiv _ _ _).symm
      (V.ρ.asModuleEquiv.symm (r • x)) = _ by
      simp only [Representation.asModuleEquiv_symm_map_smul]
      rfl } fun g ↦ by ext; exact unit_iso_comm ..

def equivalenceModuleMonoidAlgebra : Rep.{w} k G ≌ ModuleCat k[G] where
  functor := toModuleMonoidAlgebra
  inverse := ofModuleMonoidAlgebra
  unitIso := NatIso.ofComponents (fun V => unitIso V) (by cat_disch)
  counitIso := NatIso.ofComponents (fun M => counitIso M) (by cat_disch)

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

open MonoidalCategory in

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable {k G : Type u} [CommRing k] [Monoid G] in

-- INSTANCE (free from Core): :

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): free_projective

variable {G : Type u} [Group G] {n : ℕ}

-- INSTANCE (free from Core): diagonal_succ_projective

-- INSTANCE (free from Core): leftRegular_projective

-- INSTANCE (free from Core): trivial_projective_of_subsingleton

end

end Rep
