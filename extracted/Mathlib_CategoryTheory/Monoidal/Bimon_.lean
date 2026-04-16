/-
Extracted from CategoryTheory/Monoidal/Bimon_.lean
Genuine: 25 | Conflates: 0 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core
import Mathlib.CategoryTheory.Monoidal.Comon_

noncomputable section

/-!
# The category of bimonoids in a braided monoidal category.

We define bimonoids in a braided monoidal category `C`
as comonoid objects in the category of monoid objects in `C`.

We verify that this is equivalent to the monoid objects in the category of comonoid objects.

## TODO
* Construct the category of modules, and show that it is monoidal with a monoidal forgetful functor
  to `C`.
* Some form of Tannaka reconstruction:
  given a monoidal functor `F : C ⥤ D` into a braided category `D`,
  the internal endomorphisms of `F` form a bimonoid in presheaves on `D`,
  in good circumstances this is representable by a bimonoid in `D`, and then
  `C` is monoidally equivalent to the modules over that bimonoid.
-/

noncomputable section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory C]

open scoped Mon_Class Comon_Class

class Bimon_Class (M : C) extends Mon_Class M, Comon_Class M where
  /- For the names of the conditions below, the unprimed names are reserved for the version where
  the argument `M` is explicit. -/
  mul_comul' : μ[M] ≫ Δ[M] = (Δ[M] ⊗ Δ[M]) ≫ tensorμ M M M M ≫ (μ[M] ⊗ μ[M]) := by aesop_cat
  one_comul' : η[M] ≫ Δ[M] = η[M ⊗ M] := by aesop_cat
  mul_counit' : μ[M] ≫ ε[M] = ε[M ⊗ M] := by aesop_cat
  one_counit' : η[M] ≫ ε[M] = 𝟙 (𝟙_ C) := by aesop_cat

namespace Bimon_Class

attribute [reassoc] mul_comul' one_comul' mul_counit' one_counit'

variable (M : C) [Bimon_Class M]

@[reassoc (attr := simp)]
theorem mul_comul (M : C) [Bimon_Class M] :
    μ[M] ≫ Δ[M] = (Δ[M] ⊗ Δ[M]) ≫ tensorμ M M M M ≫ (μ[M] ⊗ μ[M]) :=
  mul_comul'

@[reassoc (attr := simp)]
theorem one_comul (M : C) [Bimon_Class M] : η[M] ≫ Δ[M] = η[M ⊗ M] := one_comul'

@[reassoc (attr := simp)]
theorem mul_counit (M : C) [Bimon_Class M] : μ[M] ≫ ε[M] = ε[M ⊗ M] := mul_counit'

@[reassoc (attr := simp)]
theorem one_counit (M : C) [Bimon_Class M] : η[M] ≫ ε[M] = 𝟙 (𝟙_ C) := one_counit'

end Bimon_Class

class IsBimon_Hom {M N : C} [Bimon_Class M] [Bimon_Class N] (f : M ⟶ N) extends
    IsMon_Hom f, IsComon_Hom f : Prop

variable (C)

def Bimon_ := Comon_ (Mon_ C)

namespace Bimon_

instance : Category (Bimon_ C) := inferInstanceAs (Category (Comon_ (Mon_ C)))

@[ext] lemma ext {X Y : Bimon_ C} {f g : X ⟶ Y} (w : f.hom.hom = g.hom.hom) : f = g :=
  Comon_.Hom.ext (Mon_.Hom.ext w)

@[simp] theorem id_hom' (M : Bimon_ C) : Comon_.Hom.hom (𝟙 M) = 𝟙 M.X := rfl

@[simp]
theorem comp_hom' {M N K : Bimon_ C} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

abbrev toMon_ : Bimon_ C ⥤ Mon_ C := Comon_.forget (Mon_ C)

def forget : Bimon_ C ⥤ C := toMon_ C ⋙ Mon_.forget C

@[simp]
theorem toMon_forget : toMon_ C ⋙ Mon_.forget C = forget C := rfl

@[simps!]
def toComon_ : Bimon_ C ⥤ Comon_ C := (Mon_.forget C).mapComon

@[simp]
theorem toComon_forget : toComon_ C ⋙ Comon_.forget C = forget C := rfl

def toMon_Comon_obj (M : Bimon_ C) : Mon_ (Comon_ C) where
  X := (toComon_ C).obj M
  one := { hom := M.X.one }
  mul :=
  { hom := M.X.mul,
    hom_comul := by dsimp; simp [tensor_μ] }

attribute [simps] toMon_Comon_obj -- We add this after the fact to avoid a timeout.

@[simps]
def toMon_Comon_ : Bimon_ C ⥤ Mon_ (Comon_ C) where
  obj := toMon_Comon_obj C
  map f :=
  { hom := (toComon_ C).map f }

@[simps]
def ofMon_Comon_obj (M : Mon_ (Comon_ C)) : Bimon_ C where
  X := (Comon_.forget C).mapMon.obj M
  counit := { hom := M.X.counit }
  comul :=
  { hom := M.X.comul,
    mul_hom := by dsimp; simp [tensor_μ] }

@[simps]
def ofMon_Comon_ : Mon_ (Comon_ C) ⥤ Bimon_ C where
  obj := ofMon_Comon_obj C
  map f :=
  { hom := (Comon_.forget C).mapMon.map f }

def equivMon_Comon_ : Bimon_ C ≌ Mon_ (Comon_ C) where
  functor := toMon_Comon_ C
  inverse := ofMon_Comon_ C
  unitIso := NatIso.ofComponents (fun _ => Comon_.mkIso (Mon_.mkIso (Iso.refl _)))
  counitIso := NatIso.ofComponents (fun _ => Mon_.mkIso (Comon_.mkIso (Iso.refl _)))

/-! # The trivial bimonoid -/

@[simps!]
def trivial : Bimon_ C := Comon_.trivial (Mon_ C)

@[simps]
def trivial_to (A : Bimon_ C) : trivial C ⟶ A :=
  { hom := (default : Mon_.trivial C ⟶ A.X), }

@[simps!]
def to_trivial (A : Bimon_ C) : A ⟶ trivial C :=
  (default : @Quiver.Hom (Comon_ (Mon_ C)) _ A (Comon_.trivial (Mon_ C)))

/-! # Additional lemmas -/

variable {C}

@[reassoc]
theorem one_comul (M : Bimon_ C) :
    M.X.one ≫ M.comul.hom = (λ_ _).inv ≫ (M.X.one ⊗ M.X.one) := by
  simp

@[reassoc]
theorem mul_counit (M : Bimon_ C) :
    M.X.mul ≫ M.counit.hom = (M.counit.hom ⊗ M.counit.hom) ≫ (λ_ _).hom := by
  simp

@[reassoc (attr := simp)] theorem compatibility (M : Bimon_ C) :
    (M.comul.hom ⊗ M.comul.hom) ≫
      (α_ _ _ (M.X.X ⊗ M.X.X)).hom ≫ M.X.X ◁ (α_ _ _ _).inv ≫
      M.X.X ◁ (β_ M.X.X M.X.X).hom ▷ M.X.X ≫
      M.X.X ◁ (α_ _ _ _).hom ≫ (α_ _ _ _).inv ≫
      (M.X.mul ⊗ M.X.mul) =
    M.X.mul ≫ M.comul.hom := by
  have := (Mon_.Hom.mul_hom M.comul).symm
  simpa [-Mon_.Hom.mul_hom, tensorμ] using this

@[reassoc (attr := simp)] theorem comul_counit_hom (M : Bimon_ C) :
    M.comul.hom ≫ (_ ◁ M.counit.hom) = (ρ_ _).inv := by
  simpa [- Comon_.comul_counit] using congr_arg Mon_.Hom.hom M.comul_counit

@[reassoc (attr := simp)] theorem counit_comul_hom (M : Bimon_ C) :
    M.comul.hom ≫ (M.counit.hom ▷ _) = (λ_ _).inv := by
  simpa [- Comon_.counit_comul] using congr_arg Mon_.Hom.hom M.counit_comul

@[reassoc (attr := simp)] theorem comul_assoc_hom (M : Bimon_ C) :
    M.comul.hom ≫ (M.X.X ◁ M.comul.hom) =
      M.comul.hom ≫ (M.comul.hom ▷ M.X.X) ≫ (α_ M.X.X M.X.X M.X.X).hom := by
  simpa [- Comon_.comul_assoc] using congr_arg Mon_.Hom.hom M.comul_assoc

@[reassoc] theorem hom_comul_hom {M N : Bimon_ C} (f : M ⟶ N) :
    f.hom.hom ≫ N.comul.hom = M.comul.hom ≫ (f.hom.hom ⊗ f.hom.hom) := by
  simpa [- Comon_.Hom.hom_comul] using congr_arg Mon_.Hom.hom f.hom_comul

@[reassoc] theorem hom_counit_hom {M N : Bimon_ C} (f : M ⟶ N) :
    f.hom.hom ≫ N.counit.hom = M.counit.hom := by
  simpa [- Comon_.Hom.hom_counit] using congr_arg Mon_.Hom.hom f.hom_counit

end Bimon_
