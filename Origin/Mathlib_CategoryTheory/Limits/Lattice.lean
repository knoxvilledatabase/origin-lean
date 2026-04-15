/-
Extracted from CategoryTheory/Limits/Lattice.lean
Genuine: 10 | Conflates: 0 | Dissolved: 0 | Infrastructure: 10
-/
import Origin.Core
import Mathlib.Order.CompleteLattice
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# Limits in lattice categories are given by infimums and supremums.
-/

universe w u

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.Limits.CompleteLattice

section Semilattice

variable {α : Type u}

variable {J : Type w} [SmallCategory J] [FinCategory J]

def finiteLimitCone [SemilatticeInf α] [OrderTop α] (F : J ⥤ α) : LimitCone F where
  cone :=
    { pt := Finset.univ.inf F.obj
      π := { app := fun _ => homOfLE (Finset.inf_le (Fintype.complete _)) } }
  isLimit := { lift := fun s => homOfLE (Finset.le_inf fun j _ => (s.π.app j).down.down) }

def finiteColimitCocone [SemilatticeSup α] [OrderBot α] (F : J ⥤ α) : ColimitCocone F where
  cocone :=
    { pt := Finset.univ.sup F.obj
      ι := { app := fun _ => homOfLE (Finset.le_sup (Fintype.complete _)) } }
  isColimit := { desc := fun s => homOfLE (Finset.sup_le fun j _ => (s.ι.app j).down.down) }

instance (priority := 100) hasFiniteLimits_of_semilatticeInf_orderTop [SemilatticeInf α]
    [OrderTop α] : HasFiniteLimits α := ⟨by
  intro J 𝒥₁ 𝒥₂
  exact { has_limit := fun F => HasLimit.mk (finiteLimitCone F) }⟩

instance (priority := 100) hasFiniteColimits_of_semilatticeSup_orderBot [SemilatticeSup α]
    [OrderBot α] : HasFiniteColimits α := ⟨by
  intro J 𝒥₁ 𝒥₂
  exact { has_colimit := fun F => HasColimit.mk (finiteColimitCocone F) }⟩

theorem finite_limit_eq_finset_univ_inf [SemilatticeInf α] [OrderTop α] (F : J ⥤ α) :
    limit F = Finset.univ.inf F.obj :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit F) (finiteLimitCone F).isLimit).to_eq

theorem finite_colimit_eq_finset_univ_sup [SemilatticeSup α] [OrderBot α] (F : J ⥤ α) :
    colimit F = Finset.univ.sup F.obj :=
  (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) (finiteColimitCocone F).isColimit).to_eq

theorem finite_product_eq_finset_inf [SemilatticeInf α] [OrderTop α] {ι : Type u} [Fintype ι]
    (f : ι → α) : ∏ᶜ f = Fintype.elems.inf f := by
  trans
  · exact
      (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
          (finiteLimitCone (Discrete.functor f)).isLimit).to_eq
  change Finset.univ.inf (f ∘ discreteEquiv.toEmbedding) = Fintype.elems.inf f
  simp only [← Finset.inf_map, Finset.univ_map_equiv_to_embedding]
  rfl

theorem finite_coproduct_eq_finset_sup [SemilatticeSup α] [OrderBot α] {ι : Type u} [Fintype ι]
    (f : ι → α) : ∐ f = Fintype.elems.sup f := by
  trans
  · exact
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
          (finiteColimitCocone (Discrete.functor f)).isColimit).to_eq
  change Finset.univ.sup (f ∘ discreteEquiv.toEmbedding) = Fintype.elems.sup f
  simp only [← Finset.sup_map, Finset.univ_map_equiv_to_embedding]
  rfl

instance (priority := 100) [SemilatticeInf α] [OrderTop α] : HasBinaryProducts α := by
  have : ∀ x y : α, HasLimit (pair x y) := by
    letI := hasFiniteLimits_of_hasFiniteLimits_of_size.{u} α
    infer_instance
  apply hasBinaryProducts_of_hasLimit_pair

@[simp]
theorem prod_eq_inf [SemilatticeInf α] [OrderTop α] (x y : α) : Limits.prod x y = x ⊓ y :=
  calc
    Limits.prod x y = limit (pair x y) := rfl
    _ = Finset.univ.inf (pair x y).obj := by rw [finite_limit_eq_finset_univ_inf (pair.{u} x y)]
    _ = x ⊓ (y ⊓ ⊤) := rfl
    -- Note: finset.inf is realized as a fold, hence the definitional equality
    _ = x ⊓ y := by rw [inf_top_eq]

instance (priority := 100) [SemilatticeSup α] [OrderBot α] : HasBinaryCoproducts α := by
  have : ∀ x y : α, HasColimit (pair x y) := by
    letI := hasFiniteColimits_of_hasFiniteColimits_of_size.{u} α
    infer_instance
  apply hasBinaryCoproducts_of_hasColimit_pair

@[simp]
theorem coprod_eq_sup [SemilatticeSup α] [OrderBot α] (x y : α) : Limits.coprod x y = x ⊔ y :=
  calc
    Limits.coprod x y = colimit (pair x y) := rfl
    _ = Finset.univ.sup (pair x y).obj := by rw [finite_colimit_eq_finset_univ_sup (pair x y)]
    _ = x ⊔ (y ⊔ ⊥) := rfl
    -- Note: Finset.sup is realized as a fold, hence the definitional equality
    _ = x ⊔ y := by rw [sup_bot_eq]

@[simp]
theorem pullback_eq_inf [SemilatticeInf α] [OrderTop α] {x y z : α} (f : x ⟶ z) (g : y ⟶ z) :
    pullback f g = x ⊓ y :=
  calc
    pullback f g = limit (cospan f g) := rfl
    _ = Finset.univ.inf (cospan f g).obj := by rw [finite_limit_eq_finset_univ_inf]
    _ = z ⊓ (x ⊓ (y ⊓ ⊤)) := rfl
    _ = z ⊓ (x ⊓ y) := by rw [inf_top_eq]
    _ = x ⊓ y := inf_eq_right.mpr (inf_le_of_left_le f.le)

@[simp]
theorem pushout_eq_sup [SemilatticeSup α] [OrderBot α] (x y z : α) (f : z ⟶ x) (g : z ⟶ y) :
    pushout f g = x ⊔ y :=
  calc
    pushout f g = colimit (span f g) := rfl
    _ = Finset.univ.sup (span f g).obj := by rw [finite_colimit_eq_finset_univ_sup]
    _ = z ⊔ (x ⊔ (y ⊔ ⊥)) := rfl
    _ = z ⊔ (x ⊔ y) := by rw [sup_bot_eq]
    _ = x ⊔ y := sup_eq_right.mpr (le_sup_of_le_left f.le)

end Semilattice

variable {α : Type u} [CompleteLattice α]

variable {J : Type u} [SmallCategory J]

def limitCone (F : J ⥤ α) : LimitCone F where
  cone :=
    { pt := iInf F.obj
      π := { app := fun _ => homOfLE (CompleteLattice.sInf_le _ _ (Set.mem_range_self _)) } }
  isLimit :=
    { lift := fun s =>
        homOfLE (CompleteLattice.le_sInf _ _ (by rintro _ ⟨j, rfl⟩; exact (s.π.app j).le)) }

def colimitCocone (F : J ⥤ α) : ColimitCocone F where
  cocone :=
    { pt := iSup F.obj
      ι := { app := fun _ => homOfLE (CompleteLattice.le_sSup _ _ (Set.mem_range_self _)) } }
  isColimit :=
    { desc := fun s =>
        homOfLE (CompleteLattice.sSup_le _ _ (by rintro _ ⟨j, rfl⟩; exact (s.ι.app j).le)) }

instance (priority := 100) hasLimits_of_completeLattice : HasLimits α where
  has_limits_of_shape _ := { has_limit := fun F => HasLimit.mk (limitCone F) }

instance (priority := 100) hasColimits_of_completeLattice : HasColimits α where
  has_colimits_of_shape _ := { has_colimit := fun F => HasColimit.mk (colimitCocone F) }

theorem limit_eq_iInf (F : J ⥤ α) : limit F = iInf F.obj :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit F) (limitCone F).isLimit).to_eq

theorem colimit_eq_iSup (F : J ⥤ α) : colimit F = iSup F.obj :=
  (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) (colimitCocone F).isColimit).to_eq

end CategoryTheory.Limits.CompleteLattice
