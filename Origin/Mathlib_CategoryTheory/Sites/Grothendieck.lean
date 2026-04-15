/-
Extracted from CategoryTheory/Sites/Grothendieck.lean
Genuine: 62 of 81 | Dissolved: 0 | Infrastructure: 19
-/
import Origin.Core
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Order.Copy
import Mathlib.Data.Set.Subsingleton

/-!
# Grothendieck topologies

Definition and lemmas about Grothendieck topologies.
A Grothendieck topology for a category `C` is a set of sieves on each object `X` satisfying
certain closure conditions.

Alternate versions of the axioms (in arrow form) are also described.
Two explicit examples of Grothendieck topologies are given:
* The dense topology
* The atomic topology
as well as the complete lattice structure on Grothendieck topologies (which gives two additional
explicit topologies: the discrete and trivial topologies.)

A pretopology, or a basis for a topology is defined in
`Mathlib/CategoryTheory/Sites/Pretopology.lean`. The topology associated
to a topological space is defined in `Mathlib/CategoryTheory/Sites/Spaces.lean`.

## Tags

Grothendieck topology, coverage, pretopology, site

## References

* [nLab, *Grothendieck topology*](https://ncatlab.org/nlab/show/Grothendieck+topology)
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]

## Implementation notes

We use the definition of [nlab] and [MM92][] (Chapter III, Section 2), where Grothendieck topologies
are saturated collections of morphisms, rather than the notions of the Stacks project (00VG) and
the Elephant, in which topologies are allowed to be unsaturated, and are then completed.
TODO (BM): Add the definition from Stacks, as a pretopology, and complete to a topology.

This is so that we can produce a bijective correspondence between Grothendieck topologies on a
small category and Lawvere-Tierney topologies on its presheaf topos, as well as the equivalence
between Grothendieck topoi and left exact reflective subcategories of presheaf toposes.
-/

universe v₁ u₁ v u

namespace CategoryTheory

open Category

variable (C : Type u) [Category.{v} C]

structure GrothendieckTopology where
  /-- A Grothendieck topology on `C` consists of a set of sieves for each object `X`,
    which satisfy some axioms. -/
  sieves : ∀ X : C, Set (Sieve X)
  /-- The sieves associated to each object must contain the top sieve.
    Use `GrothendieckTopology.top_mem`. -/
  top_mem' : ∀ X, ⊤ ∈ sieves X
  /-- Stability under pullback. Use `GrothendieckTopology.pullback_stable`. -/
  pullback_stable' : ∀ ⦃X Y : C⦄ ⦃S : Sieve X⦄ (f : Y ⟶ X), S ∈ sieves X → S.pullback f ∈ sieves Y
  /-- Transitivity of sieves in a Grothendieck topology.
    Use `GrothendieckTopology.transitive`. -/
  transitive' :
    ∀ ⦃X⦄ ⦃S : Sieve X⦄ (_ : S ∈ sieves X) (R : Sieve X),
      (∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → R.pullback f ∈ sieves Y) → R ∈ sieves X

namespace GrothendieckTopology

instance : DFunLike (GrothendieckTopology C) C (fun X ↦ Set (Sieve X)) where
  coe J X := sieves J X
  coe_injective' J₁ J₂ h := by cases J₁; cases J₂; congr

variable {C}

variable {X Y : C} {S R : Sieve X}

variable (J : GrothendieckTopology C)

@[ext]
theorem ext {J₁ J₂ : GrothendieckTopology C} (h : (J₁ : ∀ X : C, Set (Sieve X)) = J₂) : J₁ = J₂ :=
  DFunLike.coe_injective h

@[simp]
theorem mem_sieves_iff_coe : S ∈ J.sieves X ↔ S ∈ J X :=
  Iff.rfl

@[simp]
theorem top_mem (X : C) : ⊤ ∈ J X :=
  J.top_mem' X

@[simp]
theorem pullback_stable (f : Y ⟶ X) (hS : S ∈ J X) : S.pullback f ∈ J Y :=
  J.pullback_stable' f hS

variable {J} in

@[simp]
lemma pullback_mem_iff_of_isIso {i : X ⟶ Y} [IsIso i] {S : Sieve Y} :
    S.pullback i ∈ J _ ↔ S ∈ J _ := by
  refine ⟨fun H ↦ ?_, J.pullback_stable i⟩
  convert J.pullback_stable (inv i) H
  rw [← Sieve.pullback_comp, IsIso.inv_hom_id, Sieve.pullback_id]

theorem transitive (hS : S ∈ J X) (R : Sieve X) (h : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → R.pullback f ∈ J Y) :
    R ∈ J X :=
  J.transitive' hS R h

theorem covering_of_eq_top : S = ⊤ → S ∈ J X := fun h => h.symm ▸ J.top_mem X

theorem superset_covering (Hss : S ≤ R) (sjx : S ∈ J X) : R ∈ J X := by
  apply J.transitive sjx R fun Y f hf => _
  intros Y f hf
  apply covering_of_eq_top
  rw [← top_le_iff, ← S.pullback_eq_top_of_mem hf]
  apply Sieve.pullback_monotone _ Hss

theorem intersection_covering (rj : R ∈ J X) (sj : S ∈ J X) : R ⊓ S ∈ J X := by
  apply J.transitive rj _ fun Y f Hf => _
  intros Y f hf
  rw [Sieve.pullback_inter, R.pullback_eq_top_of_mem hf]
  simp [sj]

@[simp]
theorem intersection_covering_iff : R ⊓ S ∈ J X ↔ R ∈ J X ∧ S ∈ J X :=
  ⟨fun h => ⟨J.superset_covering inf_le_left h, J.superset_covering inf_le_right h⟩, fun t =>
    intersection_covering _ t.1 t.2⟩

theorem bind_covering {S : Sieve X} {R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y} (hS : S ∈ J X)
    (hR : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (H : S f), R H ∈ J Y) : Sieve.bind S R ∈ J X :=
  J.transitive hS _ fun _ f hf => superset_covering J (Sieve.le_pullback_bind S R f hf) (hR hf)

def Covers (S : Sieve X) (f : Y ⟶ X) : Prop :=
  S.pullback f ∈ J Y

theorem covers_iff (S : Sieve X) (f : Y ⟶ X) : J.Covers S f ↔ S.pullback f ∈ J Y :=
  Iff.rfl

theorem covering_iff_covers_id (S : Sieve X) : S ∈ J X ↔ J.Covers S (𝟙 X) := by simp [covers_iff]

theorem arrow_max (f : Y ⟶ X) (S : Sieve X) (hf : S f) : J.Covers S f := by
  rw [Covers, (Sieve.pullback_eq_top_iff_mem f).1 hf]
  apply J.top_mem

theorem arrow_stable (f : Y ⟶ X) (S : Sieve X) (h : J.Covers S f) {Z : C} (g : Z ⟶ Y) :
    J.Covers S (g ≫ f) := by
  rw [covers_iff] at h ⊢
  simp [h, Sieve.pullback_comp]

theorem arrow_trans (f : Y ⟶ X) (S R : Sieve X) (h : J.Covers S f) :
    (∀ {Z : C} (g : Z ⟶ X), S g → J.Covers R g) → J.Covers R f := by
  intro k
  apply J.transitive h
  intro Z g hg
  rw [← Sieve.pullback_comp]
  apply k (g ≫ f) hg

theorem arrow_intersect (f : Y ⟶ X) (S R : Sieve X) (hS : J.Covers S f) (hR : J.Covers R f) :
    J.Covers (S ⊓ R) f := by simpa [covers_iff] using And.intro hS hR

variable (C)

def trivial : GrothendieckTopology C where
  sieves _ := {⊤}
  top_mem' _ := rfl
  pullback_stable' X Y S f hf := by
    rw [Set.mem_singleton_iff] at hf ⊢
    simp [hf]
  transitive' X S hS R hR := by
    rw [Set.mem_singleton_iff, ← Sieve.id_mem_iff_eq_top] at hS
    simpa using hR hS

def discrete : GrothendieckTopology C where
  sieves _ := Set.univ
  top_mem' := by simp
  pullback_stable' X Y f := by simp
  transitive' := by simp

variable {C}

theorem trivial_covering : S ∈ trivial C X ↔ S = ⊤ :=
  Set.mem_singleton_iff

instance instLEGrothendieckTopology : LE (GrothendieckTopology C) where
  le J₁ J₂ := (J₁ : ∀ X : C, Set (Sieve X)) ≤ (J₂ : ∀ X : C, Set (Sieve X))

theorem le_def {J₁ J₂ : GrothendieckTopology C} : J₁ ≤ J₂ ↔ (J₁ : ∀ X : C, Set (Sieve X)) ≤ J₂ :=
  Iff.rfl

instance : PartialOrder (GrothendieckTopology C) :=
  { instLEGrothendieckTopology with
    le_refl := fun _ => le_def.mpr le_rfl
    le_trans := fun _ _ _ h₁₂ h₂₃ => le_def.mpr (le_trans h₁₂ h₂₃)
    le_antisymm := fun _ _ h₁₂ h₂₁ => GrothendieckTopology.ext (le_antisymm h₁₂ h₂₁) }

instance : InfSet (GrothendieckTopology C) where
  sInf T :=
    { sieves := sInf (sieves '' T)
      top_mem' := by
        rintro X S ⟨⟨_, J, hJ, rfl⟩, rfl⟩
        simp
      pullback_stable' := by
        rintro X Y S hS f _ ⟨⟨_, J, hJ, rfl⟩, rfl⟩
        apply J.pullback_stable _ (f _ ⟨⟨_, _, hJ, rfl⟩, rfl⟩)
      transitive' := by
        rintro X S hS R h _ ⟨⟨_, J, hJ, rfl⟩, rfl⟩
        apply
          J.transitive (hS _ ⟨⟨_, _, hJ, rfl⟩, rfl⟩) _ fun Y f hf => h hf _ ⟨⟨_, _, hJ, rfl⟩, rfl⟩ }

lemma mem_sInf (s : Set (GrothendieckTopology C)) {X : C} (S : Sieve X) :
    S ∈ sInf s X ↔ ∀ t ∈ s, S ∈ t X := by
  show S ∈ sInf (sieves '' s) X ↔ _
  simp

theorem isGLB_sInf (s : Set (GrothendieckTopology C)) : IsGLB s (sInf s) := by
  refine @IsGLB.of_image _ _ _ _ sieves ?_ _ _ ?_
  · #adaptation_note
    /--
    This proof used to be `rfl`,
    but has been temporarily broken by https://github.com/leanprover/lean4/pull/5329.
    It can hopefully be restored after https://github.com/leanprover/lean4/pull/5359
    -/
    exact Iff.rfl
  · exact _root_.isGLB_sInf _

instance : CompleteLattice (GrothendieckTopology C) :=
  CompleteLattice.copy (completeLatticeOfInf _ isGLB_sInf) _ rfl (discrete C)
    (by
      apply le_antisymm
      · exact @CompleteLattice.le_top _ (completeLatticeOfInf _ isGLB_sInf) (discrete C)
      · intro X S _
        apply Set.mem_univ)
    (trivial C)
    (by
      apply le_antisymm
      · intro X S hS
        rw [trivial_covering] at hS
        apply covering_of_eq_top _ hS
      · exact @CompleteLattice.bot_le _ (completeLatticeOfInf _ isGLB_sInf) (trivial C))
    _ rfl _ rfl _ rfl sInf rfl

instance : Inhabited (GrothendieckTopology C) :=
  ⟨⊤⟩

@[simp]
theorem trivial_eq_bot : trivial C = ⊥ :=
  rfl

@[simp]
theorem discrete_eq_top : discrete C = ⊤ :=
  rfl

@[simp]
theorem bot_covering : S ∈ (⊥ : GrothendieckTopology C) X ↔ S = ⊤ :=
  trivial_covering

@[simp]
theorem top_covering : S ∈ (⊤ : GrothendieckTopology C) X :=
  ⟨⟩

theorem bot_covers (S : Sieve X) (f : Y ⟶ X) : (⊥ : GrothendieckTopology C).Covers S f ↔ S f := by
  rw [covers_iff, bot_covering, ← Sieve.pullback_eq_top_iff_mem]

@[simp]
theorem top_covers (S : Sieve X) (f : Y ⟶ X) : (⊤ : GrothendieckTopology C).Covers S f := by
  simp [covers_iff]

def dense : GrothendieckTopology C where
  sieves X S := ∀ {Y : C} (f : Y ⟶ X), ∃ (Z : _) (g : Z ⟶ Y), S (g ≫ f)
  top_mem' _ Y _ := ⟨Y, 𝟙 Y, ⟨⟩⟩
  pullback_stable' := by
    intro X Y S h H Z f
    rcases H (f ≫ h) with ⟨W, g, H'⟩
    exact ⟨W, g, by simpa⟩
  transitive' := by
    intro X S H₁ R H₂ Y f
    rcases H₁ f with ⟨Z, g, H₃⟩
    rcases H₂ H₃ (𝟙 Z) with ⟨W, h, H₄⟩
    exact ⟨W, h ≫ g, by simpa using H₄⟩

theorem dense_covering : S ∈ dense X ↔ ∀ {Y} (f : Y ⟶ X), ∃ (Z : _) (g : Z ⟶ Y), S (g ≫ f) :=
  Iff.rfl

def RightOreCondition (C : Type u) [Category.{v} C] : Prop :=
  ∀ {X Y Z : C} (yx : Y ⟶ X) (zx : Z ⟶ X), ∃ (W : _) (wy : W ⟶ Y) (wz : W ⟶ Z), wy ≫ yx = wz ≫ zx

theorem right_ore_of_pullbacks [Limits.HasPullbacks C] : RightOreCondition C := fun _ _ =>
  ⟨_, _, _, Limits.pullback.condition⟩

def atomic (hro : RightOreCondition C) : GrothendieckTopology C where
  sieves X S := ∃ (Y : _) (f : Y ⟶ X), S f
  top_mem' _ := ⟨_, 𝟙 _, ⟨⟩⟩
  pullback_stable' := by
    rintro X Y S h ⟨Z, f, hf⟩
    rcases hro h f with ⟨W, g, k, comm⟩
    refine ⟨_, g, ?_⟩
    simp [comm, hf]
  transitive' := by
    rintro X S ⟨Y, f, hf⟩ R h
    rcases h hf with ⟨Z, g, hg⟩
    exact ⟨_, _, hg⟩

def Cover (X : C) : Type max u v :=
  { S : Sieve X // S ∈ J X } -- deriving Preorder

instance (X : C) : Preorder (J.Cover X) :=
  show Preorder {S : Sieve X // S ∈ J X} from inferInstance

namespace Cover

variable {J}

instance : CoeOut (J.Cover X) (Sieve X) := ⟨fun S => S.1⟩

instance : CoeFun (J.Cover X) fun _ => ∀ ⦃Y⦄ (_ : Y ⟶ X), Prop := ⟨fun S => (S : Sieve X)⟩

theorem condition (S : J.Cover X) : (S : Sieve X) ∈ J X := S.2

@[ext]
theorem ext (S T : J.Cover X) (h : ∀ ⦃Y⦄ (f : Y ⟶ X), S f ↔ T f) : S = T :=
  Subtype.ext <| Sieve.ext h

instance : OrderTop (J.Cover X) :=
  { (inferInstance : Preorder (J.Cover X)) with
    top := ⟨⊤, J.top_mem _⟩
    le_top := fun _ _ _ _ => by tauto }

instance : SemilatticeInf (J.Cover X) :=
  { (inferInstance : Preorder _) with
    inf := fun S T => ⟨S ⊓ T, J.intersection_covering S.condition T.condition⟩
    le_antisymm := fun _ _ h1 h2 => ext _ _ fun {Y} f => ⟨by apply h1, by apply h2⟩
    inf_le_left := fun _ _ _ _ hf => hf.1
    inf_le_right := fun _ _ _ _ hf => hf.2
    le_inf := fun _ _ _ h1 h2 _ _ h => ⟨h1 _ h, h2 _ h⟩ }

instance : Inhabited (J.Cover X) :=
  ⟨⊤⟩

@[ext]
structure Arrow (S : J.Cover X) where
  /-- The source of the arrow. -/
  Y : C
  /-- The arrow itself. -/
  f : Y ⟶ X
  /-- The given arrow is contained in the given sieve. -/
  hf : S f

@[ext]
structure Arrow.Relation {S : J.Cover X} (I₁ I₂ : S.Arrow) where
  /-- The source of the arrows defining the relation. -/
  Z : C
  /-- The first arrow defining the relation. -/
  g₁ : Z ⟶ I₁.Y
  /-- The second arrow defining the relation. -/
  g₂ : Z ⟶ I₂.Y
  /-- The relation itself. -/
  w : g₁ ≫ I₁.f = g₂ ≫ I₂.f := by aesop_cat

attribute [reassoc] Arrow.Relation.w

@[simps]
def Arrow.precomp {S : J.Cover X} (I : S.Arrow) {Z : C} (g : Z ⟶ I.Y) : S.Arrow :=
  ⟨Z, g ≫ I.f, S.1.downward_closed I.hf g⟩

@[simps]
def Arrow.precompRelation {S : J.Cover X} (I : S.Arrow) {Z : C} (g : Z ⟶ I.Y) :
    (I.precomp g).Relation I where
  g₁ := 𝟙 _
  g₂ := g

@[simps]
def Arrow.map {S T : J.Cover X} (I : S.Arrow) (f : S ⟶ T) : T.Arrow :=
  ⟨I.Y, I.f, f.le _ I.hf⟩

@[simps]
def Arrow.Relation.map {S T : J.Cover X} {I₁ I₂ : S.Arrow}
    (r : I₁.Relation I₂) (f : S ⟶ T) : (I₁.map f).Relation (I₂.map f) where
  w := r.w

def pullback (S : J.Cover X) (f : Y ⟶ X) : J.Cover Y :=
  ⟨Sieve.pullback f S, J.pullback_stable _ S.condition⟩

@[simps]
def Arrow.base {f : Y ⟶ X} {S : J.Cover X} (I : (S.pullback f).Arrow) : S.Arrow :=
  ⟨I.Y, I.f ≫ f, I.hf⟩

def Arrow.Relation.base
    {f : Y ⟶ X} {S : J.Cover X} {I₁ I₂ : (S.pullback f).Arrow}
    (r : I₁.Relation I₂) : I₁.base.Relation I₂.base where
  g₁ := r.g₁
  g₂ := r.g₂
  w := by simp [r.w_assoc]

@[simp]
theorem coe_pullback {Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (S : J.Cover X) :
    (S.pullback f) g ↔ S (g ≫ f) :=
  Iff.rfl

def pullbackId (S : J.Cover X) : S.pullback (𝟙 X) ≅ S :=
  eqToIso <| Cover.ext _ _ fun Y f => by simp

def pullbackComp {X Y Z : C} (S : J.Cover X) (f : Z ⟶ Y) (g : Y ⟶ X) :
    S.pullback (f ≫ g) ≅ (S.pullback g).pullback f :=
  eqToIso <| Cover.ext _ _ fun Y f => by simp

def bind {X : C} (S : J.Cover X) (T : ∀ I : S.Arrow, J.Cover I.Y) : J.Cover X :=
  ⟨Sieve.bind S fun Y f hf => T ⟨Y, f, hf⟩,
    J.bind_covering S.condition fun _ _ _ => (T { Y := _, f := _, hf := _ }).condition⟩

def bindToBase {X : C} (S : J.Cover X) (T : ∀ I : S.Arrow, J.Cover I.Y) : S.bind T ⟶ S :=
  homOfLE <| by
    rintro Y f ⟨Z, e1, e2, h1, _, h3⟩
    rw [← h3]
    apply Sieve.downward_closed
    exact h1

noncomputable def Arrow.middle {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : C :=
  I.hf.choose

noncomputable def Arrow.toMiddleHom {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : I.Y ⟶ I.middle :=
  I.hf.choose_spec.choose

noncomputable def Arrow.fromMiddleHom {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : I.middle ⟶ X :=
  I.hf.choose_spec.choose_spec.choose

theorem Arrow.from_middle_condition {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : S I.fromMiddleHom :=
  I.hf.choose_spec.choose_spec.choose_spec.choose

noncomputable def Arrow.fromMiddle {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : S.Arrow :=
  ⟨_, I.fromMiddleHom, I.from_middle_condition⟩

theorem Arrow.to_middle_condition {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : (T I.fromMiddle) I.toMiddleHom :=
  I.hf.choose_spec.choose_spec.choose_spec.choose_spec.1

noncomputable def Arrow.toMiddle {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : (T I.fromMiddle).Arrow :=
  ⟨_, I.toMiddleHom, I.to_middle_condition⟩

theorem Arrow.middle_spec {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : I.toMiddleHom ≫ I.fromMiddleHom = I.f :=
  I.hf.choose_spec.choose_spec.choose_spec.choose_spec.2

@[ext]
structure Relation (S : J.Cover X) where
  /-- The first arrow. -/
  fst : S.Arrow
  /-- The second arrow. -/
  snd : S.Arrow
  /-- The relation between the two arrows. -/
  r : fst.Relation snd

@[simps]
def Relation.mk' {S : J.Cover X} {fst snd : S.Arrow} (r : fst.Relation snd) :
    S.Relation where
  r := r

@[simps]
def index {D : Type u₁} [Category.{v₁} D] (S : J.Cover X) (P : Cᵒᵖ ⥤ D) :
    Limits.MulticospanIndex D where
  L := S.Arrow
  R := S.Relation
  fstTo I := I.fst
  sndTo I := I.snd
  left I := P.obj (Opposite.op I.Y)
  right I := P.obj (Opposite.op I.r.Z)
  fst I := P.map I.r.g₁.op
  snd I := P.map I.r.g₂.op

abbrev multifork {D : Type u₁} [Category.{v₁} D] (S : J.Cover X) (P : Cᵒᵖ ⥤ D) :
    Limits.Multifork (S.index P) :=
  Limits.Multifork.ofι _ (P.obj (Opposite.op X)) (fun I => P.map I.f.op)
    (by
      intro I
      dsimp
      simp only [← P.map_comp, ← op_comp, I.r.w])

noncomputable abbrev toMultiequalizer {D : Type u₁} [Category.{v₁} D] (S : J.Cover X)
    (P : Cᵒᵖ ⥤ D) [Limits.HasMultiequalizer (S.index P)] :
    P.obj (Opposite.op X) ⟶ Limits.multiequalizer (S.index P) :=
  Limits.Multiequalizer.lift _ _ (fun I => P.map I.f.op)
    (by
      intro I
      dsimp only [index, Relation.fst, Relation.snd]
      simp only [← P.map_comp, ← op_comp, I.r.w])

end Cover

@[simps obj]
def pullback (f : Y ⟶ X) : J.Cover X ⥤ J.Cover Y where
  obj S := S.pullback f
  map f := (Sieve.pullback_monotone _ f.le).hom

def pullbackId (X : C) : J.pullback (𝟙 X) ≅ 𝟭 _ :=
  NatIso.ofComponents fun S => S.pullbackId

def pullbackComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    J.pullback (f ≫ g) ≅ J.pullback g ⋙ J.pullback f :=
  NatIso.ofComponents fun S => S.pullbackComp f g

end GrothendieckTopology

end CategoryTheory
