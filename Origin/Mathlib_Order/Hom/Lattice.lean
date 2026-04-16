/-
Extracted from Order/Hom/Lattice.lean
Genuine: 115 | Conflates: 0 | Dissolved: 0 | Infrastructure: 211
-/
import Origin.Core
import Mathlib.Order.Hom.Bounded
import Mathlib.Order.SymmDiff

noncomputable section

/-!
# Lattice homomorphisms

This file defines (bounded) lattice homomorphisms.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `SupHom`: Maps which preserve `⊔`.
* `InfHom`: Maps which preserve `⊓`.
* `SupBotHom`: Finitary supremum homomorphisms. Maps which preserve `⊔` and `⊥`.
* `InfTopHom`: Finitary infimum homomorphisms. Maps which preserve `⊓` and `⊤`.
* `LatticeHom`: Lattice homomorphisms. Maps which preserve `⊔` and `⊓`.
* `BoundedLatticeHom`: Bounded lattice homomorphisms. Maps which preserve `⊤`, `⊥`, `⊔` and `⊓`.

## Typeclasses

* `SupHomClass`
* `InfHomClass`
* `SupBotHomClass`
* `InfTopHomClass`
* `LatticeHomClass`
* `BoundedLatticeHomClass`

## TODO

Do we need more intersections between `BotHom`, `TopHom` and lattice homomorphisms?
-/

open Function OrderDual

variable {F ι α β γ δ : Type*}

structure SupHom (α β : Type*) [Max α] [Max β] where
  /-- The underlying function of a `SupHom` -/
  toFun : α → β
  /-- A `SupHom` preserves suprema. -/
  map_sup' (a b : α) : toFun (a ⊔ b) = toFun a ⊔ toFun b

structure InfHom (α β : Type*) [Min α] [Min β] where
  /-- The underlying function of an `InfHom` -/
  toFun : α → β
  /-- An `InfHom` preserves infima. -/
  map_inf' (a b : α) : toFun (a ⊓ b) = toFun a ⊓ toFun b

structure SupBotHom (α β : Type*) [Max α] [Max β] [Bot α] [Bot β] extends SupHom α β where
  /-- A `SupBotHom` preserves the bottom element. -/
  map_bot' : toFun ⊥ = ⊥

structure InfTopHom (α β : Type*) [Min α] [Min β] [Top α] [Top β] extends InfHom α β where
  /-- An `InfTopHom` preserves the top element. -/
  map_top' : toFun ⊤ = ⊤

structure LatticeHom (α β : Type*) [Lattice α] [Lattice β] extends SupHom α β where
  /-- A `LatticeHom` preserves infima. -/
  map_inf' (a b : α) : toFun (a ⊓ b) = toFun a ⊓ toFun b

structure BoundedLatticeHom (α β : Type*) [Lattice α] [Lattice β] [BoundedOrder α]
  [BoundedOrder β] extends LatticeHom α β where
  /-- A `BoundedLatticeHom` preserves the top element. -/
  map_top' : toFun ⊤ = ⊤
  /-- A `BoundedLatticeHom` preserves the bottom element. -/
  map_bot' : toFun ⊥ = ⊥

initialize_simps_projections SupBotHom (+toSupHom, -toFun)

initialize_simps_projections InfTopHom (+toInfHom, -toFun)

initialize_simps_projections LatticeHom (+toSupHom, -toFun)

initialize_simps_projections BoundedLatticeHom (+toLatticeHom, -toFun)

section

class SupHomClass (F α β : Type*) [Max α] [Max β] [FunLike F α β] : Prop where
  /-- A `SupHomClass` morphism preserves suprema. -/
  map_sup (f : F) (a b : α) : f (a ⊔ b) = f a ⊔ f b

class InfHomClass (F α β : Type*) [Min α] [Min β] [FunLike F α β] : Prop where
  /-- An `InfHomClass` morphism preserves infima. -/
  map_inf (f : F) (a b : α) : f (a ⊓ b) = f a ⊓ f b

class SupBotHomClass (F α β : Type*) [Max α] [Max β] [Bot α] [Bot β] [FunLike F α β]
  extends SupHomClass F α β : Prop where
  /-- A `SupBotHomClass` morphism preserves the bottom element. -/
  map_bot (f : F) : f ⊥ = ⊥

class InfTopHomClass (F α β : Type*) [Min α] [Min β] [Top α] [Top β] [FunLike F α β]
  extends InfHomClass F α β : Prop where
  /-- An `InfTopHomClass` morphism preserves the top element. -/
  map_top (f : F) : f ⊤ = ⊤

class LatticeHomClass (F α β : Type*) [Lattice α] [Lattice β] [FunLike F α β]
  extends SupHomClass F α β : Prop where
  /-- A `LatticeHomClass` morphism preserves infima. -/
  map_inf (f : F) (a b : α) : f (a ⊓ b) = f a ⊓ f b

class BoundedLatticeHomClass (F α β : Type*) [Lattice α] [Lattice β] [BoundedOrder α]
  [BoundedOrder β] [FunLike F α β] extends LatticeHomClass F α β : Prop where
  /-- A `BoundedLatticeHomClass` morphism preserves the top element. -/
  map_top (f : F) : f ⊤ = ⊤
  /-- A `BoundedLatticeHomClass` morphism preserves the bottom element. -/
  map_bot (f : F) : f ⊥ = ⊥

end

export SupHomClass (map_sup)

export InfHomClass (map_inf)

attribute [simp] map_top map_bot map_sup map_inf

section Hom

variable [FunLike F α β]

instance (priority := 100) SupHomClass.toOrderHomClass [SemilatticeSup α] [SemilatticeSup β]
    [SupHomClass F α β] : OrderHomClass F α β :=
  { ‹SupHomClass F α β› with
    map_rel := fun f a b h => by rw [← sup_eq_right, ← map_sup, sup_eq_right.2 h] }

instance (priority := 100) InfHomClass.toOrderHomClass [SemilatticeInf α] [SemilatticeInf β]
    [InfHomClass F α β] : OrderHomClass F α β :=
  { ‹InfHomClass F α β› with
    map_rel := fun f a b h => by rw [← inf_eq_left, ← map_inf, inf_eq_left.2 h] }

instance (priority := 100) SupBotHomClass.toBotHomClass [Max α] [Max β] [Bot α]
    [Bot β] [SupBotHomClass F α β] : BotHomClass F α β :=
  { ‹SupBotHomClass F α β› with }

instance (priority := 100) InfTopHomClass.toTopHomClass [Min α] [Min β] [Top α]
    [Top β] [InfTopHomClass F α β] : TopHomClass F α β :=
  { ‹InfTopHomClass F α β› with }

instance (priority := 100) LatticeHomClass.toInfHomClass [Lattice α] [Lattice β]
    [LatticeHomClass F α β] : InfHomClass F α β :=
  { ‹LatticeHomClass F α β› with }

instance (priority := 100) BoundedLatticeHomClass.toSupBotHomClass [Lattice α] [Lattice β]
    [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] :
    SupBotHomClass F α β :=
  { ‹BoundedLatticeHomClass F α β› with }

instance (priority := 100) BoundedLatticeHomClass.toInfTopHomClass [Lattice α] [Lattice β]
    [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] :
    InfTopHomClass F α β :=
  { ‹BoundedLatticeHomClass F α β› with }

instance (priority := 100) BoundedLatticeHomClass.toBoundedOrderHomClass [Lattice α]
    [Lattice β] [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] :
    BoundedOrderHomClass F α β :=

{ show OrderHomClass F α β from inferInstance, ‹BoundedLatticeHomClass F α β› with }

end Hom

section Equiv

variable [EquivLike F α β]

instance (priority := 100) OrderIsoClass.toSupHomClass [SemilatticeSup α] [SemilatticeSup β]
    [OrderIsoClass F α β] : SupHomClass F α β :=
  { show OrderHomClass F α β from inferInstance with
    map_sup := fun f a b =>
      eq_of_forall_ge_iff fun c => by simp only [← le_map_inv_iff, sup_le_iff] }

instance (priority := 100) OrderIsoClass.toInfHomClass [SemilatticeInf α] [SemilatticeInf β]
    [OrderIsoClass F α β] : InfHomClass F α β :=
  { show OrderHomClass F α β from inferInstance with
    map_inf := fun f a b =>
      eq_of_forall_le_iff fun c => by simp only [← map_inv_le_iff, le_inf_iff] }

instance (priority := 100) OrderIsoClass.toSupBotHomClass [SemilatticeSup α] [OrderBot α]
    [SemilatticeSup β] [OrderBot β] [OrderIsoClass F α β] : SupBotHomClass F α β :=
  { OrderIsoClass.toSupHomClass, OrderIsoClass.toBotHomClass with }

instance (priority := 100) OrderIsoClass.toInfTopHomClass [SemilatticeInf α] [OrderTop α]
    [SemilatticeInf β] [OrderTop β] [OrderIsoClass F α β] : InfTopHomClass F α β :=
  { OrderIsoClass.toInfHomClass, OrderIsoClass.toTopHomClass with }

instance (priority := 100) OrderIsoClass.toLatticeHomClass [Lattice α] [Lattice β]
    [OrderIsoClass F α β] : LatticeHomClass F α β :=
  { OrderIsoClass.toSupHomClass, OrderIsoClass.toInfHomClass with }

instance (priority := 100) OrderIsoClass.toBoundedLatticeHomClass [Lattice α] [Lattice β]
    [BoundedOrder α] [BoundedOrder β] [OrderIsoClass F α β] :
    BoundedLatticeHomClass F α β :=
  { OrderIsoClass.toLatticeHomClass, OrderIsoClass.toBoundedOrderHomClass with }

end Equiv

section OrderEmbedding

variable [FunLike F α β]

@[simps! apply]
def orderEmbeddingOfInjective [SemilatticeInf α] [SemilatticeInf β] (f : F) [InfHomClass F α β]
    (hf : Injective f) : α ↪o β :=
  OrderEmbedding.ofMapLEIff f (fun x y ↦ by
    refine ⟨fun h ↦ ?_, fun h ↦ OrderHomClass.mono f h⟩
    rwa [← inf_eq_left, ← hf.eq_iff, map_inf, inf_eq_left])

end OrderEmbedding

section BoundedLattice

variable [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β]

variable [FunLike F α β] [BoundedLatticeHomClass F α β]

variable (f : F) {a b : α}

theorem Disjoint.map (h : Disjoint a b) : Disjoint (f a) (f b) := by
  rw [disjoint_iff, ← map_inf, h.eq_bot, map_bot]

theorem Codisjoint.map (h : Codisjoint a b) : Codisjoint (f a) (f b) := by
  rw [codisjoint_iff, ← map_sup, h.eq_top, map_top]

theorem IsCompl.map (h : IsCompl a b) : IsCompl (f a) (f b) :=
  ⟨h.1.map _, h.2.map _⟩

end BoundedLattice

section BooleanAlgebra

variable [BooleanAlgebra α] [BooleanAlgebra β] [FunLike F α β] [BoundedLatticeHomClass F α β]

variable (f : F)

theorem map_compl' (a : α) : f aᶜ = (f a)ᶜ :=
  (isCompl_compl.map _).compl_eq.symm

theorem map_sdiff' (a b : α) : f (a \ b) = f a \ f b := by
  rw [sdiff_eq, sdiff_eq, map_inf, map_compl']

open scoped symmDiff in

theorem map_symmDiff' (a b : α) : f (a ∆ b) = f a ∆ f b := by
  rw [symmDiff, symmDiff, map_sup, map_sdiff', map_sdiff']

end BooleanAlgebra

variable [FunLike F α β]

instance [Max α] [Max β] [SupHomClass F α β] : CoeTC F (SupHom α β) :=
  ⟨fun f => ⟨f, map_sup f⟩⟩

instance [Min α] [Min β] [InfHomClass F α β] : CoeTC F (InfHom α β) :=
  ⟨fun f => ⟨f, map_inf f⟩⟩

instance [Max α] [Max β] [Bot α] [Bot β] [SupBotHomClass F α β] : CoeTC F (SupBotHom α β) :=
  ⟨fun f => ⟨f, map_bot f⟩⟩

instance [Min α] [Min β] [Top α] [Top β] [InfTopHomClass F α β] : CoeTC F (InfTopHom α β) :=
  ⟨fun f => ⟨f, map_top f⟩⟩

instance [Lattice α] [Lattice β] [LatticeHomClass F α β] : CoeTC F (LatticeHom α β) :=
  ⟨fun f =>
    { toFun := f
      map_sup' := map_sup f
      map_inf' := map_inf f }⟩

instance [Lattice α] [Lattice β] [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] :
    CoeTC F (BoundedLatticeHom α β) :=
  ⟨fun f =>
    { (f : LatticeHom α β) with
      toFun := f
      map_top' := map_top f
      map_bot' := map_bot f }⟩

/-! ### Supremum homomorphisms -/

namespace SupHom

variable [Max α]

section Sup

variable [Max β] [Max γ] [Max δ]

instance : FunLike (SupHom α β) α β where
  coe := SupHom.toFun
  coe_injective' f g h := by cases f; cases g; congr

instance : SupHomClass (SupHom α β) α β where
  map_sup := SupHom.map_sup'

@[ext]
theorem ext {f g : SupHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

protected def copy (f : SupHom α β) (f' : α → β) (h : f' = f) : SupHom α β where
  toFun := f'
  map_sup' := h.symm ▸ f.map_sup'

theorem copy_eq (f : SupHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

protected def id : SupHom α α :=
  ⟨id, fun _ _ => rfl⟩

instance : Inhabited (SupHom α α) :=
  ⟨SupHom.id α⟩

variable {α}

def comp (f : SupHom β γ) (g : SupHom α β) : SupHom α γ where
  toFun := f ∘ g
  map_sup' a b := by rw [comp_apply, map_sup, map_sup]; rfl

@[simp]
theorem comp_apply (f : SupHom β γ) (g : SupHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem cancel_right {g₁ g₂ : SupHom β γ} {f : SupHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => SupHom.ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[simp]
theorem cancel_left {g : SupHom β γ} {f₁ f₂ : SupHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => SupHom.ext fun a => hg <| by rw [← SupHom.comp_apply, h, SupHom.comp_apply],
    congr_arg _⟩

end Sup

variable (α) [SemilatticeSup β]

def const (b : β) : SupHom α β := ⟨fun _ ↦ b, fun _ _ ↦ (sup_idem _).symm⟩

variable {α}

instance : Max (SupHom α β) :=
  ⟨fun f g =>
    ⟨f ⊔ g, fun a b => by
      rw [Pi.sup_apply, map_sup, map_sup]
      exact sup_sup_sup_comm _ _ _ _⟩⟩

instance : SemilatticeSup (SupHom α β) :=
  (DFunLike.coe_injective.semilatticeSup _) fun _ _ => rfl

instance [Bot β] : Bot (SupHom α β) :=
  ⟨SupHom.const α ⊥⟩

instance [Top β] : Top (SupHom α β) :=
  ⟨SupHom.const α ⊤⟩

instance [OrderBot β] : OrderBot (SupHom α β) :=
  OrderBot.lift ((↑) : _ → α → β) (fun _ _ => id) rfl

instance [OrderTop β] : OrderTop (SupHom α β) :=
  OrderTop.lift ((↑) : _ → α → β) (fun _ _ => id) rfl

instance [BoundedOrder β] : BoundedOrder (SupHom α β) :=
  BoundedOrder.lift ((↑) : _ → α → β) (fun _ _ => id) rfl rfl

@[simp]
theorem coe_bot [Bot β] : ⇑(⊥ : SupHom α β) = ⊥ :=
  rfl

@[simp]
theorem coe_top [Top β] : ⇑(⊤ : SupHom α β) = ⊤ :=
  rfl

@[simp]
theorem sup_apply (f g : SupHom α β) (a : α) : (f ⊔ g) a = f a ⊔ g a :=
  rfl

def subtypeVal {P : β → Prop}
    (Psup : ∀ ⦃x y : β⦄, P x → P y → P (x ⊔ y)) :
    letI := Subtype.semilatticeSup Psup
    SupHom {x : β // P x} β :=
  letI := Subtype.semilatticeSup Psup
  .mk Subtype.val (by simp)

end SupHom

/-! ### Infimum homomorphisms -/

namespace InfHom

variable [Min α]

section Inf

variable [Min β] [Min γ] [Min δ]

instance : FunLike (InfHom α β) α β where
  coe := InfHom.toFun
  coe_injective' f g h := by cases f; cases g; congr

instance : InfHomClass (InfHom α β) α β where
  map_inf := InfHom.map_inf'

@[ext]
theorem ext {f g : InfHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

protected def copy (f : InfHom α β) (f' : α → β) (h : f' = f) : InfHom α β where
  toFun := f'
  map_inf' := h.symm ▸ f.map_inf'

theorem copy_eq (f : InfHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

protected def id : InfHom α α :=
  ⟨id, fun _ _ => rfl⟩

instance : Inhabited (InfHom α α) :=
  ⟨InfHom.id α⟩

variable {α}

def comp (f : InfHom β γ) (g : InfHom α β) : InfHom α γ where
  toFun := f ∘ g
  map_inf' a b := by rw [comp_apply, map_inf, map_inf]; rfl

@[simp]
theorem comp_apply (f : InfHom β γ) (g : InfHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem cancel_right {g₁ g₂ : InfHom β γ} {f : InfHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => InfHom.ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[simp]
theorem cancel_left {g : InfHom β γ} {f₁ f₂ : InfHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => InfHom.ext fun a => hg <| by rw [← InfHom.comp_apply, h, InfHom.comp_apply],
    congr_arg _⟩

end Inf

variable (α) [SemilatticeInf β]

def const (b : β) : InfHom α β := ⟨fun _ ↦ b, fun _ _ ↦ (inf_idem _).symm⟩

variable {α}

instance : Min (InfHom α β) :=
  ⟨fun f g =>
    ⟨f ⊓ g, fun a b => by
      rw [Pi.inf_apply, map_inf, map_inf]
      exact inf_inf_inf_comm _ _ _ _⟩⟩

instance : SemilatticeInf (InfHom α β) :=
  (DFunLike.coe_injective.semilatticeInf _) fun _ _ => rfl

instance [Bot β] : Bot (InfHom α β) :=
  ⟨InfHom.const α ⊥⟩

instance [Top β] : Top (InfHom α β) :=
  ⟨InfHom.const α ⊤⟩

instance [OrderBot β] : OrderBot (InfHom α β) :=
  OrderBot.lift ((↑) : _ → α → β) (fun _ _ => id) rfl

instance [OrderTop β] : OrderTop (InfHom α β) :=
  OrderTop.lift ((↑) : _ → α → β) (fun _ _ => id) rfl

instance [BoundedOrder β] : BoundedOrder (InfHom α β) :=
  BoundedOrder.lift ((↑) : _ → α → β) (fun _ _ => id) rfl rfl

@[simp]
theorem coe_inf (f g : InfHom α β) : DFunLike.coe (f ⊓ g) = f ⊓ g :=
  rfl

@[simp]
theorem coe_bot [Bot β] : ⇑(⊥ : InfHom α β) = ⊥ :=
  rfl

@[simp]
theorem coe_top [Top β] : ⇑(⊤ : InfHom α β) = ⊤ :=
  rfl

@[simp]
theorem inf_apply (f g : InfHom α β) (a : α) : (f ⊓ g) a = f a ⊓ g a :=
  rfl

def subtypeVal {P : β → Prop}
    (Pinf : ∀ ⦃x y : β⦄, P x → P y → P (x ⊓ y)) :
    letI := Subtype.semilatticeInf Pinf
    InfHom {x : β // P x} β :=
  letI := Subtype.semilatticeInf Pinf
  .mk Subtype.val (by simp)

end InfHom

/-! ### Finitary supremum homomorphisms -/

namespace SupBotHom

variable [Max α] [Bot α]

section Sup

variable [Max β] [Bot β] [Max γ] [Bot γ] [Max δ] [Bot δ]

def toBotHom (f : SupBotHom α β) : BotHom α β :=
  { f with }

instance : FunLike (SupBotHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

instance : SupBotHomClass (SupBotHom α β) α β where
  map_sup f := f.map_sup'
  map_bot f := f.map_bot'

@[ext]
theorem ext {f g : SupBotHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

protected def copy (f : SupBotHom α β) (f' : α → β) (h : f' = f) : SupBotHom α β :=
  { f.toBotHom.copy f' h with toSupHom := f.toSupHom.copy f' h }

theorem copy_eq (f : SupBotHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

@[simps]
protected def id : SupBotHom α α :=
  ⟨SupHom.id α, rfl⟩

instance : Inhabited (SupBotHom α α) :=
  ⟨SupBotHom.id α⟩

variable {α}

def comp (f : SupBotHom β γ) (g : SupBotHom α β) : SupBotHom α γ :=
  { f.toSupHom.comp g.toSupHom, f.toBotHom.comp g.toBotHom with }

@[simp]
theorem comp_apply (f : SupBotHom β γ) (g : SupBotHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem cancel_right {g₁ g₂ : SupBotHom β γ} {f : SupBotHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[simp]
theorem cancel_left {g : SupBotHom β γ} {f₁ f₂ : SupBotHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => SupBotHom.ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end Sup

variable [SemilatticeSup β] [OrderBot β]

instance : Max (SupBotHom α β) :=
  ⟨fun f g => { f.toBotHom ⊔ g.toBotHom with toSupHom := f.toSupHom ⊔ g.toSupHom }⟩

instance : SemilatticeSup (SupBotHom α β) :=
  (DFunLike.coe_injective.semilatticeSup _) fun _ _ => rfl

instance : OrderBot (SupBotHom α β) where
  bot := ⟨⊥, rfl⟩
  bot_le _ _ := bot_le

@[simp]
theorem coe_bot : ⇑(⊥ : SupBotHom α β) = ⊥ :=
  rfl

@[simp]
theorem sup_apply (f g : SupBotHom α β) (a : α) : (f ⊔ g) a = f a ⊔ g a :=
  rfl

def subtypeVal {P : β → Prop}
    (Pbot : P ⊥) (Psup : ∀ ⦃x y : β⦄, P x → P y → P (x ⊔ y)) :
    letI := Subtype.orderBot Pbot
    letI := Subtype.semilatticeSup Psup
    SupBotHom {x : β // P x} β :=
  letI := Subtype.orderBot Pbot
  letI := Subtype.semilatticeSup Psup
  .mk (SupHom.subtypeVal Psup) (by simp [Subtype.coe_bot Pbot])

end SupBotHom

/-! ### Finitary infimum homomorphisms -/

namespace InfTopHom

variable [Min α] [Top α]

section Inf

variable [Min β] [Top β] [Min γ] [Top γ] [Min δ] [Top δ]

def toTopHom (f : InfTopHom α β) : TopHom α β :=
  { f with }

instance : FunLike (InfTopHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

instance : InfTopHomClass (InfTopHom α β) α β where
  map_inf f := f.map_inf'
  map_top f := f.map_top'

@[ext]
theorem ext {f g : InfTopHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

protected def copy (f : InfTopHom α β) (f' : α → β) (h : f' = f) : InfTopHom α β :=
  { f.toTopHom.copy f' h with toInfHom := f.toInfHom.copy f' h }

theorem copy_eq (f : InfTopHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

@[simps]
protected def id : InfTopHom α α :=
  ⟨InfHom.id α, rfl⟩

instance : Inhabited (InfTopHom α α) :=
  ⟨InfTopHom.id α⟩

variable {α}

def comp (f : InfTopHom β γ) (g : InfTopHom α β) : InfTopHom α γ :=
  { f.toInfHom.comp g.toInfHom, f.toTopHom.comp g.toTopHom with }

@[simp]
theorem comp_apply (f : InfTopHom β γ) (g : InfTopHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem cancel_right {g₁ g₂ : InfTopHom β γ} {f : InfTopHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[simp]
theorem cancel_left {g : InfTopHom β γ} {f₁ f₂ : InfTopHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => InfTopHom.ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end Inf

variable [SemilatticeInf β] [OrderTop β]

instance : Min (InfTopHom α β) :=
  ⟨fun f g => { f.toTopHom ⊓ g.toTopHom with toInfHom := f.toInfHom ⊓ g.toInfHom }⟩

instance : SemilatticeInf (InfTopHom α β) :=
  (DFunLike.coe_injective.semilatticeInf _) fun _ _ => rfl

instance : OrderTop (InfTopHom α β) where
  top := ⟨⊤, rfl⟩
  le_top _ _ := le_top

@[simp]
theorem coe_inf (f g : InfTopHom α β) : DFunLike.coe (f ⊓ g) = f ⊓ g :=
  rfl

@[simp]
theorem coe_top : ⇑(⊤ : InfTopHom α β) = ⊤ :=
  rfl

@[simp]
theorem inf_apply (f g : InfTopHom α β) (a : α) : (f ⊓ g) a = f a ⊓ g a :=
  rfl

def subtypeVal {P : β → Prop}
    (Ptop : P ⊤) (Pinf : ∀ ⦃x y : β⦄, P x → P y → P (x ⊓ y)) :
    letI := Subtype.orderTop Ptop
    letI := Subtype.semilatticeInf Pinf
    InfTopHom {x : β // P x} β :=
  letI := Subtype.orderTop Ptop
  letI := Subtype.semilatticeInf Pinf
  .mk (InfHom.subtypeVal Pinf) (by simp [Subtype.coe_top Ptop])

end InfTopHom

/-! ### Lattice homomorphisms -/

namespace LatticeHom

variable [Lattice α] [Lattice β] [Lattice γ] [Lattice δ]

def toInfHom (f : LatticeHom α β) : InfHom α β :=
  { f with }

instance : FunLike (LatticeHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr

instance : LatticeHomClass (LatticeHom α β) α β where
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'

@[ext]
theorem ext {f g : LatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

protected def copy (f : LatticeHom α β) (f' : α → β) (h : f' = f) : LatticeHom α β :=
  { f.toSupHom.copy f' h, f.toInfHom.copy f' h with }

theorem copy_eq (f : LatticeHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

protected def id : LatticeHom α α where
  toFun := id
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

instance : Inhabited (LatticeHom α α) :=
  ⟨LatticeHom.id α⟩

variable {α}

def comp (f : LatticeHom β γ) (g : LatticeHom α β) : LatticeHom α γ :=
  { f.toSupHom.comp g.toSupHom, f.toInfHom.comp g.toInfHom with }

@[simp]
theorem comp_apply (f : LatticeHom β γ) (g : LatticeHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem cancel_right {g₁ g₂ : LatticeHom β γ} {f : LatticeHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => LatticeHom.ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[simp]
theorem cancel_left {g : LatticeHom β γ} {f₁ f₂ : LatticeHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => LatticeHom.ext fun a => hg <| by rw [← LatticeHom.comp_apply, h, LatticeHom.comp_apply],
    congr_arg _⟩

def subtypeVal {P : β → Prop}
    (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)) :
    letI := Subtype.lattice Psup Pinf
    LatticeHom {x : β // P x} β :=
  letI := Subtype.lattice Psup Pinf
  .mk (SupHom.subtypeVal Psup) (by simp [Subtype.coe_inf Pinf])

end LatticeHom

namespace OrderHomClass

variable (α β)

variable [LinearOrder α] [Lattice β] [OrderHomClass F α β]

instance (priority := 100) toLatticeHomClass : LatticeHomClass F α β :=
  { ‹OrderHomClass F α β› with
    map_sup := fun f a b => by
      obtain h | h := le_total a b
      · rw [sup_eq_right.2 h, sup_eq_right.2 (OrderHomClass.mono f h : f a ≤ f b)]
      · rw [sup_eq_left.2 h, sup_eq_left.2 (OrderHomClass.mono f h : f b ≤ f a)]
    map_inf := fun f a b => by
      obtain h | h := le_total a b
      · rw [inf_eq_left.2 h, inf_eq_left.2 (OrderHomClass.mono f h : f a ≤ f b)]
      · rw [inf_eq_right.2 h, inf_eq_right.2 (OrderHomClass.mono f h : f b ≤ f a)] }

def toLatticeHom (f : F) : LatticeHom α β := f

end OrderHomClass

/-! ### Bounded lattice homomorphisms -/

namespace BoundedLatticeHom

variable [Lattice α] [Lattice β] [Lattice γ] [Lattice δ] [BoundedOrder α] [BoundedOrder β]
  [BoundedOrder γ] [BoundedOrder δ]

def toSupBotHom (f : BoundedLatticeHom α β) : SupBotHom α β :=
  { f with }

def toInfTopHom (f : BoundedLatticeHom α β) : InfTopHom α β :=
  { f with }

def toBoundedOrderHom (f : BoundedLatticeHom α β) : BoundedOrderHom α β :=
  { f, (f.toLatticeHom : α →o β) with }

instance instFunLike : FunLike (BoundedLatticeHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr

instance instBoundedLatticeHomClass : BoundedLatticeHomClass (BoundedLatticeHom α β) α β where
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'
  map_bot f := f.map_bot'

@[ext]
theorem ext {f g : BoundedLatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

protected def copy (f : BoundedLatticeHom α β) (f' : α → β) (h : f' = f) : BoundedLatticeHom α β :=
  { f.toLatticeHom.copy f' h, f.toBoundedOrderHom.copy f' h with }

theorem copy_eq (f : BoundedLatticeHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

protected def id : BoundedLatticeHom α α :=
  { LatticeHom.id α, BoundedOrderHom.id α with }

instance : Inhabited (BoundedLatticeHom α α) :=
  ⟨BoundedLatticeHom.id α⟩

variable {α}

def comp (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) : BoundedLatticeHom α γ :=
  { f.toLatticeHom.comp g.toLatticeHom, f.toBoundedOrderHom.comp g.toBoundedOrderHom with }

@[simp]
theorem comp_apply (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) (a : α) :
    (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem cancel_right {g₁ g₂ : BoundedLatticeHom β γ} {f : BoundedLatticeHom α β}
    (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => BoundedLatticeHom.ext <| hf.forall.2 <| DFunLike.ext_iff.1 h,
    fun h => congr_arg₂ _ h rfl⟩

@[simp]
theorem cancel_left {g : BoundedLatticeHom β γ} {f₁ f₂ : BoundedLatticeHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

def subtypeVal {P : β → Prop} (Pbot : P ⊥) (Ptop : P ⊤)
    (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)) :
    letI := Subtype.lattice Psup Pinf
    letI := Subtype.boundedOrder Pbot Ptop
    BoundedLatticeHom {x : β // P x} β :=
  letI := Subtype.lattice Psup Pinf
  letI := Subtype.boundedOrder Pbot Ptop
  .mk (.subtypeVal Psup Pinf) (by simp [Subtype.coe_top Ptop]) (by simp [Subtype.coe_bot Pbot])

end BoundedLatticeHom

/-! ### Dual homs -/

namespace SupHom

variable [Max α] [Max β] [Max γ]

end SupHom

namespace InfHom

variable [Min α] [Min β] [Min γ]

end InfHom

namespace SupBotHom

variable [Max α] [Bot α] [Max β] [Bot β] [Max γ] [Bot γ]

end SupBotHom

namespace InfTopHom

variable [Min α] [Top α] [Min β] [Top β] [Min γ] [Top γ]

end InfTopHom

namespace LatticeHom

variable [Lattice α] [Lattice β] [Lattice γ]

end LatticeHom

namespace BoundedLatticeHom

variable [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β] [Lattice γ] [BoundedOrder γ]

end BoundedLatticeHom

/-! ### Prod -/

namespace LatticeHom

variable [Lattice α] [Lattice β]

end LatticeHom

/-! ### Pi -/

namespace Pi

variable {ι : Type*} {α : ι → Type*} [∀ i, Lattice (α i)]

end Pi

/-! ### `WithTop`, `WithBot` -/

namespace SupHom

variable [SemilatticeSup α] [SemilatticeSup β] [SemilatticeSup γ]

@[simps]
protected def withTop (f : SupHom α β) : SupHom (WithTop α) (WithTop β) where
  -- Porting note: this was `Option.map f`
  toFun := WithTop.map f
  map_sup' a b :=
    match a, b with
    | ⊤, ⊤ => rfl
    | ⊤, (b : α) => rfl
    | (a : α), ⊤ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_sup' _ _)

@[simp]
theorem withTop_id : (SupHom.id α).withTop = SupHom.id _ := DFunLike.coe_injective Option.map_id

@[simp]
theorem withTop_comp (f : SupHom β γ) (g : SupHom α β) :
    (f.comp g).withTop = f.withTop.comp g.withTop :=
  DFunLike.coe_injective <| Eq.symm <| Option.map_comp_map _ _

@[simps]
protected def withBot (f : SupHom α β) : SupBotHom (WithBot α) (WithBot β) where
  toFun := Option.map f
  map_sup' a b :=
    match a, b with
    | ⊥, ⊥ => rfl
    | ⊥, (b : α) => rfl
    | (a : α), ⊥ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_sup' _ _)
  map_bot' := rfl

@[simp]
theorem withBot_id : (SupHom.id α).withBot = SupBotHom.id _ := DFunLike.coe_injective Option.map_id

@[simp]
theorem withBot_comp (f : SupHom β γ) (g : SupHom α β) :
    (f.comp g).withBot = f.withBot.comp g.withBot :=
  DFunLike.coe_injective <| Eq.symm <| Option.map_comp_map _ _

end SupHom

namespace InfHom

variable [SemilatticeInf α] [SemilatticeInf β] [SemilatticeInf γ]

@[simps]
protected def withTop (f : InfHom α β) : InfTopHom (WithTop α) (WithTop β) where
  toFun := Option.map f
  map_inf' a b :=
    match a, b with
    | ⊤, ⊤ => rfl
    | ⊤, (b : α) => rfl
    | (a : α), ⊤ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_inf' _ _)
  map_top' := rfl

@[simp]
theorem withTop_id : (InfHom.id α).withTop = InfTopHom.id _ := DFunLike.coe_injective Option.map_id

@[simp]
theorem withTop_comp (f : InfHom β γ) (g : InfHom α β) :
    (f.comp g).withTop = f.withTop.comp g.withTop :=
  DFunLike.coe_injective <| Eq.symm <| Option.map_comp_map _ _

@[simps]
protected def withBot (f : InfHom α β) : InfHom (WithBot α) (WithBot β) where
  toFun := Option.map f
  map_inf' a b :=
    match a, b with
    | ⊥, ⊥ => rfl
    | ⊥, (b : α) => rfl
    | (a : α), ⊥ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_inf' _ _)

@[simp]
theorem withBot_id : (InfHom.id α).withBot = InfHom.id _ := DFunLike.coe_injective Option.map_id

@[simp]
theorem withBot_comp (f : InfHom β γ) (g : InfHom α β) :
    (f.comp g).withBot = f.withBot.comp g.withBot :=
  DFunLike.coe_injective <| Eq.symm <| Option.map_comp_map _ _

end InfHom

namespace LatticeHom

variable [Lattice α] [Lattice β] [Lattice γ]

@[simps]
protected def withTop (f : LatticeHom α β) : LatticeHom (WithTop α) (WithTop β) :=
  { f.toInfHom.withTop with toSupHom := f.toSupHom.withTop }

@[simp]
theorem withTop_id : (LatticeHom.id α).withTop = LatticeHom.id _ :=
  DFunLike.coe_injective Option.map_id

@[simp]
theorem withTop_comp (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g).withTop = f.withTop.comp g.withTop :=
  DFunLike.coe_injective <| Eq.symm <| Option.map_comp_map _ _

@[simps]
protected def withBot (f : LatticeHom α β) : LatticeHom (WithBot α) (WithBot β) :=
  { f.toInfHom.withBot with toSupHom := f.toSupHom.withBot }

@[simp]
theorem withBot_id : (LatticeHom.id α).withBot = LatticeHom.id _ :=
  DFunLike.coe_injective Option.map_id

@[simp]
theorem withBot_comp (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g).withBot = f.withBot.comp g.withBot :=
  DFunLike.coe_injective <| Eq.symm <| Option.map_comp_map _ _

@[simps]
def withTopWithBot (f : LatticeHom α β) :
    BoundedLatticeHom (WithTop <| WithBot α) (WithTop <| WithBot β) :=
  ⟨f.withBot.withTop, rfl, rfl⟩

@[simp]
theorem withTopWithBot_id : (LatticeHom.id α).withTopWithBot = BoundedLatticeHom.id _ :=
  DFunLike.coe_injective <| by
    refine (congr_arg Option.map ?_).trans Option.map_id
    rw [withBot_id]
    rfl

@[simp]
theorem withTopWithBot_comp (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g).withTopWithBot = f.withTopWithBot.comp g.withTopWithBot := by
  ext; simp

end LatticeHom

set_option linter.style.longFile 1800
