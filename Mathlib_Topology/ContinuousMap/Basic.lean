/-
Extracted from Topology/ContinuousMap/Basic.lean
Genuine: 45 | Conflates: 0 | Dissolved: 0 | Infrastructure: 18
-/
import Origin.Core
import Mathlib.Data.Set.UnionLift
import Mathlib.Topology.ContinuousMap.Defs
import Mathlib.Topology.Homeomorph

noncomputable section

/-!
# Continuous bundled maps

In this file we define the type `ContinuousMap` of continuous bundled maps.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.
-/

open Function Topology

section ContinuousMapClass

variable {F α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [FunLike F α β]

variable [ContinuousMapClass F α β]

theorem map_continuousAt (f : F) (a : α) : ContinuousAt f a :=
  (map_continuous f).continuousAt

theorem map_continuousWithinAt (f : F) (s : Set α) (a : α) : ContinuousWithinAt f s a :=
  (map_continuous f).continuousWithinAt

end ContinuousMapClass

/-! ### Continuous maps -/

namespace ContinuousMap

variable {α β γ δ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  [TopologicalSpace δ]

variable {f g : C(α, β)}

protected theorem continuousAt (f : C(α, β)) (x : α) : ContinuousAt f x :=
  map_continuousAt f x

theorem map_specializes (f : C(α, β)) {x y : α} (h : x ⤳ y) : f x ⤳ f y :=
  h.map f.2

section

variable (α β)

@[simps]
def equivFnOfDiscrete [DiscreteTopology α] : C(α, β) ≃ (α → β) :=
  ⟨fun f => f,
    fun f => ⟨f, continuous_of_discreteTopology⟩,
    fun _ => by ext; rfl,
    fun _ => by ext; rfl⟩

end

variable (α)

protected def id : C(α, α) where
  toFun := id

@[simp]
theorem coe_id : ⇑(ContinuousMap.id α) = id :=
  rfl

def const (b : β) : C(α, β) where
  toFun := fun _ : α => b

@[simp]
theorem coe_const (b : β) : ⇑(const α b) = Function.const α b :=
  rfl

@[simps (config := .asFn)]
def constPi : C(β, α → β) where
  toFun b := Function.const α b

instance [Inhabited β] : Inhabited C(α, β) :=
  ⟨const α default⟩

variable {α}

@[simp]
theorem id_apply (a : α) : ContinuousMap.id α a = a :=
  rfl

@[simp]
theorem const_apply (b : β) (a : α) : const α b a = b :=
  rfl

def comp (f : C(β, γ)) (g : C(α, β)) : C(α, γ) where
  toFun := f ∘ g

@[simp]
theorem coe_comp (f : C(β, γ)) (g : C(α, β)) : ⇑(comp f g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : C(β, γ)) (g : C(α, β)) (a : α) : comp f g a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : C(γ, δ)) (g : C(β, γ)) (h : C(α, β)) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem id_comp (f : C(α, β)) : (ContinuousMap.id _).comp f = f :=
  ext fun _ => rfl

@[simp]
theorem comp_id (f : C(α, β)) : f.comp (ContinuousMap.id _) = f :=
  ext fun _ => rfl

@[simp]
theorem const_comp (c : γ) (f : C(α, β)) : (const β c).comp f = const α c :=
  ext fun _ => rfl

@[simp]
theorem comp_const (f : C(β, γ)) (b : β) : f.comp (const α b) = const α (f b) :=
  ext fun _ => rfl

@[simp]
theorem cancel_right {f₁ f₂ : C(β, γ)} {g : C(α, β)} (hg : Surjective g) :
    f₁.comp g = f₂.comp g ↔ f₁ = f₂ :=
  ⟨fun h => ext <| hg.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (ContinuousMap.comp · g)⟩

@[simp]
theorem cancel_left {f : C(β, γ)} {g₁ g₂ : C(α, β)} (hf : Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
  ⟨fun h => ext fun a => hf <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

instance [Nonempty α] [Nontrivial β] : Nontrivial C(α, β) :=
  ⟨let ⟨b₁, b₂, hb⟩ := exists_pair_ne β
  ⟨const _ b₁, const _ b₂, fun h => hb <| DFunLike.congr_fun h <| Classical.arbitrary α⟩⟩

section Prod

variable {α₁ α₂ β₁ β₂ : Type*} [TopologicalSpace α₁] [TopologicalSpace α₂] [TopologicalSpace β₁]
  [TopologicalSpace β₂]

@[simps (config := .asFn)]
def fst : C(α × β, α) where
  toFun := Prod.fst

@[simps (config := .asFn)]
def snd : C(α × β, β) where
  toFun := Prod.snd

def prodMk (f : C(α, β₁)) (g : C(α, β₂)) : C(α, β₁ × β₂) where
  toFun x := (f x, g x)

@[simps]
def prodMap (f : C(α₁, α₂)) (g : C(β₁, β₂)) : C(α₁ × β₁, α₂ × β₂) where
  toFun := Prod.map f g

@[simp]
theorem prod_eval (f : C(α, β₁)) (g : C(α, β₂)) (a : α) : (prodMk f g) a = (f a, g a) :=
  rfl

@[simps!]
def prodSwap : C(α × β, β × α) := .prodMk .snd .fst

end Prod

section Sigma

variable {I A : Type*} {X : I → Type*} [TopologicalSpace A] [∀ i, TopologicalSpace (X i)]

@[simps apply]
def sigmaMk (i : I) : C(X i, Σ i, X i) where
  toFun := Sigma.mk i

@[simps]
def sigma (f : ∀ i, C(X i, A)) : C((Σ i, X i), A) where
  toFun ig := f ig.fst ig.snd

variable (A X) in

@[simps]
def sigmaEquiv : (∀ i, C(X i, A)) ≃ C((Σ i, X i), A) where
  toFun := sigma
  invFun f i := f.comp (sigmaMk i)
  left_inv := by intro; ext; simp
  right_inv := by intro; ext; simp

end Sigma

section Pi

variable {I A : Type*} {X Y : I → Type*} [TopologicalSpace A] [∀ i, TopologicalSpace (X i)]
  [∀ i, TopologicalSpace (Y i)]

def pi (f : ∀ i, C(A, X i)) : C(A, ∀ i, X i) where
  toFun (a : A) (i : I) := f i a

@[simp]
theorem pi_eval (f : ∀ i, C(A, X i)) (a : A) : (pi f) a = fun i : I => (f i) a :=
  rfl

@[simps (config := .asFn)]
def eval (i : I) : C(∀ j, X j, X i) where
  toFun := Function.eval i

variable (A X) in

@[simps]
def piEquiv : (∀ i, C(A, X i)) ≃ C(A, ∀ i, X i) where
  toFun := pi
  invFun f i := (eval i).comp f
  left_inv := by intro; ext; simp [pi]
  right_inv := by intro; ext; simp [pi]

@[simps!]
def piMap (f : ∀ i, C(X i, Y i)) : C((i : I) → X i, (i : I) → Y i) :=
  .pi fun i ↦ (f i).comp (eval i)

def precomp {ι : Type*} (φ : ι → I) : C((i : I) → X i, (i : ι) → X (φ i)) :=
  ⟨_, Pi.continuous_precomp' φ⟩

end Pi

section Restrict

variable (s : Set α)

def restrict (f : C(α, β)) : C(s, β) where
  toFun := f ∘ ((↑) : s → α)

@[simp]
theorem coe_restrict (f : C(α, β)) : ⇑(f.restrict s) = f ∘ ((↑) : s → α) :=
  rfl

@[simp]
theorem restrict_apply (f : C(α, β)) (s : Set α) (x : s) : f.restrict s x = f x :=
  rfl

@[simp]
theorem restrict_apply_mk (f : C(α, β)) (s : Set α) (x : α) (hx : x ∈ s) :
    f.restrict s ⟨x, hx⟩ = f x :=
  rfl

theorem injective_restrict [T2Space β] {s : Set α} (hs : Dense s) :
    Injective (restrict s : C(α, β) → C(s, β)) := fun f g h ↦
  DFunLike.ext' <| (map_continuous f).ext_on hs (map_continuous g) <|
    Set.restrict_eq_restrict_iff.1 <| congr_arg DFunLike.coe h

@[simps]
def restrictPreimage (f : C(α, β)) (s : Set β) : C(f ⁻¹' s, s) :=
  ⟨s.restrictPreimage f, continuous_iff_continuousAt.mpr fun _ ↦
    (map_continuousAt f _).restrictPreimage⟩

end Restrict

section Gluing

variable {ι : Type*} (S : ι → Set α) (φ : ∀ i : ι, C(S i, β))
  (hφ : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩)
  (hS : ∀ x : α, ∃ i, S i ∈ 𝓝 x)

noncomputable def liftCover : C(α, β) :=
  haveI H : ⋃ i, S i = Set.univ :=
    Set.iUnion_eq_univ_iff.2 fun x ↦ (hS x).imp fun _ ↦ mem_of_mem_nhds
  mk (Set.liftCover S (fun i ↦ φ i) hφ H) <| continuous_of_cover_nhds hS fun i ↦ by
    rw [continuousOn_iff_continuous_restrict]
    simpa (config := { unfoldPartialApp := true }) only [Set.restrict, Set.liftCover_coe]
      using map_continuous (φ i)

variable {S φ hφ hS}

@[simp]
theorem liftCover_coe {i : ι} (x : S i) : liftCover S φ hφ hS x = φ i x := by
  rw [liftCover, coe_mk, Set.liftCover_coe _]

@[simp]
theorem liftCover_restrict {i : ι} : (liftCover S φ hφ hS).restrict (S i) = φ i := by
  ext
  simp only [coe_restrict, Function.comp_apply, liftCover_coe]

variable (A : Set (Set α)) (F : ∀ s ∈ A, C(s, β))
  (hF : ∀ (s) (hs : s ∈ A) (t) (ht : t ∈ A) (x : α) (hxi : x ∈ s) (hxj : x ∈ t),
    F s hs ⟨x, hxi⟩ = F t ht ⟨x, hxj⟩)
  (hA : ∀ x : α, ∃ i ∈ A, i ∈ 𝓝 x)

noncomputable def liftCover' : C(α, β) := by
  let S : A → Set α := (↑)
  let F : ∀ i : A, C(i, β) := fun i => F i i.prop
  refine liftCover S F (fun i j => hF i i.prop j j.prop) ?_
  intro x
  obtain ⟨s, hs, hsx⟩ := hA x
  exact ⟨⟨s, hs⟩, hsx⟩

variable {A F hF hA}

@[simp]
theorem liftCover_coe' {s : Set α} {hs : s ∈ A} (x : s) : liftCover' A F hF hA x = F s hs x :=
  let x' : ((↑) : A → Set α) ⟨s, hs⟩ := x
  by delta liftCover'; exact liftCover_coe x'

@[simp]
theorem liftCover_restrict' {s : Set α} {hs : s ∈ A} :
    (liftCover' A F hF hA).restrict s = F s hs := ext <| liftCover_coe' (hF := hF) (hA := hA)

end Gluing

def inclusion {s t : Set α} (h : s ⊆ t) : C(s, t) where
  toFun := Set.inclusion h
  continuous_toFun := continuous_inclusion h

end ContinuousMap

section Lift

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : C(X, Y)}

@[simps!]
def Function.RightInverse.homeomorph {f' : C(Y, X)} (hf : Function.RightInverse f' f) :
    Quotient (Setoid.ker f) ≃ₜ Y where
  toEquiv := Setoid.quotientKerEquivOfRightInverse _ _ hf
  continuous_toFun := isQuotientMap_quot_mk.continuous_iff.mpr (map_continuous f)
  continuous_invFun := continuous_quotient_mk'.comp (map_continuous f')

namespace Topology.IsQuotientMap

@[simps!]
noncomputable def homeomorph (hf : IsQuotientMap f) : Quotient (Setoid.ker f) ≃ₜ Y where
  toEquiv := Setoid.quotientKerEquivOfSurjective _ hf.surjective
  continuous_toFun := isQuotientMap_quot_mk.continuous_iff.mpr hf.continuous
  continuous_invFun := by
    rw [hf.continuous_iff]
    convert continuous_quotient_mk'
    ext
    simp only [Equiv.invFun_as_coe, Function.comp_apply,
      (Setoid.quotientKerEquivOfSurjective f hf.surjective).symm_apply_eq]
    rfl

variable (hf : IsQuotientMap f) (g : C(X, Z)) (h : Function.FactorsThrough g f)

@[simps]
noncomputable def lift : C(Y, Z) where
  toFun := ((fun i ↦ Quotient.liftOn' i g (fun _ _ (hab : f _ = f _) ↦ h hab)) :
    Quotient (Setoid.ker f) → Z) ∘ hf.homeomorph.symm
  continuous_toFun := Continuous.comp (continuous_quot_lift _ g.2) (Homeomorph.continuous _)

@[simp]
theorem lift_comp : (hf.lift g h).comp f = g := by
  ext
  simpa using h (Function.rightInverse_surjInv _ _)

@[simps]
noncomputable def liftEquiv : { g : C(X, Z) // Function.FactorsThrough g f} ≃ C(Y, Z) where
  toFun g := hf.lift g g.prop
  invFun g := ⟨g.comp f, fun _ _ h ↦ by simp only [ContinuousMap.comp_apply]; rw [h]⟩
  left_inv := by intro; simp
  right_inv := by
    intro g
    ext a
    simpa using congrArg g (Function.rightInverse_surjInv hf.surjective a)

end Topology.IsQuotientMap

end Lift

namespace Homeomorph

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

variable (f : α ≃ₜ β) (g : β ≃ₜ γ)

instance instContinuousMapClass : ContinuousMapClass (α ≃ₜ β) α β where
  map_continuous f := f.continuous_toFun

@[simps, deprecated _root_.toContinuousMap (since := "2024-10-12")]
protected def toContinuousMap (e : α ≃ₜ β) : C(α, β) :=
  ⟨e, e.continuous_toFun⟩

attribute [deprecated ContinuousMap.coe_apply (since := "2024-10-12")] toContinuousMap_apply

@[simp]
theorem coe_refl : (Homeomorph.refl α : C(α, α)) = ContinuousMap.id α :=
  rfl

@[simp]
theorem coe_trans : (f.trans g : C(α, γ)) = (g : C(β, γ)).comp f :=
  rfl

@[simp]
theorem symm_comp_toContinuousMap :
    (f.symm : C(β, α)).comp (f : C(α, β)) = ContinuousMap.id α := by
  rw [← coe_trans, self_trans_symm, coe_refl]

@[simp]
theorem toContinuousMap_comp_symm :
    (f : C(α, β)).comp (f.symm : C(β, α)) = ContinuousMap.id β := by
  rw [← coe_trans, symm_trans_self, coe_refl]

end Homeomorph
