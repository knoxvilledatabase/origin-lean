/-
Extracted from Geometry/Manifold/Algebra/SmoothFunctions.lean
Genuine: 10 | Conflates: 0 | Dissolved: 0 | Infrastructure: 26
-/
import Origin.Core
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Algebraic structures over smooth functions

In this file, we define instances of algebraic structures over smooth functions.
-/

noncomputable section

open scoped Manifold

local notation "∞" => (⊤ : ℕ∞)

open TopologicalSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {N' : Type*} [TopologicalSpace N'] [ChartedSpace H'' N']

namespace SmoothMap

@[to_additive]
protected instance instMul {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H' G]
    [SmoothMul I' G] : Mul C^∞⟮I, N; I', G⟯ :=
  ⟨fun f g => ⟨f * g, f.contMDiff.mul g.contMDiff⟩⟩

@[to_additive (attr := simp)]
theorem coe_mul {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H' G] [SmoothMul I' G]
    (f g : C^∞⟮I, N; I', G⟯) : ⇑(f * g) = f * g :=
  rfl

@[to_additive (attr := simp)]
theorem mul_comp {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H' G] [SmoothMul I' G]
    (f g : C^∞⟮I'', N'; I', G⟯) (h : C^∞⟮I, N; I'', N'⟯) : (f * g).comp h = f.comp h * g.comp h :=
  rfl

@[to_additive]
protected instance instOne {G : Type*} [One G] [TopologicalSpace G] [ChartedSpace H' G] :
    One C^∞⟮I, N; I', G⟯ :=
  ⟨ContMDiffMap.const (1 : G)⟩

@[to_additive (attr := simp)]
theorem coe_one {G : Type*} [One G] [TopologicalSpace G] [ChartedSpace H' G] :
    ⇑(1 : C^∞⟮I, N; I', G⟯) = 1 :=
  rfl

instance instNSMul {G : Type*} [AddMonoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [SmoothAdd I' G] : SMul ℕ C^∞⟮I, N; I', G⟯ where
  smul n f := ⟨n • (f : N → G), (contMDiff_nsmul n).comp f.contMDiff⟩

@[to_additive existing]
instance instPow {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H' G] [SmoothMul I' G] :
    Pow C^∞⟮I, N; I', G⟯ ℕ where
  pow f n := ⟨(f : N → G) ^ n, (contMDiff_pow n).comp f.contMDiff⟩

@[to_additive (attr := simp)]
theorem coe_pow {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H' G] [SmoothMul I' G]
    (f : C^∞⟮I, N; I', G⟯) (n : ℕ) :
    ⇑(f ^ n) = (f : N → G) ^ n :=
  rfl

section GroupStructure

/-!
### Group structure

In this section we show that smooth functions valued in a Lie group inherit a group structure
under pointwise multiplication.
-/

@[to_additive]
instance semigroup {G : Type*} [Semigroup G] [TopologicalSpace G] [ChartedSpace H' G]
    [SmoothMul I' G] : Semigroup C^∞⟮I, N; I', G⟯ :=
  DFunLike.coe_injective.semigroup _ coe_mul

@[to_additive]
instance monoid {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [SmoothMul I' G] : Monoid C^∞⟮I, N; I', G⟯ :=
  DFunLike.coe_injective.monoid _ coe_one coe_mul coe_pow

@[to_additive (attr := simps) "Coercion to a function as an `AddMonoidHom`.
  Similar to `AddMonoidHom.coeFn`."]
def coeFnMonoidHom {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [SmoothMul I' G] : C^∞⟮I, N; I', G⟯ →* N → G where
  toFun := DFunLike.coe
  map_one' := coe_one
  map_mul' := coe_mul

variable (I N)

@[to_additive "For a manifold `N` and a smooth homomorphism `φ` between additive Lie groups `G'`,
`G''`, the 'left-composition-by-`φ`' group homomorphism from `C^∞⟮I, N; I', G'⟯` to
`C^∞⟮I, N; I'', G''⟯`."]
def compLeftMonoidHom {G' : Type*} [Monoid G'] [TopologicalSpace G'] [ChartedSpace H' G']
    [SmoothMul I' G'] {G'' : Type*} [Monoid G''] [TopologicalSpace G''] [ChartedSpace H'' G'']
    [SmoothMul I'' G''] (φ : G' →* G'') (hφ : ContMDiff I' I'' ⊤ φ) :
    C^∞⟮I, N; I', G'⟯ →* C^∞⟮I, N; I'', G''⟯ where
  toFun f := ⟨φ ∘ f, hφ.comp f.contMDiff⟩
  map_one' := by ext; show φ 1 = 1; simp
  map_mul' f g := by ext x; show φ (f x * g x) = φ (f x) * φ (g x); simp

variable (I') {N}

@[to_additive "For an additive Lie group `G` and open sets `U ⊆ V` in `N`, the 'restriction' group
homomorphism from `C^∞⟮I, V; I', G⟯` to `C^∞⟮I, U; I', G⟯`."]
def restrictMonoidHom (G : Type*) [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [SmoothMul I' G] {U V : Opens N} (h : U ≤ V) : C^∞⟮I, V; I', G⟯ →* C^∞⟮I, U; I', G⟯ where
  toFun f := ⟨f ∘ Set.inclusion h, f.contMDiff.comp (contMDiff_inclusion h)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable {I I'}

@[to_additive]
instance commMonoid {G : Type*} [CommMonoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [SmoothMul I' G] : CommMonoid C^∞⟮I, N; I', G⟯ :=
  DFunLike.coe_injective.commMonoid _ coe_one coe_mul coe_pow

@[to_additive]
instance group {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' G] :
    Group C^∞⟮I, N; I', G⟯ :=
  { SmoothMap.monoid with
    inv := fun f => ⟨fun x => (f x)⁻¹, f.contMDiff.inv⟩
    inv_mul_cancel := fun a => by ext; exact inv_mul_cancel _
    div := fun f g => ⟨f / g, f.contMDiff.div g.contMDiff⟩
    div_eq_mul_inv := fun f g => by ext; exact div_eq_mul_inv _ _ }

@[to_additive (attr := simp)]
theorem coe_inv {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' G]
    (f : C^∞⟮I, N; I', G⟯) : ⇑f⁻¹ = (⇑f)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
theorem coe_div {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' G]
    (f g : C^∞⟮I, N; I', G⟯) : ⇑(f / g) = f / g :=
  rfl

@[to_additive]
instance commGroup {G : Type*} [CommGroup G] [TopologicalSpace G] [ChartedSpace H' G]
    [LieGroup I' G] : CommGroup C^∞⟮I, N; I', G⟯ :=
  { SmoothMap.group, SmoothMap.commMonoid with }

end GroupStructure

section RingStructure

/-!
### Ring structure

In this section we show that smooth functions valued in a smooth ring `R` inherit a ring structure
under pointwise multiplication.
-/

instance semiring {R : Type*} [Semiring R] [TopologicalSpace R] [ChartedSpace H' R]
    [SmoothRing I' R] : Semiring C^∞⟮I, N; I', R⟯ :=
  { SmoothMap.addCommMonoid,
    SmoothMap.monoid with
    left_distrib := fun a b c => by ext; exact left_distrib _ _ _
    right_distrib := fun a b c => by ext; exact right_distrib _ _ _
    zero_mul := fun a => by ext; exact zero_mul _
    mul_zero := fun a => by ext; exact mul_zero _ }

instance ring {R : Type*} [Ring R] [TopologicalSpace R] [ChartedSpace H' R] [SmoothRing I' R] :
    Ring C^∞⟮I, N; I', R⟯ :=
  { SmoothMap.semiring, SmoothMap.addCommGroup with }

instance commRing {R : Type*} [CommRing R] [TopologicalSpace R] [ChartedSpace H' R]
    [SmoothRing I' R] : CommRing C^∞⟮I, N; I', R⟯ :=
  { SmoothMap.semiring, SmoothMap.addCommGroup, SmoothMap.commMonoid with }

variable (I N)

def compLeftRingHom {R' : Type*} [Ring R'] [TopologicalSpace R'] [ChartedSpace H' R']
    [SmoothRing I' R'] {R'' : Type*} [Ring R''] [TopologicalSpace R''] [ChartedSpace H'' R'']
    [SmoothRing I'' R''] (φ : R' →+* R'') (hφ : ContMDiff I' I'' ⊤ φ) :
    C^∞⟮I, N; I', R'⟯ →+* C^∞⟮I, N; I'', R''⟯ :=
  { SmoothMap.compLeftMonoidHom I N φ.toMonoidHom hφ,
    SmoothMap.compLeftAddMonoidHom I N φ.toAddMonoidHom hφ with
    toFun := fun f => ⟨φ ∘ f, hφ.comp f.contMDiff⟩ }

variable (I') {N}

def restrictRingHom (R : Type*) [Ring R] [TopologicalSpace R] [ChartedSpace H' R] [SmoothRing I' R]
    {U V : Opens N} (h : U ≤ V) : C^∞⟮I, V; I', R⟯ →+* C^∞⟮I, U; I', R⟯ :=
  { SmoothMap.restrictMonoidHom I I' R h, SmoothMap.restrictAddMonoidHom I I' R h with
    toFun := fun f => ⟨f ∘ Set.inclusion h, f.contMDiff.comp (contMDiff_inclusion h)⟩ }

variable {I I'}

@[simps]
def coeFnRingHom {R : Type*} [CommRing R] [TopologicalSpace R] [ChartedSpace H' R]
    [SmoothRing I' R] : C^∞⟮I, N; I', R⟯ →+* N → R :=
  { (coeFnMonoidHom : C^∞⟮I, N; I', R⟯ →* _), (coeFnAddMonoidHom : C^∞⟮I, N; I', R⟯ →+ _) with
    toFun := (↑) }

def evalRingHom {R : Type*} [CommRing R] [TopologicalSpace R] [ChartedSpace H' R] [SmoothRing I' R]
    (n : N) : C^∞⟮I, N; I', R⟯ →+* R :=
  (Pi.evalRingHom _ n : (N → R) →+* R).comp SmoothMap.coeFnRingHom

end RingStructure

section ModuleStructure

/-!
### Semimodule structure

In this section we show that smooth functions valued in a vector space `M` over a normed
field `𝕜` inherit a vector space structure.
-/

instance instSMul {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] :
    SMul 𝕜 C^∞⟮I, N; 𝓘(𝕜, V), V⟯ :=
  ⟨fun r f => ⟨r • ⇑f, contMDiff_const.smul f.contMDiff⟩⟩

@[simp]
theorem coe_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] (r : 𝕜)
    (f : C^∞⟮I, N; 𝓘(𝕜, V), V⟯) : ⇑(r • f) = r • ⇑f :=
  rfl

@[simp]
theorem smul_comp {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] (r : 𝕜)
    (g : C^∞⟮I'', N'; 𝓘(𝕜, V), V⟯) (h : C^∞⟮I, N; I'', N'⟯) : (r • g).comp h = r • g.comp h :=
  rfl

instance module {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] :
    Module 𝕜 C^∞⟮I, N; 𝓘(𝕜, V), V⟯ :=
  Function.Injective.module 𝕜 coeFnAddMonoidHom ContMDiffMap.coe_injective coe_smul

@[simps]
def coeFnLinearMap {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] :
    C^∞⟮I, N; 𝓘(𝕜, V), V⟯ →ₗ[𝕜] N → V :=
  { (coeFnAddMonoidHom : C^∞⟮I, N; 𝓘(𝕜, V), V⟯ →+ _) with
    toFun := (↑)
    map_smul' := coe_smul }

end ModuleStructure

section AlgebraStructure

/-!
### Algebra structure

In this section we show that smooth functions valued in a normed algebra `A` over a normed field `𝕜`
inherit an algebra structure.
-/

variable {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A] [SmoothRing 𝓘(𝕜, A) A]

def C : 𝕜 →+* C^∞⟮I, N; 𝓘(𝕜, A), A⟯ where
  toFun := fun c : 𝕜 => ⟨fun _ => (algebraMap 𝕜 A) c, contMDiff_const⟩
  map_one' := by ext; exact (algebraMap 𝕜 A).map_one
  map_mul' c₁ c₂ := by ext; exact (algebraMap 𝕜 A).map_mul _ _
  map_zero' := by ext; exact (algebraMap 𝕜 A).map_zero
  map_add' c₁ c₂ := by ext; exact (algebraMap 𝕜 A).map_add _ _

instance algebra : Algebra 𝕜 C^∞⟮I, N; 𝓘(𝕜, A), A⟯ :=
  { --SmoothMap.semiring with -- Porting note: Commented this out.
    smul := fun r f => ⟨r • f, contMDiff_const.smul f.contMDiff⟩
    toRingHom := SmoothMap.C
    commutes' := fun c f => by ext x; exact Algebra.commutes' _ _
    smul_def' := fun c f => by ext x; exact Algebra.smul_def' _ _ }

@[simps]
def coeFnAlgHom : C^∞⟮I, N; 𝓘(𝕜, A), A⟯ →ₐ[𝕜] N → A where
  toFun := (↑)
  commutes' _ := rfl
  -- `(SmoothMap.coeFnRingHom : C^∞⟮I, N; 𝓘(𝕜, A), A⟯ →+* _) with` times out for some reason
  map_zero' := SmoothMap.coe_zero
  map_one' := SmoothMap.coe_one
  map_add' := SmoothMap.coe_add
  map_mul' := SmoothMap.coe_mul

end AlgebraStructure

section ModuleOverContinuousFunctions

/-!
### Structure as module over scalar functions

If `V` is a module over `𝕜`, then we show that the space of smooth functions from `N` to `V`
is naturally a vector space over the ring of smooth functions from `N` to `𝕜`. -/

instance instSMul' {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] :
    SMul C^∞⟮I, N; 𝕜⟯ C^∞⟮I, N; 𝓘(𝕜, V), V⟯ :=
  ⟨fun f g => ⟨fun x => f x • g x, ContMDiff.smul f.2 g.2⟩⟩

@[simp]
theorem smul_comp' {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] (f : C^∞⟮I'', N'; 𝕜⟯)
    (g : C^∞⟮I'', N'; 𝓘(𝕜, V), V⟯) (h : C^∞⟮I, N; I'', N'⟯) :
    (f • g).comp h = f.comp h • g.comp h :=
  rfl

instance module' {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] :
    Module C^∞⟮I, N; 𝓘(𝕜), 𝕜⟯ C^∞⟮I, N; 𝓘(𝕜, V), V⟯ where
  smul := (· • ·)
  smul_add c f g := by ext x; exact smul_add (c x) (f x) (g x)
  add_smul c₁ c₂ f := by ext x; exact add_smul (c₁ x) (c₂ x) (f x)
  mul_smul c₁ c₂ f := by ext x; exact mul_smul (c₁ x) (c₂ x) (f x)
  one_smul f := by ext x; exact one_smul 𝕜 (f x)
  zero_smul f := by ext x; exact zero_smul _ _
  smul_zero r := by ext x; exact smul_zero _

end ModuleOverContinuousFunctions

end SmoothMap
