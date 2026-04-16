/-
Extracted from Algebra/Group/Pi/Lemmas.lean
Genuine: 47 | Conflates: 0 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Data.Set.Function
import Mathlib.Logic.Pairwise

noncomputable section

/-!
# Extra lemmas about products of monoids and groups

This file proves lemmas about the instances defined in `Algebra.Group.Pi.Basic` that require more
imports.
-/

universe u v w

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v}

variable (i : I)

@[to_additive (attr := simp)]
theorem Set.range_one {α β : Type*} [One β] [Nonempty α] : Set.range (1 : α → β) = {1} :=
  range_const

@[to_additive]
theorem Set.preimage_one {α β : Type*} [One β] (s : Set β) [Decidable ((1 : β) ∈ s)] :
    (1 : α → β) ⁻¹' s = if (1 : β) ∈ s then Set.univ else ∅ :=
  Set.preimage_const 1 s

namespace Pi

variable {α β : Type*} [Preorder α] [Preorder β]

@[to_additive] lemma one_mono [One β] : Monotone (1 : α → β) := monotone_const

@[to_additive] lemma one_anti [One β] : Antitone (1 : α → β) := antitone_const

end Pi

namespace MulHom

@[to_additive]
theorem coe_mul {M N} {_ : Mul M} {_ : CommSemigroup N} (f g : M →ₙ* N) : (f * g : M → N) =
    fun x => f x * g x := rfl

end MulHom

section MulHom

@[to_additive (attr := simps)
  "A family of AddHom's `f a : γ → β a` defines an AddHom `Pi.addHom f : γ → Π a, β a` given by
  `Pi.addHom f x b = f b x`."]
def Pi.mulHom {γ : Type w} [∀ i, Mul (f i)] [Mul γ] (g : ∀ i, γ →ₙ* f i) : γ →ₙ* ∀ i, f i where
  toFun x i := g i x
  map_mul' x y := funext fun i => (g i).map_mul x y

@[to_additive]
theorem Pi.mulHom_injective {γ : Type w} [Nonempty I] [∀ i, Mul (f i)] [Mul γ] (g : ∀ i, γ →ₙ* f i)
    (hg : ∀ i, Function.Injective (g i)) : Function.Injective (Pi.mulHom g) := fun _ _ h =>
  let ⟨i⟩ := ‹Nonempty I›
  hg i ((funext_iff.mp h : _) i)

@[to_additive (attr := simps)
  "A family of additive monoid homomorphisms `f a : γ →+ β a` defines a monoid homomorphism
  `Pi.addMonoidHom f : γ →+ Π a, β a` given by `Pi.addMonoidHom f x b = f b x`."]
def Pi.monoidHom {γ : Type w} [∀ i, MulOneClass (f i)] [MulOneClass γ] (g : ∀ i, γ →* f i) :
    γ →* ∀ i, f i :=
  { Pi.mulHom fun i => (g i).toMulHom with
    toFun := fun x i => g i x
    map_one' := funext fun i => (g i).map_one }

@[to_additive]
theorem Pi.monoidHom_injective {γ : Type w} [Nonempty I] [∀ i, MulOneClass (f i)] [MulOneClass γ]
    (g : ∀ i, γ →* f i) (hg : ∀ i, Function.Injective (g i)) :
    Function.Injective (Pi.monoidHom g) :=
  Pi.mulHom_injective (fun i => (g i).toMulHom) hg

variable (f)

variable [(i : I) → Mul (f i)]

@[to_additive (attr := simps)
  "Evaluation of functions into an indexed collection of additive semigroups at a point is an
  additive semigroup homomorphism. This is `Function.eval i` as an `AddHom`."]
def Pi.evalMulHom (i : I) : (∀ i, f i) →ₙ* f i where
  toFun g := g i
  map_mul' _ _ := Pi.mul_apply _ _ i

@[to_additive (attr := simps) "`Function.const` as an `AddHom`."]
def Pi.constMulHom (α β : Type*) [Mul β] :
    β →ₙ* α → β where
  toFun := Function.const α
  map_mul' _ _ := rfl

@[to_additive (attr := simps) "Coercion of an `AddHom` into a function is itself an `AddHom`.
See also `AddHom.eval`."]
def MulHom.coeFn (α β : Type*) [Mul α] [CommSemigroup β] :
    (α →ₙ* β) →ₙ* α → β where
  toFun g := g
  map_mul' _ _ := rfl

@[to_additive (attr := simps) "Additive semigroup homomorphism between the function spaces `I → α`
and `I → β`, induced by an additive semigroup homomorphism `f` between `α` and `β`"]
protected def MulHom.compLeft {α β : Type*} [Mul α] [Mul β] (f : α →ₙ* β) (I : Type*) :
    (I → α) →ₙ* I → β where
  toFun h := f ∘ h
  map_mul' _ _ := by ext; simp

end MulHom

section MonoidHom

variable (f)

variable [(i : I) → MulOneClass (f i)]

@[to_additive (attr := simps) "Evaluation of functions into an indexed collection of additive
monoids at a point is an additive monoid homomorphism. This is `Function.eval i` as an
`AddMonoidHom`."]
def Pi.evalMonoidHom (i : I) : (∀ i, f i) →* f i where
  toFun g := g i
  map_one' := Pi.one_apply i
  map_mul' _ _ := Pi.mul_apply _ _ i

@[to_additive (attr := simps) "`Function.const` as an `AddMonoidHom`."]
def Pi.constMonoidHom (α β : Type*) [MulOneClass β] : β →* α → β where
  toFun := Function.const α
  map_one' := rfl
  map_mul' _ _ := rfl

@[to_additive (attr := simps) "Coercion of an `AddMonoidHom` into a function is itself
an `AddMonoidHom`.
See also `AddMonoidHom.eval`."]
def MonoidHom.coeFn (α β : Type*) [MulOneClass α] [CommMonoid β] : (α →* β) →* α → β where
  toFun g := g
  map_one' := rfl
  map_mul' _ _ := rfl

@[to_additive (attr := simps)
  "Additive monoid homomorphism between the function spaces `I → α` and `I → β`, induced by an
  additive monoid homomorphism `f` between `α` and `β`"]
protected def MonoidHom.compLeft {α β : Type*} [MulOneClass α] [MulOneClass β] (f : α →* β)
    (I : Type*) : (I → α) →* I → β where
  toFun h := f ∘ h
  map_one' := by ext; dsimp; simp
  map_mul' _ _ := by ext; simp

end MonoidHom

section Single

variable [DecidableEq I]

open Pi

variable (f)

@[to_additive
      "The zero-preserving homomorphism including a single value into a dependent family of values,
      as functions supported at a point.
      This is the `ZeroHom` version of `Pi.single`."]
nonrec def OneHom.mulSingle [∀ i, One <| f i] (i : I) : OneHom (f i) (∀ i, f i) where
  toFun := mulSingle i
  map_one' := mulSingle_one i

@[to_additive (attr := simp)]
theorem OneHom.mulSingle_apply [∀ i, One <| f i] (i : I) (x : f i) :
    mulSingle f i x = Pi.mulSingle i x := rfl

@[to_additive
      "The additive monoid homomorphism including a single additive monoid into a dependent family
      of additive monoids, as functions supported at a point.
      This is the `AddMonoidHom` version of `Pi.single`."]
def MonoidHom.mulSingle [∀ i, MulOneClass <| f i] (i : I) : f i →* ∀ i, f i :=
  { OneHom.mulSingle f i with map_mul' := mulSingle_op₂ (fun _ => (· * ·)) (fun _ => one_mul _) _ }

@[to_additive (attr := simp)]
theorem MonoidHom.mulSingle_apply [∀ i, MulOneClass <| f i] (i : I) (x : f i) :
    mulSingle f i x = Pi.mulSingle i x :=
  rfl

variable {f}

@[to_additive]
theorem Pi.mulSingle_sup [∀ i, SemilatticeSup (f i)] [∀ i, One (f i)] (i : I) (x y : f i) :
    Pi.mulSingle i (x ⊔ y) = Pi.mulSingle i x ⊔ Pi.mulSingle i y :=
  Function.update_sup _ _ _ _

@[to_additive]
theorem Pi.mulSingle_inf [∀ i, SemilatticeInf (f i)] [∀ i, One (f i)] (i : I) (x y : f i) :
    Pi.mulSingle i (x ⊓ y) = Pi.mulSingle i x ⊓ Pi.mulSingle i y :=
  Function.update_inf _ _ _ _

@[to_additive]
theorem Pi.mulSingle_mul [∀ i, MulOneClass <| f i] (i : I) (x y : f i) :
    mulSingle i (x * y) = mulSingle i x * mulSingle i y :=
  (MonoidHom.mulSingle f i).map_mul x y

@[to_additive]
theorem Pi.mulSingle_inv [∀ i, Group <| f i] (i : I) (x : f i) :
    mulSingle i x⁻¹ = (mulSingle i x)⁻¹ :=
  (MonoidHom.mulSingle f i).map_inv x

@[to_additive]
theorem Pi.mulSingle_div [∀ i, Group <| f i] (i : I) (x y : f i) :
    mulSingle i (x / y) = mulSingle i x / mulSingle i y :=
  (MonoidHom.mulSingle f i).map_div x y

@[to_additive]
theorem Pi.mulSingle_pow [∀ i, Monoid (f i)] (i : I) (x : f i) (n : ℕ) :
    mulSingle i (x ^ n) = mulSingle i x ^ n :=
  (MonoidHom.mulSingle f i).map_pow x n

@[to_additive]
theorem Pi.mulSingle_zpow [∀ i, Group (f i)] (i : I) (x : f i) (n : ℤ) :
    mulSingle i (x ^ n) = mulSingle i x ^ n :=
  (MonoidHom.mulSingle f i).map_zpow x n

@[to_additive
      "The injection into an additive pi group at different indices commutes.
      For injections of commuting elements at the same index, see `AddCommute.map`"]
theorem Pi.mulSingle_commute [∀ i, MulOneClass <| f i] :
    Pairwise fun i j => ∀ (x : f i) (y : f j), Commute (mulSingle i x) (mulSingle j y) := by
  intro i j hij x y; ext k
  by_cases h1 : i = k
  · subst h1
    simp [hij]
  by_cases h2 : j = k
  · subst h2
    simp [hij]
  simp [h1, h2]

@[to_additive "The injection into an additive pi group with the same values commutes."]
theorem Pi.mulSingle_apply_commute [∀ i, MulOneClass <| f i] (x : ∀ i, f i) (i j : I) :
    Commute (mulSingle i (x i)) (mulSingle j (x j)) := by
  obtain rfl | hij := Decidable.eq_or_ne i j
  · rfl
  · exact Pi.mulSingle_commute hij _ _

@[to_additive]
theorem Pi.update_eq_div_mul_mulSingle [∀ i, Group <| f i] (g : ∀ i : I, f i) (x : f i) :
    Function.update g i x = g / mulSingle i (g i) * mulSingle i x := by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [Function.update_noteq h.symm, h]

@[to_additive]
theorem Pi.mulSingle_mul_mulSingle_eq_mulSingle_mul_mulSingle {M : Type*} [CommMonoid M]
    {k l m n : I} {u v : M} (hu : u ≠ 1) (hv : v ≠ 1) :
    (mulSingle k u : I → M) * mulSingle l v = mulSingle m u * mulSingle n v ↔
      k = m ∧ l = n ∨ u = v ∧ k = n ∧ l = m ∨ u * v = 1 ∧ k = l ∧ m = n := by
  refine ⟨fun h => ?_, ?_⟩
  · have hk := congr_fun h k
    have hl := congr_fun h l
    have hm := (congr_fun h m).symm
    have hn := (congr_fun h n).symm
    simp only [mul_apply, mulSingle_apply, if_pos rfl] at hk hl hm hn
    rcases eq_or_ne k m with (rfl | hkm)
    · refine Or.inl ⟨rfl, not_ne_iff.mp fun hln => (hv ?_).elim⟩
      rcases eq_or_ne k l with (rfl | hkl)
      · rwa [if_neg hln.symm, if_neg hln.symm, one_mul, one_mul] at hn
      · rwa [if_neg hkl.symm, if_neg hln, one_mul, one_mul] at hl
    · rcases eq_or_ne m n with (rfl | hmn)
      · rcases eq_or_ne k l with (rfl | hkl)
        · rw [if_neg hkm.symm, if_neg hkm.symm, one_mul, if_pos rfl] at hm
          exact Or.inr (Or.inr ⟨hm, rfl, rfl⟩)
        · simp only [if_neg hkm, if_neg hkl, mul_one] at hk
          dsimp at hk
          contradiction
      · rw [if_neg hkm.symm, if_neg hmn, one_mul, mul_one] at hm
        obtain rfl := (ite_ne_right_iff.mp (ne_of_eq_of_ne hm.symm hu)).1
        rw [if_neg hkm, if_neg hkm, one_mul, mul_one] at hk
        obtain rfl := (ite_ne_right_iff.mp (ne_of_eq_of_ne hk.symm hu)).1
        exact Or.inr (Or.inl ⟨hk.trans (if_pos rfl), rfl, rfl⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨h, rfl, rfl⟩)
    · rfl
    · apply mul_comm
    · simp_rw [← Pi.mulSingle_mul, h, mulSingle_one]

end Single

section

variable [∀ i, Mul <| f i]

@[to_additive]
theorem SemiconjBy.pi {x y z : ∀ i, f i} (h : ∀ i, SemiconjBy (x i) (y i) (z i)) :
    SemiconjBy x y z :=
  funext h

@[to_additive]
theorem Pi.semiconjBy_iff {x y z : ∀ i, f i} :
    SemiconjBy x y z ↔ ∀ i, SemiconjBy (x i) (y i) (z i) := funext_iff

@[to_additive]
theorem Commute.pi {x y : ∀ i, f i} (h : ∀ i, Commute (x i) (y i)) : Commute x y := .pi h

@[to_additive]
theorem Pi.commute_iff {x y : ∀ i, f i} : Commute x y ↔ ∀ i, Commute (x i) (y i) := semiconjBy_iff

end

namespace Function

@[to_additive (attr := simp)]
theorem update_one [∀ i, One (f i)] [DecidableEq I] (i : I) : update (1 : ∀ i, f i) i 1 = 1 :=
  update_eq_self i (1 : (a : I) → f a)

@[to_additive]
theorem update_mul [∀ i, Mul (f i)] [DecidableEq I] (f₁ f₂ : ∀ i, f i) (i : I) (x₁ : f i)
    (x₂ : f i) : update (f₁ * f₂) i (x₁ * x₂) = update f₁ i x₁ * update f₂ i x₂ :=
  funext fun j => (apply_update₂ (fun _ => (· * ·)) f₁ f₂ i x₁ x₂ j).symm

@[to_additive]
theorem update_inv [∀ i, Inv (f i)] [DecidableEq I] (f₁ : ∀ i, f i) (i : I) (x₁ : f i) :
    update f₁⁻¹ i x₁⁻¹ = (update f₁ i x₁)⁻¹ :=
  funext fun j => (apply_update (fun _ => Inv.inv) f₁ i x₁ j).symm

@[to_additive]
theorem update_div [∀ i, Div (f i)] [DecidableEq I] (f₁ f₂ : ∀ i, f i) (i : I) (x₁ : f i)
    (x₂ : f i) : update (f₁ / f₂) i (x₁ / x₂) = update f₁ i x₁ / update f₂ i x₂ :=
  funext fun j => (apply_update₂ (fun _ => (· / ·)) f₁ f₂ i x₁ x₂ j).symm

variable [One α] [Nonempty ι] {a : α}

@[to_additive (attr := simp)]
theorem const_eq_one : const ι a = 1 ↔ a = 1 :=
  @const_inj _ _ _ _ 1

@[to_additive]
theorem const_ne_one : const ι a ≠ 1 ↔ a ≠ 1 :=
  Iff.not const_eq_one

end Function

section Piecewise

@[to_additive]
theorem Set.piecewise_mul [∀ i, Mul (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)]
    (f₁ f₂ g₁ g₂ : ∀ i, f i) :
    s.piecewise (f₁ * f₂) (g₁ * g₂) = s.piecewise f₁ g₁ * s.piecewise f₂ g₂ :=
  s.piecewise_op₂ f₁ _ _ _ fun _ => (· * ·)

@[to_additive]
theorem Set.piecewise_inv [∀ i, Inv (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)] (f₁ g₁ : ∀ i, f i) :
    s.piecewise f₁⁻¹ g₁⁻¹ = (s.piecewise f₁ g₁)⁻¹ :=
  s.piecewise_op f₁ g₁ fun _ x => x⁻¹

@[to_additive]
theorem Set.piecewise_div [∀ i, Div (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)]
    (f₁ f₂ g₁ g₂ : ∀ i, f i) :
    s.piecewise (f₁ / f₂) (g₁ / g₂) = s.piecewise f₁ g₁ / s.piecewise f₂ g₂ :=
  s.piecewise_op₂ f₁ _ _ _ fun _ => (· / ·)

end Piecewise

section Extend

variable {η : Type v} (R : Type w) (s : ι → η)

@[to_additive (attr := simps) Function.ExtendByZero.hom "`Function.extend s f 0` as a bundled hom."]
noncomputable def Function.ExtendByOne.hom [MulOneClass R] :
    (ι → R) →* η → R where
  toFun f := Function.extend s f 1
  map_one' := Function.extend_one s
  map_mul' f g := by simpa using Function.extend_mul s f g 1 1

end Extend

namespace Pi

variable [DecidableEq I] [∀ i, Preorder (f i)] [∀ i, One (f i)]

@[to_additive]
theorem mulSingle_mono : Monotone (Pi.mulSingle i : f i → ∀ i, f i) :=
  Function.update_mono

@[to_additive]
theorem mulSingle_strictMono : StrictMono (Pi.mulSingle i : f i → ∀ i, f i) :=
  Function.update_strictMono

end Pi

namespace Sigma

variable {α : Type*} {β : α → Type*} {γ : ∀ a, β a → Type*}

@[to_additive (attr := simp)]
theorem curry_one [∀ a b, One (γ a b)] : Sigma.curry (1 : (i : Σ a, β a) → γ i.1 i.2) = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem uncurry_one [∀ a b, One (γ a b)] : Sigma.uncurry (1 : ∀ a b, γ a b) = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem curry_mul [∀ a b, Mul (γ a b)] (x y : (i : Σ a, β a) → γ i.1 i.2) :
    Sigma.curry (x * y) = Sigma.curry x * Sigma.curry y :=
  rfl

@[to_additive (attr := simp)]
theorem uncurry_mul [∀ a b, Mul (γ a b)] (x y : ∀ a b, γ a b) :
    Sigma.uncurry (x * y) = Sigma.uncurry x * Sigma.uncurry y :=
  rfl

@[to_additive (attr := simp)]
theorem curry_inv [∀ a b, Inv (γ a b)] (x : (i : Σ a, β a) → γ i.1 i.2) :
    Sigma.curry (x⁻¹) = (Sigma.curry x)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
theorem uncurry_inv [∀ a b, Inv (γ a b)] (x : ∀ a b, γ a b) :
    Sigma.uncurry (x⁻¹) = (Sigma.uncurry x)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
theorem curry_mulSingle [DecidableEq α] [∀ a, DecidableEq (β a)] [∀ a b, One (γ a b)]
    (i : Σ a, β a) (x : γ i.1 i.2) :
    Sigma.curry (Pi.mulSingle i x) = Pi.mulSingle i.1 (Pi.mulSingle i.2 x) := by
  simp only [Pi.mulSingle, Sigma.curry_update, Sigma.curry_one, Pi.one_apply]

@[to_additive (attr := simp)]
theorem uncurry_mulSingle_mulSingle [DecidableEq α] [∀ a, DecidableEq (β a)] [∀ a b, One (γ a b)]
    (a : α) (b : β a) (x : γ a b) :
    Sigma.uncurry (Pi.mulSingle a (Pi.mulSingle b x)) = Pi.mulSingle (Sigma.mk a b) x := by
  rw [← curry_mulSingle ⟨a, b⟩, uncurry_curry]

end Sigma
