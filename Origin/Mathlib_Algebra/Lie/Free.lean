/-
Extracted from Algebra/Lie/Free.lean
Genuine: 15 of 28 | Dissolved: 0 | Infrastructure: 13
-/
import Origin.Core

/-!
# Free Lie algebras

Given a commutative ring `R` and a type `X` we construct the free Lie algebra on `X` with
coefficients in `R` together with its universal property.

## Main definitions

  * `FreeLieAlgebra`
  * `FreeLieAlgebra.lift`
  * `FreeLieAlgebra.of`
  * `FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra`

## Implementation details

### Quotient of free non-unital, non-associative algebra

We follow [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*](bourbaki1975) and construct
the free Lie algebra as a quotient of the free non-unital, non-associative algebra. Since we do not
currently have definitions of ideals, lattices of ideals, and quotients for
`NonUnitalNonAssocSemiring`, we construct our quotient using the low-level `Quot` function on
an inductively-defined relation.

### Alternative construction (needs PBW)

An alternative construction of the free Lie algebra on `X` is to start with the free unital
associative algebra on `X`, regard it as a Lie algebra via the ring commutator, and take its
smallest Lie subalgebra containing `X`. I.e.:
`LieSubalgebra.lieSpan R (FreeAlgebra R X) (Set.range (FreeAlgebra.ι R))`.

However with this definition there does not seem to be an easy proof that the required universal
property holds, and I don't know of a proof that avoids invoking the Poincaré–Birkhoff–Witt theorem.
A related MathOverflow question is [this one](https://mathoverflow.net/questions/396680/).

## Tags

lie algebra, free algebra, non-unital, non-associative, universal property, forgetful functor,
adjoint functor
-/

universe u v w

noncomputable section

variable (R : Type u) (X : Type v) [CommRing R]

local notation "lib" => FreeNonUnitalNonAssocAlgebra

local notation "lib.lift" => FreeNonUnitalNonAssocAlgebra.lift

local notation "lib.of" => FreeNonUnitalNonAssocAlgebra.of

local notation "lib.lift_of_apply" => FreeNonUnitalNonAssocAlgebra.lift_of_apply

local notation "lib.lift_comp_of" => FreeNonUnitalNonAssocAlgebra.lift_comp_of

namespace FreeLieAlgebra

inductive Rel : lib R X → lib R X → Prop
  | lie_self (a : lib R X) : Rel (a * a) 0
  | leibniz_lie (a b c : lib R X) : Rel (a * (b * c)) (a * b * c + b * (a * c))
  | smul (t : R) {a b : lib R X} : Rel a b → Rel (t • a) (t • b)
  | add_right {a b : lib R X} (c : lib R X) : Rel a b → Rel (a + c) (b + c)
  | mul_left (a : lib R X) {b c : lib R X} : Rel b c → Rel (a * b) (a * c)
  | mul_right {a b : lib R X} (c : lib R X) : Rel a b → Rel (a * c) (b * c)

variable {R X}

theorem Rel.addLeft (a : lib R X) {b c : lib R X} (h : Rel R X b c) : Rel R X (a + b) (a + c) := by
  rw [add_comm _ b, add_comm _ c]; exact h.add_right _

theorem Rel.neg {a b : lib R X} (h : Rel R X a b) : Rel R X (-a) (-b) := by
  simpa only [neg_one_smul] using h.smul (-1)

theorem Rel.subLeft (a : lib R X) {b c : lib R X} (h : Rel R X b c) : Rel R X (a - b) (a - c) := by
  simpa only [sub_eq_add_neg] using h.neg.addLeft a

theorem Rel.subRight {a b : lib R X} (c : lib R X) (h : Rel R X a b) : Rel R X (a - c) (b - c) := by
  simpa only [sub_eq_add_neg] using h.add_right (-c)

theorem Rel.smulOfTower {S : Type*} [Monoid S] [DistribMulAction S R] [IsScalarTower S R R] (t : S)
    (a b : lib R X) (h : Rel R X a b) : Rel R X (t • a) (t • b) := by
  rw [← smul_one_smul R t a, ← smul_one_smul R t b]
  exact h.smul _

end FreeLieAlgebra

def FreeLieAlgebra :=
  Quot (FreeLieAlgebra.Rel R X)

-- INSTANCE (free from Core): :

namespace FreeLieAlgebra

-- INSTANCE (free from Core): {S

-- INSTANCE (free from Core): {S

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): {S

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable {X}

def of : X → FreeLieAlgebra R X := fun x => Quot.mk _ (lib.of R x)

variable {L : Type w} [LieRing L] [LieAlgebra R L]

def liftAux (f : X → CommutatorRing L) :=
  lib.lift R f

theorem liftAux_map_smul (f : X → L) (t : R) (a : lib R X) :
    liftAux R f (t • a) = t • liftAux R f a :=
  map_smul _ t a

theorem liftAux_map_add (f : X → L) (a b : lib R X) :
    liftAux R f (a + b) = liftAux R f a + liftAux R f b :=
  map_add _ a b

theorem liftAux_map_mul (f : X → L) (a b : lib R X) :
    liftAux R f (a * b) = ⁅liftAux R f a, liftAux R f b⁆ :=
  map_mul _ a b

theorem liftAux_spec (f : X → L) (a b : lib R X) (h : FreeLieAlgebra.Rel R X a b) :
    liftAux R f a = liftAux R f b := by
  induction h with
  | lie_self a' => simp only [liftAux_map_mul, map_zero, lie_self]
  | leibniz_lie a' b' c' =>
    simp only [liftAux_map_mul, liftAux_map_add, sub_add_cancel, lie_lie]
  | smul b' _ h₂ => simp only [liftAux_map_smul, h₂]
  | add_right c' _ h₂ => simp only [liftAux_map_add, h₂]
  | mul_left c' _ h₂ => simp only [liftAux_map_mul, h₂]
  | mul_right c' _ h₂ => simp only [liftAux_map_mul, h₂]

def mk : lib R X →ₙₐ[R] CommutatorRing (FreeLieAlgebra R X) where
  toFun := Quot.mk (Rel R X)
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

set_option backward.isDefEq.respectTransparency false in

def lift : (X → L) ≃ (FreeLieAlgebra R X →ₗ⁅R⁆ L) where
  toFun f :=
    { toFun := fun c => Quot.liftOn c (liftAux R f) (liftAux_spec R f)
      map_add' := by rintro ⟨a⟩ ⟨b⟩; rw [← liftAux_map_add]; rfl
      map_smul' := by rintro t ⟨a⟩; rw [← liftAux_map_smul]; rfl
      map_lie' := by rintro ⟨a⟩ ⟨b⟩; rw [← liftAux_map_mul]; rfl }
  invFun F := F ∘ of R
  left_inv f := by
    ext x
    simp only [liftAux, of, LieHom.coe_mk, Function.comp_apply, lib.lift_of_apply]
  right_inv F := by
    ext ⟨a⟩
    let F' := F.toNonUnitalAlgHom.comp (mk R)
    exact NonUnitalAlgHom.congr_fun (lib.lift_comp_of R F') a
