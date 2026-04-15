/-
Extracted from Data/QPF/Multivariate/Constructions/Fix.lean
Genuine: 12 of 12 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The initial algebra of a multivariate qpf is again a qpf.

For an `(n+1)`-ary QPF `F (α₀,..,αₙ)`, we take the least fixed point of `F` with
regards to its last argument `αₙ`. The result is an `n`-ary functor: `Fix F (α₀,..,αₙ₋₁)`.
Making `Fix F` into a functor allows us to take the fixed point, compose with other functors
and take a fixed point again.

## Main definitions

* `Fix.mk`     - constructor
* `Fix.dest`    - destructor
* `Fix.rec`    - recursor: basis for defining functions by structural recursion on `Fix F α`
* `Fix.drec`   - dependent recursor: generalization of `Fix.rec` where
                  the result type of the function is allowed to depend on the `Fix F α` value
* `Fix.rec_eq` - defining equation for `recursor`
* `Fix.ind`    - induction principle for `Fix F α`

## Implementation notes

For `F` a `QPF`, we define `Fix F α` in terms of the W-type of the polynomial functor `P` of `F`.
We define the relation `WEquiv` and take its quotient as the definition of `Fix F α`.

See [avigad-carneiro-hudon2019] for more details.

## Reference

* Jeremy Avigad, Mario M. Carneiro and Simon Hudon.
  [*Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/

universe u v

namespace MvQPF

open TypeVec

open MvFunctor (LiftP LiftR)

open MvFunctor

variable {n : ℕ} {F : TypeVec.{u} (n + 1) → Type u} [q : MvQPF F]

def recF {α : TypeVec n} {β : Type u} (g : F (α.append1 β) → β) : q.P.W α → β :=
  q.P.wRec fun a f' _f rec => g (abs ⟨a, splitFun f' rec⟩)

theorem recF_eq {α : TypeVec n} {β : Type u} (g : F (α.append1 β) → β) (a : q.P.A)
    (f' : q.P.drop.B a ⟹ α) (f : q.P.last.B a → q.P.W α) :
    recF g (q.P.wMk a f' f) = g (abs ⟨a, splitFun f' (recF g ∘ f)⟩) := by
  rw [recF, MvPFunctor.wRec_eq]; rfl

set_option backward.isDefEq.respectTransparency false in

theorem recF_eq' {α : TypeVec n} {β : Type u} (g : F (α.append1 β) → β) (x : q.P.W α) :
    recF g x = g (abs (appendFun id (recF g) <$$> q.P.wDest' x)) := by
  induction x using q.P.wCases
  case ih a f' f =>
    rw [recF_eq, q.P.wDest'_wMk, MvPFunctor.map_eq, appendFun_comp_splitFun, TypeVec.id_comp]

inductive WEquiv {α : TypeVec n} : q.P.W α → q.P.W α → Prop
  | ind (a : q.P.A) (f' : q.P.drop.B a ⟹ α) (f₀ f₁ : q.P.last.B a → q.P.W α) :
    (∀ x, WEquiv (f₀ x) (f₁ x)) → WEquiv (q.P.wMk a f' f₀) (q.P.wMk a f' f₁)
  | abs (a₀ : q.P.A) (f'₀ : q.P.drop.B a₀ ⟹ α) (f₀ : q.P.last.B a₀ → q.P.W α) (a₁ : q.P.A)
    (f'₁ : q.P.drop.B a₁ ⟹ α) (f₁ : q.P.last.B a₁ → q.P.W α) :
    abs ⟨a₀, q.P.appendContents f'₀ f₀⟩ = abs ⟨a₁, q.P.appendContents f'₁ f₁⟩ →
      WEquiv (q.P.wMk a₀ f'₀ f₀) (q.P.wMk a₁ f'₁ f₁)
  | trans (u v w : q.P.W α) : WEquiv u v → WEquiv v w → WEquiv u w

theorem recF_eq_of_wEquiv (α : TypeVec n) {β : Type u} (u : F (α.append1 β) → β) (x y : q.P.W α) :
    WEquiv x y → recF u x = recF u y := by
  induction x using q.P.wCases
  case ih a₀ f'₀ f₀ =>
    induction y using q.P.wCases
    case ih a₁ f'₁ f₁ =>
      intro h
      -- Porting note: induction on h doesn't work.
      refine @WEquiv.recOn _ _ _ _ (fun a a' _ ↦ recF u a = recF u a') _ _ h ?_ ?_ ?_
      · intro a f' f₀ f₁ _h ih; simp only [recF_eq]
        congr 4; funext; apply ih
      · intro a₀ f'₀ f₀ a₁ f'₁ f₁ h; simp only [recF_eq', abs_map, MvPFunctor.wDest'_wMk, h]
      · intro x y z _e₁ _e₂ ih₁ ih₂; exact Eq.trans ih₁ ih₂

theorem wEquiv.abs' {α : TypeVec n} (x y : q.P.W α)
    (h : MvQPF.abs (q.P.wDest' x) = MvQPF.abs (q.P.wDest' y)) :
    WEquiv x y := by
  revert h
  induction x using q.P.wCases
  case ih a₀ f'₀ f₀ =>
    induction y using q.P.wCases
    apply WEquiv.abs

theorem wEquiv.refl {α : TypeVec n} (x : q.P.W α) : WEquiv x x := abs' x x rfl

theorem wEquiv.symm {α : TypeVec n} (x y : q.P.W α) : WEquiv x y → WEquiv y x := by
  intro h; induction h with
  | ind a f' f₀ f₁ _h ih => exact WEquiv.ind _ _ _ _ ih
  | abs a₀ f'₀ f₀ a₁ f'₁ f₁ h => exact WEquiv.abs _ _ _ _ _ _ h.symm
  | trans x y z _e₁ _e₂ ih₁ ih₂ => exact MvQPF.WEquiv.trans _ _ _ ih₂ ih₁

def wrepr {α : TypeVec n} : q.P.W α → q.P.W α :=
  recF (q.P.wMk' ∘ repr)

theorem wrepr_wMk {α : TypeVec n} (a : q.P.A) (f' : q.P.drop.B a ⟹ α)
    (f : q.P.last.B a → q.P.W α) :
    wrepr (q.P.wMk a f' f) =
      q.P.wMk' (repr (abs (appendFun id wrepr <$$> ⟨a, q.P.appendContents f' f⟩))) := by
  rw [wrepr, recF_eq', q.P.wDest'_wMk]; rfl

set_option backward.isDefEq.respectTransparency false in

theorem wrepr_equiv {α : TypeVec n} (x : q.P.W α) : WEquiv (wrepr x) x := by
  induction x using q.P.wInd
  case ih a f' f ih =>
    apply WEquiv.trans _ (q.P.wMk' (appendFun id wrepr <$$> ⟨a, q.P.appendContents f' f⟩))
    · apply wEquiv.abs'
      rw [wrepr_wMk, q.P.wDest'_wMk', q.P.wDest'_wMk', abs_repr]
    rw [q.P.map_eq, MvPFunctor.wMk', appendFun_comp_splitFun, id_comp]
    apply WEquiv.ind; exact ih

theorem wEquiv_map {α β : TypeVec n} (g : α ⟹ β) (x y : q.P.W α) :
    WEquiv x y → WEquiv (g <$$> x) (g <$$> y) := by
  intro h; induction h with
  | ind a f' f₀ f₁ h ih => rw [q.P.w_map_wMk, q.P.w_map_wMk]; apply WEquiv.ind; exact ih
  | abs a₀ f'₀ f₀ a₁ f'₁ f₁ h =>
    rw [q.P.w_map_wMk, q.P.w_map_wMk]; apply WEquiv.abs
    change
      abs (q.P.objAppend1 a₀ (g ⊚ f'₀) fun x => q.P.wMap g (f₀ x)) =
        abs (q.P.objAppend1 a₁ (g ⊚ f'₁) fun x => q.P.wMap g (f₁ x))
    rw [← q.P.map_objAppend1, ← q.P.map_objAppend1, abs_map, abs_map, h]
  | trans x y z _ _ ih₁ ih₂ =>
    apply MvQPF.WEquiv.trans
    · apply ih₁
    · apply ih₂
