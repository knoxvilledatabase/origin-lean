/-
Extracted from Data/QPF/Univariate/Basic.lean
Genuine: 15 of 17 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!

# Quotients of Polynomial Functors

We assume the following:

* `P`: a polynomial functor
* `W`: its W-type
* `M`: its M-type
* `F`: a functor

We define:

* `q`: `QPF` data, representing `F` as a quotient of `P`

The main goal is to construct:

* `Fix`: the initial algebra with structure map `F Fix → Fix`.
* `Cofix`: the final coalgebra with structure map `Cofix → F Cofix`

We also show that the composition of qpfs is a qpf, and that the quotient of a qpf
is a qpf.

The present theory focuses on the univariate case for qpfs

## References

* [Jeremy Avigad, Mario M. Carneiro and Simon Hudon, *Data Types as Quotients of Polynomial
  Functors*][avigad-carneiro-hudon2019]

-/

universe u u' v

class QPF (F : Type u → Type v) extends Functor F where
  P : PFunctor.{u, u'}
  abs : ∀ {α}, P α → F α
  repr : ∀ {α}, F α → P α
  abs_repr : ∀ {α} (x : F α), abs (repr x) = x
  abs_map : ∀ {α β} (f : α → β) (p : P α), abs (P.map f p) = f <$> abs p

namespace QPF

variable {F : Type u → Type v} [q : QPF F]

open Functor (Liftp Liftr)

theorem id_map {α : Type _} (x : F α) : id <$> x = x := by
  rw [← abs_repr x]
  obtain ⟨a, f⟩ := repr x
  rw [← abs_map]
  rfl

theorem comp_map {α β γ : Type _} (f : α → β) (g : β → γ) (x : F α) :
    (g ∘ f) <$> x = g <$> f <$> x := by
  rw [← abs_repr x]
  rw [← abs_map, ← abs_map, ← abs_map]
  rfl

theorem lawfulFunctor
    (h : ∀ α β : Type u, @Functor.mapConst F _ α _ = Functor.map ∘ Function.const β) :
    LawfulFunctor F :=
  { map_const := @h
    id_map := @id_map F _
    comp_map := @comp_map F _ }

open Functor

theorem liftp_iff {α : Type u} (p : α → Prop) (x : F α) :
    Liftp p x ↔ ∃ a f, x = abs ⟨a, f⟩ ∧ ∀ i, p (f i) := by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : repr y with ⟨a, f⟩
    use a, fun i => (f i).val
    constructor
    · rw [← hy, ← abs_repr y, h, ← abs_map]
      rfl
    intro i
    apply (f i).property
  rintro ⟨a, f, h₀, h₁⟩
  use abs ⟨a, fun i => ⟨f i, h₁ i⟩⟩
  rw [← abs_map, h₀]; rfl

theorem liftp_iff' {α : Type u} (p : α → Prop) (x : F α) :
    Liftp p x ↔ ∃ u : q.P α, abs u = x ∧ ∀ i, p (u.snd i) := by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : repr y with ⟨a, f⟩
    use ⟨a, fun i => (f i).val⟩
    dsimp
    constructor
    · rw [← hy, ← abs_repr y, h, ← abs_map]
      rfl
    intro i
    apply (f i).property
  rintro ⟨⟨a, f⟩, h₀, h₁⟩; dsimp at *
  use abs ⟨a, fun i => ⟨f i, h₁ i⟩⟩
  rw [← abs_map, ← h₀]; rfl

theorem liftr_iff {α : Type u} (r : α → α → Prop) (x y : F α) :
    Liftr r x y ↔ ∃ a f₀ f₁, x = abs ⟨a, f₀⟩ ∧ y = abs ⟨a, f₁⟩ ∧ ∀ i, r (f₀ i) (f₁ i) := by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    rcases h : repr u with ⟨a, f⟩
    use a, fun i => (f i).val.fst, fun i => (f i).val.snd
    constructor
    · rw [← xeq, ← abs_repr u, h, ← abs_map]
      rfl
    constructor
    · rw [← yeq, ← abs_repr u, h, ← abs_map]
      rfl
    intro i
    exact (f i).property
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  use abs ⟨a, fun i => ⟨(f₀ i, f₁ i), h i⟩⟩
  constructor
  · rw [xeq, ← abs_map]
    rfl
  rw [yeq, ← abs_map]; rfl

end

def recF {α : Type _} (g : F α → α) : q.P.W → α
  | ⟨a, f⟩ => g (abs ⟨a, fun x => recF g (f x)⟩)

theorem recF_eq {α : Type _} (g : F α → α) (x : q.P.W) :
    recF g x = g (abs (q.P.map (recF g) x.dest)) := by
  cases x
  rfl

inductive Wequiv : q.P.W → q.P.W → Prop
  | ind (a : q.P.A) (f f' : q.P.B a → q.P.W) : (∀ x, Wequiv (f x) (f' x)) → Wequiv ⟨a, f⟩ ⟨a, f'⟩
  | abs (a : q.P.A) (f : q.P.B a → q.P.W) (a' : q.P.A) (f' : q.P.B a' → q.P.W) :
      abs ⟨a, f⟩ = abs ⟨a', f'⟩ → Wequiv ⟨a, f⟩ ⟨a', f'⟩
  | trans (u v w : q.P.W) : Wequiv u v → Wequiv v w → Wequiv u w

theorem recF_eq_of_Wequiv {α : Type u} (u : F α → α) (x y : q.P.W) :
    Wequiv x y → recF u x = recF u y := by
  intro h
  induction h with
  | ind a f f' _ ih => simp only [recF_eq', PFunctor.map_eq, Function.comp_def, ih]
  | abs a f a' f' h => simp only [recF_eq', abs_map, h]
  | trans x y z _ _ ih₁ ih₂ => exact Eq.trans ih₁ ih₂

theorem Wequiv.abs' (x y : q.P.W) (h : QPF.abs x.dest = QPF.abs y.dest) : Wequiv x y := by
  cases x
  cases y
  apply Wequiv.abs
  apply h

theorem Wequiv.refl (x : q.P.W) : Wequiv x x := by
  obtain ⟨a, f⟩ := x
  exact Wequiv.abs a f a f rfl

theorem Wequiv.symm (x y : q.P.W) : Wequiv x y → Wequiv y x := by
  intro h
  induction h with
  | ind a f f' _ ih => exact Wequiv.ind _ _ _ ih
  | abs a f a' f' h => exact Wequiv.abs _ _ _ _ h.symm
  | trans x y z _ _ ih₁ ih₂ => exact QPF.Wequiv.trans _ _ _ ih₂ ih₁

def Wrepr : q.P.W → q.P.W :=
  recF (PFunctor.W.mk ∘ repr)
