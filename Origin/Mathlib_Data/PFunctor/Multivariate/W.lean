/-
Extracted from Data/PFunctor/Multivariate/W.lean
Genuine: 10 of 15 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# The W construction as a multivariate polynomial functor.

W types are well-founded tree-like structures. They are defined
as the least fixpoint of a polynomial functor.

## Main definitions

* `W_mk`     - constructor
* `W_dest`   - destructor
* `W_rec`    - recursor: basis for defining functions by structural recursion on `P.W α`
* `W_rec_eq` - defining equation for `W_rec`
* `W_ind`    - induction principle for `P.W α`

## Implementation notes

Three views of M-types:

* `wp`: polynomial functor
* `W`: data type inductively defined by a triple:
     shape of the root, data in the root and children of the root
* `W`: least fixed point of a polynomial functor

Specifically, we define the polynomial functor `wp` as:

* A := a tree-like structure without information in the nodes
* B := given the tree-like structure `t`, `B t` is a valid path
  (specified inductively by `W_path`) from the root of `t` to any given node.

As a result `wp α` is made of a dataless tree and a function from
its valid paths to values of `α`

## Reference

* Jeremy Avigad, Mario M. Carneiro and Simon Hudon.
  [*Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/

universe u v

namespace MvPFunctor

open TypeVec

open MvFunctor

variable {n : ℕ} (P : MvPFunctor.{u} (n + 1))

inductive WPath : P.last.W → Fin2 n → Type u
  | root (a : P.A) (f : P.last.B a → P.last.W) (i : Fin2 n) (c : P.drop.B a i) : WPath ⟨a, f⟩ i
  | child (a : P.A) (f : P.last.B a → P.last.W) (i : Fin2 n) (j : P.last.B a)
    (c : WPath (f j) i) : WPath ⟨a, f⟩ i

-- INSTANCE (free from Core): WPath.inhabited

def wPathCasesOn {α : TypeVec n} {a : P.A} {f : P.last.B a → P.last.W} (g' : P.drop.B a ⟹ α)
    (g : ∀ j : P.last.B a, P.WPath (f j) ⟹ α) : P.WPath ⟨a, f⟩ ⟹ α := by
  intro i x
  match x with
  | WPath.root _ _ i c => exact g' i c
  | WPath.child _ _ i j c => exact g j i c

def wPathDestLeft {α : TypeVec n} {a : P.A} {f : P.last.B a → P.last.W}
    (h : P.WPath ⟨a, f⟩ ⟹ α) : P.drop.B a ⟹ α := fun i c => h i (WPath.root a f i c)

def wPathDestRight {α : TypeVec n} {a : P.A} {f : P.last.B a → P.last.W}
    (h : P.WPath ⟨a, f⟩ ⟹ α) : ∀ j : P.last.B a, P.WPath (f j) ⟹ α := fun j i c =>
  h i (WPath.child a f i j c)

theorem wPathCasesOn_eta {α : TypeVec n} {a : P.A} {f : P.last.B a → P.last.W}
    (h : P.WPath ⟨a, f⟩ ⟹ α) : P.wPathCasesOn (P.wPathDestLeft h) (P.wPathDestRight h) = h := by
  ext i x; cases x <;> rfl

theorem comp_wPathCasesOn {α β : TypeVec n} (h : α ⟹ β) {a : P.A} {f : P.last.B a → P.last.W}
    (g' : P.drop.B a ⟹ α) (g : ∀ j : P.last.B a, P.WPath (f j) ⟹ α) :
    h ⊚ P.wPathCasesOn g' g = P.wPathCasesOn (h ⊚ g') fun i => h ⊚ g i := by
  ext i x; cases x <;> rfl

def wp : MvPFunctor n where
  A := P.last.W
  B := P.WPath

def W (α : TypeVec n) : Type _ :=
  P.wp α

-- INSTANCE (free from Core): mvfunctorW

/-!
First, describe operations on `W` as a polynomial functor.
-/

def wpMk {α : TypeVec n} (a : P.A) (f : P.last.B a → P.last.W) (f' : P.WPath ⟨a, f⟩ ⟹ α) :
    P.W α :=
  ⟨⟨a, f⟩, f'⟩

def wpRec {α : TypeVec n} {C : Sort*}
    (g : ∀ (a : P.A) (f : P.last.B a → P.last.W), P.WPath ⟨a, f⟩ ⟹ α → (P.last.B a → C) → C) :
    ∀ (x : P.last.W) (_ : P.WPath x ⟹ α), C
  | ⟨a, f⟩, f' => g a f f' fun i => wpRec g (f i) (P.wPathDestRight f' i)
