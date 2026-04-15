/-
Extracted from Algebra/Homology/ModelCategory/Lifting.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lifting properties in cochain complexes

Let `C` be an abelian category. Consider a commutative diagram
in the category `CochainComplex C ℤ`.
```
   t
 A ⟶ X
i|   |p
 v   v
 B ⟶ Y
   b
```
Assume that there exists a degreewise lifting `B.X n ⟶ X.X n` for any `n : ℤ`,
that `Q` is a cokernel of `i`, and `K` is a kernel of `p`. In this situation,
we construct a cocycle in `Cocycle Q K 1` and show that there exists
a lifting `B ⟶ X` if this cocycle is a coboundary.

-/

namespace CochainComplex

open CategoryTheory Limits HomComplex

variable {C : Type*} [Category* C] [Abelian C]

namespace Lifting

variable {A B X Y : CochainComplex C ℤ}
  {t : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {b : B ⟶ Y}
  (sq : CommSq t i p b)
  (hsq : ∀ n, (sq.map (HomologicalComplex.eval _ _ n)).LiftStruct)
  {Q : CochainComplex C ℤ} {π : B ⟶ Q} {hπ : i ≫ π = 0}
  (hQ : IsColimit (CokernelCofork.ofπ _ hπ))
  {K : CochainComplex C ℤ} {ι : K ⟶ X} {hι : ι ≫ p = 0}
  (hK : IsLimit (KernelFork.ofι _ hι))

abbrev cochain₀ : Cochain B X 0 := Cochain.ofHoms (fun n ↦ (hsq n).l)

def cocycle₁' : Cocycle B X 1 :=
  Cocycle.mk (δ 0 1 (cochain₀ sq hsq)) 2 (by simp) (by simp [δ_δ])
