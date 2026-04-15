/-
Extracted from Algebra/Homology/HomotopyCategory/HomComplex.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! The cochain complex of homomorphisms between cochain complexes

If `F` and `G` are cochain complexes (indexed by `ℤ`) in a preadditive category,
there is a cochain complex of abelian groups whose `0`-cocycles identify to
morphisms `F ⟶ G`. Informally, in degree `n`, this complex shall consist of
cochains of degree `n` from `F` to `G`, i.e. arbitrary families for morphisms
`F.X p ⟶ G.X (p + n)`. This complex shall be denoted `HomComplex F G`.

In order to avoid type-theoretic issues, a cochain of degree `n : ℤ`
(i.e. a term of type of `Cochain F G n`) shall be defined here
as the data of a morphism `F.X p ⟶ G.X q` for all triplets
`⟨p, q, hpq⟩` where `p` and `q` are integers and `hpq : p + n = q`.
If `α : Cochain F G n`, we shall define `α.v p q hpq : F.X p ⟶ G.X q`.

We follow the signs conventions appearing in the introduction of
[Brian Conrad's book *Grothendieck duality and base change*][conrad2000].

## References
* [Brian Conrad, Grothendieck duality and base change][conrad2000]

-/

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

namespace CochainComplex

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

namespace HomComplex

structure Triplet (n : ℤ) where
  /-- a first integer -/
  p : ℤ
  /-- a second integer -/
  q : ℤ
  /-- the condition on the two integers -/
  hpq : p + n = q

variable (F G)

def Cochain := ∀ (T : Triplet n), F.X T.p ⟶ G.X T.q

deriving AddCommGroup

-- INSTANCE (free from Core): :

namespace Cochain

variable {F G n}

def mk (v : ∀ (p q : ℤ) (_ : p + n = q), F.X p ⟶ G.X q) : Cochain F G n :=
  fun ⟨p, q, hpq⟩ => v p q hpq

def v (γ : Cochain F G n) (p q : ℤ) (hpq : p + n = q) :
    F.X p ⟶ G.X q := γ ⟨p, q, hpq⟩
