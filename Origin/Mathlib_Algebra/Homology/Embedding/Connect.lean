/-
Extracted from Algebra/Homology/Embedding/Connect.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Connecting a chain complex and a cochain complex

Given a chain complex `K`: `... ⟶ K.X 2 ⟶ K.X 1 ⟶ K.X 0`,
a cochain complex `L`: `L.X 0 ⟶ L.X 1 ⟶ L.X 2 ⟶ ...`,
a morphism `d₀ : K.X 0 ⟶ L.X 0` satisfying the identifies `K.d 1 0 ≫ d₀ = 0`
and `d₀ ≫ L.d 0 1 = 0`, we construct a cochain complex indexed by `ℤ` of the form
`... ⟶ K.X 2 ⟶ K.X 1 ⟶ K.X 0 ⟶ L.X 0 ⟶ L.X 1 ⟶ L.X 2 ⟶ ...`,
where `K.X 0` lies in degree `-1` and `L.X 0` in degree `0`.

## Main definitions

Say `K : ChainComplex C ℕ` and `L : CochainComplex C ℕ`, so `... ⟶ K₂ ⟶ K₁ ⟶ K₀`
and `L⁰ ⟶ L¹ ⟶ L² ⟶ ...`.

* `ConnectData K L`: an auxiliary structure consisting of `d₀ : K₀ ⟶ L⁰` "connecting" the
  complexes and proofs that the induced maps `K₁ ⟶ K₀ ⟶ L⁰` and `K₀ ⟶ L⁰ ⟶ L¹` are both zero.

Now say `h : ConnectData K L`.

* `CochainComplex.ConnectData.cochainComplex h` : the induced ℤ-indexed complex
  `... ⟶ K₁ ⟶ K₀ ⟶ L⁰ ⟶ L¹ ⟶ ...`
* `CochainComplex.ConnectData.homologyIsoPos h (n : ℕ) (m : ℤ)` : if `m = n + 1`,
  the isomorphism `h.cochainComplex.homology m ≅ L.homology (n + 1)`
* `CochainComplex.ConnectData.homologyIsoNeg h (n : ℕ) (m : ℤ)` : if `m = -(n + 2)`,
  the isomorphism `h.cochainComplex.homology m ≅ K.homology (n + 1)`

## TODO

* Computation of `h.cochainComplex.homology k` when `k = 0` or `k = -1`.

-/

universe v u

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

namespace CochainComplex

variable {K K' K'' : ChainComplex C ℕ} {L L' L'' : CochainComplex C ℕ}

variable (K L) in

structure ConnectData where
  /-- the differential which connect `K` and `L` -/
  d₀ : K.X 0 ⟶ L.X 0
  comp_d₀ : K.d 1 0 ≫ d₀ = 0
  d₀_comp : d₀ ≫ L.d 0 1 = 0

namespace ConnectData

attribute [reassoc (attr := simp)] comp_d₀ d₀_comp

variable (h : ConnectData K L) (h' : ConnectData K' L') (h'' : ConnectData K'' L'')

variable (K L) in

def X : ℤ → C
  | .ofNat n => L.X n
  | .negSucc n => K.X n
