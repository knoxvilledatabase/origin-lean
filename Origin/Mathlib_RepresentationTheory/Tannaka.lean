/-
Extracted from RepresentationTheory/Tannaka.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Tannaka duality for finite groups

In this file we prove Tannaka duality for finite groups.

The theorem can be formulated as follows: for any integral domain `k`, a finite group `G` can be
recovered from `FDRep k G`, the monoidal category of finite-dimensional `k`-linear representations
of `G`, and the monoidal forgetful functor `forget : FDRep k G ⥤ FGModuleCat k`.

The main result is the isomorphism `equiv : G ≃* Aut (forget k G)`.

## Reference

<https://math.leidenuniv.nl/scripties/1bachCommelin.pdf>
-/

noncomputable section

open CategoryTheory MonoidalCategory ModuleCat Finset Pi

universe u

namespace TannakaDuality

namespace FiniteGroup

variable {k G : Type u} [CommRing k] [Group G]

section definitions

-- INSTANCE (free from Core): :

variable (k G) in

def forget := LaxMonoidalFunctor.of (forget₂ (FDRep k G) (FGModuleCat k))
