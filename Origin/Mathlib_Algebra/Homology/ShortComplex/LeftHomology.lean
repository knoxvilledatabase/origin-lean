/-
Extracted from Algebra/Homology/ShortComplex/LeftHomology.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Left Homology of short complexes

Given a short complex `S : ShortComplex C`, which consists of two composable
maps `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` such that `f ≫ g = 0`, we shall define
here the "left homology" `S.leftHomology` of `S`. For this, we introduce the
notion of "left homology data". Such an `h : S.LeftHomologyData` consists of the
data of morphisms `i : K ⟶ X₂` and `π : K ⟶ H` such that `i` identifies
`K` with the kernel of `g : X₂ ⟶ X₃`, and that `π` identifies `H` with the cokernel
of the induced map `f' : X₁ ⟶ K`.

When such a `S.LeftHomologyData` exists, we shall say that `[S.HasLeftHomology]`
and we define `S.leftHomology` to be the `H` field of a chosen left homology data.
Similarly, we define `S.cycles` to be the `K` field.

The dual notion is defined in `RightHomologyData.lean`. In `Homology.lean`,
when `S` has two compatible left and right homology data (i.e. they give
the same `H` up to a canonical isomorphism), we shall define `[S.HasHomology]`
and `S.homology`.

-/

namespace CategoryTheory

open Category Limits

namespace ShortComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

structure LeftHomologyData where
  /-- a choice of kernel of `S.g : S.X₂ ⟶ S.X₃` -/
  K : C
  /-- a choice of cokernel of the induced morphism `S.f' : S.X₁ ⟶ K` -/
  H : C
  /-- the inclusion of cycles in `S.X₂` -/
  i : K ⟶ S.X₂
  /-- the projection from cycles to the (left) homology -/
  π : K ⟶ H
  /-- the kernel condition for `i` -/
  wi : i ≫ S.g = 0
  /-- `i : K ⟶ S.X₂` is a kernel of `g : S.X₂ ⟶ S.X₃` -/
  hi : IsLimit (KernelFork.ofι i wi)
  /-- the cokernel condition for `π` -/
  wπ : hi.lift (KernelFork.ofι _ S.zero) ≫ π = 0
  /-- `π : K ⟶ H` is a cokernel of the induced morphism `S.f' : S.X₁ ⟶ K` -/
  hπ : IsColimit (CokernelCofork.ofπ π wπ)

initialize_simps_projections LeftHomologyData (-hi, -hπ)

namespace LeftHomologyData

set_option backward.isDefEq.respectTransparency false in
