/-
Extracted from Algebra/Homology/ExactSequenceFour.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Exact sequences with four terms

The main definition in this file is `ComposableArrows.Exact.cokerIsoKer`:
given an exact sequence `S` (involving at least four objects),
this is the isomorphism from the cokernel of `S.map' k (k + 1)`
to the kernel of `S.map' (k + 2) (k + 3)`. This is intended
to be used for exact sequences in abelian categories, but the
construction works for preadditive balanced categories.

-/

namespace CategoryTheory

open Category Limits

namespace ComposableArrows

section HasZeroMorphisms

namespace IsComplex

variable {C : Type*} [Category C] [HasZeroMorphisms C] {n : ℕ} {S : ComposableArrows C (n + 3)}
  (hS : S.IsComplex) (k : ℕ)

set_option backward.isDefEq.respectTransparency false in

def cokerToKer' (hk : k ≤ n) (cc : CokernelCofork (S.map' k (k + 1)))
    (kf : KernelFork (S.map' (k + 2) (k + 3))) (hcc : IsColimit cc) (hkf : IsLimit kf) :
    cc.pt ⟶ kf.pt :=
  IsColimit.desc hcc (CokernelCofork.ofπ _
    (show S.map' k (k + 1) ≫ IsLimit.lift hkf (KernelFork.ofι _ (hS.zero (k + 1))) = _ from
      Fork.IsLimit.hom_ext hkf (by simpa using hS.zero k)))

set_option backward.isDefEq.respectTransparency false in
