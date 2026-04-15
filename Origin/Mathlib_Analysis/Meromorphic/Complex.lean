/-
Extracted from Analysis/Meromorphic/Complex.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Gamma function is meromorphic
-/

open Set Complex

lemma MeromorphicNFOn.Gamma : MeromorphicNFOn Gamma univ :=
  meromorphicNFOn_inv.mp <| AnalyticOnNhd.meromorphicNFOn <|
    analyticOnNhd_univ_iff_differentiable.mpr differentiable_one_div_Gamma

lemma Meromorphic.Gamma : Meromorphic Gamma :=
  meromorphicOn_univ.mp MeromorphicNFOn.Gamma.meromorphicOn

lemma MeromorphicOn.Gamma {s} : MeromorphicOn Gamma s :=
  Meromorphic.Gamma.meromorphicOn
