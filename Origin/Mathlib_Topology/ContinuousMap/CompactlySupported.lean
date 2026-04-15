/-
Extracted from Topology/ContinuousMap/CompactlySupported.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Compactly supported continuous functions

In this file, we define the type `C_c(α, β)` of compactly supported continuous functions and the
class `CompactlySupportedContinuousMapClass`, and prove basic properties.

## Main definitions and results

This file contains various instances such as `Add`, `Mul`, `SMul F C_c(α, β)` when `F` is a class of
continuous functions.
When `β` has more structures, `C_c(α, β)` inherits such structures as `AddCommGroup`,
`NonUnitalRing` and `StarRing`.

When the domain `α` is compact, `CompactlySupportedContinuousMap.continuousMapEquiv`
gives the identification `C(α, β) ≃ C_c(α, β)`.

-/

variable {F α β γ : Type*} [TopologicalSpace α]

structure CompactlySupportedContinuousMap (α β : Type*) [TopologicalSpace α] [Zero β]
    [TopologicalSpace β] extends ContinuousMap α β where
  /-- The function has compact support . -/
  hasCompactSupport' : HasCompactSupport toFun
