/-
Extracted from Topology/MetricSpace/HolderNorm.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Hölder norm

This file defines the Hölder (semi-)norm for Hölder functions alongside some basic properties.
The `r`-Hölder norm of a function `f : X → Y` between two metric spaces is the least non-negative
real number `C` for which `f` is `r`-Hölder continuous with constant `C`, i.e. it is the least `C`
for which `WithHolder C r f` is true.

## Main definitions

* `eHolderNorm r f`: `r`-Hölder (semi-)norm in `ℝ≥0∞` of a function `f`.
* `nnHolderNorm r f`: `r`-Hölder (semi-)norm in `ℝ≥0` of a function `f`.
* `MemHolder r f`: Predicate for a function `f` being `r`-Hölder continuous.

## Main results

* `eHolderNorm_eq_zero`: the Hölder norm of a function is zero if and only if it is constant.
* `MemHolder.holderWith`: The Hölder norm of a Hölder function `f` is a Hölder constant of `f`.

## Tags

Hölder norm, Hoelder norm, Holder norm

-/

variable {X Y : Type*}

open Filter Set

open NNReal ENNReal Topology

section PseudoEMetricSpace

variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y] {r : ℝ≥0} {f : X → Y}

noncomputable

def eHolderNorm (r : ℝ≥0) (f : X → Y) : ℝ≥0∞ := ⨅ (C) (_ : HolderWith C r f), C

noncomputable

def nnHolderNorm (r : ℝ≥0) (f : X → Y) : ℝ≥0 := (eHolderNorm r f).toNNReal

def MemHolder (r : ℝ≥0) (f : X → Y) : Prop := ∃ C, HolderWith C r f

lemma HolderWith.memHolder {C : ℝ≥0} (hf : HolderWith C r f) : MemHolder r f := ⟨C, hf⟩
