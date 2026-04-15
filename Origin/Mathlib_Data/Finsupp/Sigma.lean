/-
Extracted from Data/Finsupp/Sigma.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Embedding a finitely supported function into a sigma type summand

This file provides `Finsupp.embSigma`, which embeds a finitely supported function `ι k →₀ M`
into the corresponding summand of `(Σ k, ι k) →₀ M`.

## Main declarations

* `Finsupp.embSigma`: Embed `ι k →₀ M` into `(Σ k, ι k) →₀ M` for a specific `k`.

## Implementation notes

This is a special case of `Finsupp.embDomain` using `Function.Embedding.sigmaMk`.
-/

noncomputable section

open Function

variable {κ : Type*} {ι : κ → Type*} {M : Type*}

namespace Finsupp

section EmbSigma

variable [Zero M]

def embSigma {k : κ} (f : ι k →₀ M) : (Σ k, ι k) →₀ M :=
  embDomain (Embedding.sigmaMk k) f
