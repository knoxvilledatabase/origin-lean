/-
Extracted from Analysis/Real/Hyperreal.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Construction of the hyperreal numbers as an ultraproduct of real sequences

We define the `Hyperreal` numbers as quotients of sequences `ℕ → ℝ` by an ultrafilter. These form
a field, and we prove some of their basic properties.

Note that most of the machinery that is usually defined for the specific purpose of non-standard
analysis (infinitesimal and infinite elements, standard parts) has been generalized to other
non-archimedean fields. In particular:

- `ArchimedeanClass` can be used to measure whether an element is infinitesimal (`0 < mk x`) or
  infinite (`mk x < 0`).
- `ArchimedeanClass.stdPart` generalizes the standard part function to a general ordered field.

## Todo

Use Łoś's Theorem `FirstOrder.Language.Ultraproduct.sentence_realize` to formalize the transfer
principle on `Hyperreal`.
-/

open ArchimedeanClass Filter Germ Topology

def Hyperreal : Type :=
  Germ (hyperfilter ℕ : Filter ℕ) ℝ

noncomputable section

#adaptation_note

namespace Hyperreal
