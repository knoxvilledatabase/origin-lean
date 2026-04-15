/-
Extracted from Analysis/SpecialFunctions/Sigmoid.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Sigmoid function

In this file we define the sigmoid function `x : ℝ ↦ (1 + exp (-x))⁻¹` and prove some of
its analytic properties.

We then show that the sigmoid function can be seen as an order embedding from `ℝ` to `I = [0, 1]`
and that this embedding is both a topological embedding and a measurable embedding. We also prove
that the composition of this embedding with the measurable embedding from a standard Borel space
`α` to `ℝ` is a measurable embedding from `α` to `I`.

## Main definitions and results

### Sigmoid as a function from `ℝ` to `ℝ`
* `Real.sigmoid` : the sigmoid function from `ℝ` to `ℝ`.
* `Real.sigmoid_strictMono` : the sigmoid function is strictly monotone.
* `Real.continuous_sigmoid` : the sigmoid function is continuous.
* `Real.tendsto_sigmoid_atTop` : the sigmoid function tends to `1` at `+∞`.
* `Real.tendsto_sigmoid_atBot` : the sigmoid function tends to `0` at `-∞`.
* `Real.hasDerivAt_sigmoid` : the derivative of the sigmoid function.
* `Real.analyticAt_sigmoid` : the sigmoid function is analytic at every point.

### Sigmoid as a function from `ℝ` to `I`
* `unitInterval.sigmoid` : the sigmoid function from `ℝ` to `I`.
* `unitInterval.sigmoid_strictMono` : the sigmoid function is strictly monotone.
* `unitInterval.continuous_sigmoid` : the sigmoid function is continuous.
* `unitInterval.tendsto_sigmoid_atTop` : the sigmoid function tends to `1` at `+∞`.
* `unitInterval.tendsto_sigmoid_atBot` : the sigmoid function tends to `0` at `-∞`.

### Sigmoid as an `OrderEmbedding` from `ℝ` to `I`
* `OrderEmbedding.sigmoid` : the sigmoid function as an `OrderEmbedding` from `ℝ` to `I`.
* `Topology.isEmbedding_sigmoid` : the sigmoid function from `ℝ` to `I` is a topological
  embedding.
* `measurableEmbedding_sigmoid` : the sigmoid function from `ℝ` to `I` is a
  measurable embedding.
* `measurableEmbedding_sigmoid_comp_embeddingReal` : the composition of the
  sigmoid function from `ℝ` to `I` with the measurable embedding from a standard Borel
  space `α` to `ℝ` is a measurable embedding from `α` to `I`.

## Tags
sigmoid, embedding, measurable embedding, topological embedding
-/

namespace Real

noncomputable def sigmoid (x : ℝ) := (1 + exp (-x))⁻¹
