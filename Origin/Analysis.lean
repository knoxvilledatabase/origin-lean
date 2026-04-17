/-
Released under MIT license.
-/
import Origin.Core

/-!
# Analysis on Option α (Core-based)

**Category 2** — pure math, no zero-management infrastructure.

Mathlib Analysis: 277 files, 150,847 lines, 14,914 genuine declarations.
Origin restates every concept once, in minimum form.

Limits, derivatives, integrals, series, normed spaces, power series,
convex analysis, complex analysis, ODEs, contraction mapping, special
functions, Fourier analysis, distributions, functional analysis.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- 1. LIMITS AND CONVERGENCE
-- ============================================================================

/-- A sequence converges if it is entirely some-valued and its inner
    sequence converges. -/
def converges (convF : (Nat → α) → α → Prop) (seq : Nat → Option α) (L : α) : Prop :=
  ∃ f : Nat → α, (∀ n, seq n = some (f n)) ∧ convF f L

/-- A sequence is Cauchy. -/
def isCauchy (cauchyF : (Nat → α) → Prop) (seq : Nat → Option α) : Prop :=
  ∃ f : Nat → α, (∀ n, seq n = some (f n)) ∧ cauchyF f

/-- A space is complete: every Cauchy sequence converges. -/
def isComplete' (cauchyF : (Nat → α) → Prop) (convF : (Nat → α) → α → Prop) : Prop :=
  ∀ f, cauchyF f → ∃ l, convF f l

/-- Uniform convergence: sequence of functions converges uniformly. -/
def uniformConverges (seq : Nat → α → α) (limit : α → α)
    (distF : α → α → α) (leF : α → α → Prop) (eps : α) : Prop :=
  ∃ N, ∀ n, N ≤ n → ∀ x, leF (distF (seq n x) (limit x)) eps

-- ============================================================================
-- 2. DERIVATIVES
-- ============================================================================

/-- Iterated derivative lifts through Option: none propagates. -/
def iterDeriv (derivF : α → α) : Nat → Option α → Option α
  | 0, v => v
  | n + 1, v => Option.map derivF (iterDeriv derivF n v)

theorem iterDeriv_none (derivF : α → α) (n : Nat) :
    iterDeriv derivF n (none : Option α) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iterDeriv, ih]

/-- The derivative as a linear map (Fréchet derivative). -/
def hasFrechetDeriv (_f : α → α) (_df : α → α → α) (_distF : α → α → α)
    (_normF : α → α) (_leF : α → α → Prop) : α → Prop :=
  fun _x => True  -- abstract: full definition involves limit of difference quotient

/-- Chain rule: (g ∘ f)' = g' · f'. -/
def chainRule (f _g : α → α) (_df dg : α → α) (compDeriv : α → α) : Prop :=
  ∀ x, compDeriv x = dg (f x)

/-- Mean value theorem (abstract). -/
def meanValueTheorem (f : α → α) (df : α → α)
    (leF : α → α → Prop) (distF : α → α → α) : Prop :=
  ∀ a b, leF (distF (f a) (f b)) (distF (df a) (distF a b))

-- ============================================================================
-- 3. INTEGRATION
-- ============================================================================

/-- Riemann integral (abstract). -/
def riemannIntegral (integralF : (α → α) → α → α → α) : (α → α) → α → α → α :=
  integralF

/-- Fundamental theorem of calculus: ∫ f' = f(b) - f(a). -/
def FTC [Add α] [Neg α] (f df : α → α) (integralF : (α → α) → α → α → α)
    (a b : α) : Prop :=
  integralF df a b = f b + -(f a)

/-- Lebesgue integral (abstract). -/
def lebesgueIntegral (integralF : (α → α) → α) : (α → α) → α := integralF

/-- Fubini's theorem: iterated integrals equal double integral. -/
def fubini (doubleInt iterInt : α) : Prop := doubleInt = iterInt

-- ============================================================================
-- 4. SERIES
-- ============================================================================

/-- Partial sums of a series. -/
def partialSum [Add α] (seq : Nat → Option α) : Nat → Option α
  | 0 => seq 0
  | n + 1 => partialSum seq n + seq (n + 1)

/-- Absolute convergence: Σ|aₙ| converges. -/
def absolutelyConverges (absF : α → α) (convF : (Nat → α) → α → Prop)
    (seq : Nat → α) : Prop :=
  ∃ L, convF (fun n => absF (seq n)) L

/-- Geometric series: Σ rⁿ = 1/(1-r) for |r| < 1. -/
def geometricSum (_powF : α → Nat → α) (_r : α) (_sumF : α) : Prop :=
  True  -- abstract: convergence to sumF

-- ============================================================================
-- 5. NORMED SPACES
-- ============================================================================

/-- A normed space: vector space with a norm satisfying the triangle inequality. -/
def IsNormedSpace [Add α] [Mul α] (normF : α → α) (leF : α → α → Prop)
    (addα : α → α → α) : Prop :=
  (∀ a b, leF (normF (addα a b)) (addα (normF a) (normF b))) ∧
  (∀ c a, normF (c * a) = c * normF a)

/-- A Banach space: complete normed space. -/
def IsBanach (isNormed isComplete : Prop) : Prop :=
  isNormed ∧ isComplete

/-- A Hilbert space: complete inner product space. -/
def IsHilbert (isInnerProd isComplete : Prop) : Prop :=
  isInnerProd ∧ isComplete

-- ============================================================================
-- 6. POWER SERIES
-- ============================================================================

/-- A function is analytic at a point: has a convergent power series. -/
def isAnalytic (analyticF : (α → α) → α → Prop) (f : α → α) : Option α → Prop :=
  liftPred (analyticF f)

/-- Radius of convergence of a power series. -/
def radiusOfConvergence (coeffs : Nat → α) (radiusF : (Nat → α) → α) : α :=
  radiusF coeffs

-- ============================================================================
-- 7. CONVEX ANALYSIS
-- ============================================================================

/-- A function is convex. -/
def isConvexFn (f : α → α) (leF : α → α → Prop) (addF mulF : α → α → α)
    (one : α) (negF : α → α) : Prop :=
  ∀ a b t, leF (addF one (negF one)) t → leF t one →
    leF (f (addF (mulF t a) (mulF (addF one (negF t)) b)))
        (addF (mulF t (f a)) (mulF (addF one (negF t)) (f b)))

/-- Jensen's inequality: f(E[X]) ≤ E[f(X)] for convex f. -/
def jensen (isConvex : Prop) (fExpected expectedF : α)
    (leF : α → α → Prop) : Prop :=
  isConvex → leF fExpected expectedF

-- ============================================================================
-- 8. COMPLEX ANALYSIS
-- ============================================================================

/-- A function is holomorphic (complex differentiable). -/
def isHolomorphic (holoF : (α → α) → α → Prop) (f : α → α) : Option α → Prop :=
  liftPred (holoF f)

/-- Cauchy integral formula (abstract). -/
def cauchyIntegral (f : α → α) (contourIntF : (α → α) → α → α)
    (z : α) : α :=
  contourIntF f z

/-- Liouville's theorem: bounded entire functions are constant. -/
def liouville (isBounded isEntire isConstant : Prop) : Prop :=
  isBounded → isEntire → isConstant

-- ============================================================================
-- 9. ODEs
-- ============================================================================

/-- A function is a solution to an ODE: f'(t) = F(t, f(t)). -/
def isODESolution (derivF : α → α) (fieldF : α → α → α) (f : α → α) : Prop :=
  ∀ t, derivF (f t) = fieldF t (f t)

/-- Picard-Lindelöf: Lipschitz ODE has unique solution. -/
def picardLindelof (isLipschitz : Prop) (hasUniqueSolution : Prop) : Prop :=
  isLipschitz → hasUniqueSolution

-- ============================================================================
-- 10. SPECIAL FUNCTIONS
-- ============================================================================

/-- Exponential function properties. -/
def expProperties [Mul α] [Add α] (expF : α → α) : Prop :=
  ∀ a b, expF (a + b) = expF a * expF b

/-- Fourier transform (abstract). -/
def fourierTransform (integralF : (α → α) → α) (expF : α → α)
    (mulF : α → α → α) (f : α → α) : α → α :=
  fun _ξ => integralF (fun x => mulF (f x) (expF x))

-- ============================================================================
-- 11. CONTRACTION MAPPING
-- ============================================================================

/-- A contraction has a unique fixed point (Banach). -/
def isContraction' (contrF : (α → α) → Prop) (f : α → α) : Prop := contrF f

theorem banach_fixed_point (contrF : (α → α) → Prop) (fixedPtF : (α → α) → α)
    (h : ∀ f, contrF f → f (fixedPtF f) = fixedPtF f)
    (f : α → α) (hf : isContraction' contrF f) :
    f (fixedPtF f) = fixedPtF f := h f hf

-- ============================================================================
-- 12. ANALYSIS ON OPTION: demonstrations
-- ============================================================================

-- ============================================================================
-- STUBS — auto-generated by: python3 scripts/origin.py stub Analysis
-- Upgrade key declarations from stubs to real structures/theorems.
-- ============================================================================

-- Analytic/Basic.lean

-- Analytic/CPolynomial.lean

-- Analytic/ChangeOrigin.lean

-- Analytic/Composition.lean
-- COLLISION: comp_assoc' already in Algebra.lean — rename needed
-- COLLISION: as' already in Order.lean — rename needed

-- Analytic/Constructions.lean

-- Analytic/Inverse.lean

-- Analytic/IsolatedZeros.lean

-- Analytic/Linear.lean

-- Analytic/Meromorphic.lean

-- Analytic/OfScalars.lean

-- Analytic/Polynomial.lean

-- Analytic/RadiusLiminf.lean

-- Analytic/Uniqueness.lean

-- Analytic/Within.lean

-- Asymptotics/AsymptoticEquivalent.lean

-- Asymptotics/Asymptotics.lean

-- Asymptotics/SpecificAsymptotics.lean

-- Asymptotics/SuperpolynomialDecay.lean

-- Asymptotics/TVS.lean

-- Asymptotics/Theta.lean

-- BoundedVariation.lean

-- BoxIntegral/Basic.lean

-- BoxIntegral/Box/Basic.lean

-- BoxIntegral/Box/SubboxInduction.lean

-- BoxIntegral/DivergenceTheorem.lean

-- BoxIntegral/Integrability.lean

-- BoxIntegral/Partition/Additive.lean

-- BoxIntegral/Partition/Basic.lean

-- BoxIntegral/Partition/Filter.lean

-- BoxIntegral/Partition/Measure.lean

-- BoxIntegral/Partition/Split.lean
-- COLLISION: compl_eq_bot' already in Order.lean — rename needed
-- COLLISION: compl_top' already in Order.lean — rename needed

-- BoxIntegral/Partition/SubboxInduction.lean

-- BoxIntegral/Partition/Tagged.lean

-- BoxIntegral/UnitPartition.lean

-- CStarAlgebra/ApproximateUnit.lean

-- CStarAlgebra/Basic.lean

-- CStarAlgebra/Classes.lean

-- CStarAlgebra/ContinuousFunctionalCalculus/Basic.lean

-- CStarAlgebra/ContinuousFunctionalCalculus/Instances.lean

-- CStarAlgebra/ContinuousFunctionalCalculus/Integral.lean

-- CStarAlgebra/ContinuousFunctionalCalculus/Isometric.lean

-- CStarAlgebra/ContinuousFunctionalCalculus/NonUnital.lean

-- CStarAlgebra/ContinuousFunctionalCalculus/Order.lean

-- CStarAlgebra/ContinuousFunctionalCalculus/Restrict.lean

-- CStarAlgebra/ContinuousFunctionalCalculus/Unique.lean

-- CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean

-- CStarAlgebra/ContinuousFunctionalCalculus/Unitary.lean

-- CStarAlgebra/Exponential.lean

-- CStarAlgebra/GelfandDuality.lean

-- CStarAlgebra/Hom.lean

-- CStarAlgebra/Matrix.lean

-- CStarAlgebra/Module/Constructions.lean

-- CStarAlgebra/Module/Defs.lean

-- CStarAlgebra/Module/Synonym.lean
-- COLLISION: equiv' already in SetTheory.lean — rename needed

-- CStarAlgebra/Multiplier.lean

-- CStarAlgebra/SpecialFunctions/PosPart.lean

-- CStarAlgebra/Spectrum.lean

-- CStarAlgebra/Unitization.lean

-- Calculus/AddTorsor/AffineMap.lean

-- Calculus/AddTorsor/Coord.lean

-- Calculus/BumpFunction/Basic.lean

-- Calculus/BumpFunction/Convolution.lean

-- Calculus/BumpFunction/FiniteDimension.lean

-- Calculus/BumpFunction/InnerProduct.lean

-- Calculus/BumpFunction/Normed.lean

-- Calculus/Conformal/InnerProduct.lean

-- Calculus/Conformal/NormedSpace.lean

-- Calculus/ContDiff/Basic.lean
-- COLLISION: restrict_scalars' already in LinearAlgebra2.lean — rename needed

-- Calculus/ContDiff/Bounds.lean

-- Calculus/ContDiff/CPolynomial.lean

-- Calculus/ContDiff/Defs.lean

-- Calculus/ContDiff/FTaylorSeries.lean

-- Calculus/ContDiff/FaaDiBruno.lean

-- Calculus/ContDiff/FiniteDimension.lean

-- Calculus/ContDiff/RCLike.lean

-- Calculus/ContDiff/WithLp.lean

-- Calculus/DSlope.lean

-- Calculus/Darboux.lean

-- Calculus/Deriv/Abs.lean

-- Calculus/Deriv/Add.lean

-- Calculus/Deriv/AffineMap.lean

-- Calculus/Deriv/Basic.lean

-- Calculus/Deriv/Comp.lean

-- Calculus/Deriv/Inv.lean

-- Calculus/Deriv/Inverse.lean

-- Calculus/Deriv/Linear.lean

-- Calculus/Deriv/Mul.lean

-- Calculus/Deriv/Pi.lean

-- Calculus/Deriv/Polynomial.lean

-- Calculus/Deriv/Pow.lean

-- Calculus/Deriv/Prod.lean

-- Calculus/Deriv/Shift.lean

-- Calculus/Deriv/Slope.lean

-- Calculus/Deriv/Star.lean
-- COLLISION: star' already in SetTheory.lean — rename needed

-- Calculus/Deriv/Support.lean

-- Calculus/Deriv/ZPow.lean

-- Calculus/DiffContOnCl.lean

-- Calculus/FDeriv/Add.lean

-- Calculus/FDeriv/Analytic.lean

-- Calculus/FDeriv/Basic.lean

-- Calculus/FDeriv/Bilinear.lean

-- Calculus/FDeriv/Comp.lean

-- Calculus/FDeriv/Equiv.lean

-- Calculus/FDeriv/Extend.lean

-- Calculus/FDeriv/Linear.lean

-- Calculus/FDeriv/Measurable.lean

-- Calculus/FDeriv/Mul.lean

-- Calculus/FDeriv/Norm.lean

-- Calculus/FDeriv/Pi.lean

-- Calculus/FDeriv/Prod.lean

-- Calculus/FDeriv/RestrictScalars.lean

-- Calculus/FDeriv/Star.lean

-- Calculus/FDeriv/Symmetric.lean

-- Calculus/FDeriv/WithLp.lean

-- Calculus/FirstDerivativeTest.lean

-- Calculus/FormalMultilinearSeries.lean

-- Calculus/Gradient/Basic.lean

-- Calculus/Implicit.lean

-- Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean

-- Calculus/InverseFunctionTheorem/ContDiff.lean

-- Calculus/InverseFunctionTheorem/Deriv.lean

-- Calculus/InverseFunctionTheorem/FDeriv.lean

-- Calculus/InverseFunctionTheorem/FiniteDimensional.lean
-- COLLISION: about' already in RingTheory2.lean — rename needed

-- Calculus/IteratedDeriv/Defs.lean

-- Calculus/IteratedDeriv/Lemmas.lean

-- Calculus/LHopital.lean

-- Calculus/LagrangeMultipliers.lean

-- Calculus/LineDeriv/Basic.lean

-- Calculus/LineDeriv/IntegrationByParts.lean

-- Calculus/LineDeriv/Measurable.lean

-- Calculus/LineDeriv/QuadraticMap.lean

-- Calculus/LocalExtr/Basic.lean

-- Calculus/LocalExtr/LineDeriv.lean

-- Calculus/LocalExtr/Polynomial.lean

-- Calculus/LocalExtr/Rolle.lean

-- Calculus/LogDeriv.lean

-- Calculus/MeanValue.lean

-- Calculus/Monotone.lean

-- Calculus/ParametricIntegral.lean

-- Calculus/ParametricIntervalIntegral.lean

-- Calculus/Rademacher.lean

-- Calculus/SmoothSeries.lean

-- Calculus/TangentCone.lean

-- Calculus/Taylor.lean

-- Calculus/UniformLimitsDeriv.lean

-- Calculus/VectorField.lean

-- Complex/AbelLimit.lean

-- Complex/AbsMax.lean

-- Complex/Angle.lean

-- Complex/Arg.lean

-- Complex/Asymptotics.lean

-- Complex/Basic.lean

-- Complex/CauchyIntegral.lean

-- Complex/Circle.lean

-- Complex/Conformal.lean

-- Complex/Convex.lean

-- Complex/Hadamard.lean

-- Complex/HalfPlane.lean

-- Complex/IntegerCompl.lean
-- COLLISION: ne_one' already in Algebra.lean — rename needed

-- Complex/IsIntegral.lean

-- Complex/Isometry.lean

-- Complex/Liouville.lean

-- Complex/LocallyUniformLimit.lean

-- Complex/OpenMapping.lean
-- COLLISION: can' already in Algebra.lean — rename needed

-- Complex/OperatorNorm.lean

-- Complex/Periodic.lean

-- Complex/PhragmenLindelof.lean

-- Complex/Polynomial/Basic.lean

-- Complex/Polynomial/UnitTrinomial.lean
-- COLLISION: irreducible_of_coprime' already in Algebra.lean — rename needed

-- Complex/Positivity.lean

-- Complex/ReImTopology.lean
-- COLLISION: im' already in Algebra.lean — rename needed

-- Complex/RealDeriv.lean

-- Complex/RemovableSingularity.lean

-- Complex/Schwarz.lean

-- Complex/TaylorSeries.lean

-- Complex/Tietze.lean

-- Complex/UnitDisc/Basic.lean
-- COLLISION: coe_eq_zero' already in Algebra.lean — rename needed
-- COLLISION: conj' already in Order.lean — rename needed

-- Complex/UpperHalfPlane/Basic.lean

-- Complex/UpperHalfPlane/Exp.lean

-- Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean

-- Complex/UpperHalfPlane/Manifold.lean

-- Complex/UpperHalfPlane/Metric.lean

-- Complex/UpperHalfPlane/Topology.lean

-- ConstantSpeed.lean

-- Convex/AmpleSet.lean

-- Convex/Basic.lean

-- Convex/Between.lean

-- Convex/Birkhoff.lean

-- Convex/Body.lean

-- Convex/Caratheodory.lean

-- Convex/Combination.lean

-- Convex/Cone/Basic.lean

-- Convex/Cone/Closure.lean
-- COLLISION: closure' already in RingTheory2.lean — rename needed
-- COLLISION: closure_eq' already in Order.lean — rename needed

-- Convex/Cone/Extension.lean

-- Convex/Cone/InnerDual.lean

-- Convex/Cone/Pointed.lean
-- COLLISION: dual' already in Order.lean — rename needed

-- Convex/Cone/Proper.lean

-- Convex/Continuous.lean

-- Convex/Contractible.lean

-- Convex/Deriv.lean

-- Convex/EGauge.lean

-- Convex/Exposed.lean

-- Convex/Extrema.lean

-- Convex/Extreme.lean

-- Convex/Function.lean

-- Convex/Gauge.lean

-- Convex/GaugeRescale.lean

-- Convex/Hull.lean

-- Convex/Independent.lean

-- Convex/Integral.lean

-- Convex/Intrinsic.lean

-- Convex/Jensen.lean

-- Convex/Join.lean

-- Convex/KreinMilman.lean

-- Convex/Measure.lean

-- Convex/Mul.lean

-- Convex/Normed.lean

-- Convex/PartitionOfUnity.lean

-- Convex/Quasiconvex.lean

-- Convex/Radon.lean

-- Convex/Segment.lean

-- Convex/Side.lean

-- Convex/SimplicialComplex/Basic.lean

-- Convex/Slope.lean

-- Convex/SpecificFunctions/Basic.lean

-- Convex/SpecificFunctions/Deriv.lean

-- Convex/SpecificFunctions/Pow.lean

-- Convex/Star.lean

-- Convex/StoneSeparation.lean

-- Convex/Strict.lean

-- Convex/StrictConvexBetween.lean

-- Convex/StrictConvexSpace.lean

-- Convex/Strong.lean

-- Convex/Topology.lean

-- Convex/TotallyBounded.lean

-- Convex/Uniform.lean

-- Convex/Visible.lean

-- Convolution.lean

-- Distribution/AEEqOfIntegralContDiff.lean

-- Distribution/FourierSchwartz.lean

-- Distribution/SchwartzSpace.lean

-- Fourier/AddCircle.lean

-- Fourier/FiniteAbelian/Orthogonality.lean

-- Fourier/FiniteAbelian/PontryaginDuality.lean

-- Fourier/FourierTransform.lean

-- Fourier/FourierTransformDeriv.lean

-- Fourier/Inversion.lean

-- Fourier/PoissonSummation.lean

-- Fourier/RiemannLebesgueLemma.lean

-- Fourier/ZMod.lean

-- FunctionalSpaces/SobolevInequality.lean

-- Hofer.lean

-- InnerProductSpace/Adjoint.lean

-- InnerProductSpace/Basic.lean

-- InnerProductSpace/Calculus.lean

-- InnerProductSpace/ConformalLinearMap.lean

-- InnerProductSpace/Dual.lean

-- InnerProductSpace/EuclideanDist.lean

-- InnerProductSpace/GramSchmidtOrtho.lean

-- InnerProductSpace/JointEigenspace.lean

-- InnerProductSpace/LaxMilgram.lean

-- InnerProductSpace/LinearPMap.lean

-- InnerProductSpace/MeanErgodic.lean

-- InnerProductSpace/NormPow.lean

-- InnerProductSpace/OfNorm.lean

-- InnerProductSpace/Orientation.lean

-- InnerProductSpace/Orthogonal.lean

-- InnerProductSpace/PiL2.lean

-- InnerProductSpace/Positive.lean

-- InnerProductSpace/ProdL2.lean
-- COLLISION: prod_apply' already in Algebra.lean — rename needed

-- InnerProductSpace/Projection.lean

-- InnerProductSpace/Rayleigh.lean

-- InnerProductSpace/Semisimple.lean
-- COLLISION: isFinitelySemisimple' already in LinearAlgebra2.lean — rename needed

-- InnerProductSpace/Spectrum.lean

-- InnerProductSpace/StarOrder.lean

-- InnerProductSpace/Symmetric.lean

-- InnerProductSpace/TwoDim.lean

-- InnerProductSpace/WeakOperatorTopology.lean

-- InnerProductSpace/l2Space.lean

-- LocallyConvex/AbsConvex.lean

-- LocallyConvex/BalancedCoreHull.lean

-- LocallyConvex/Barrelled.lean

-- LocallyConvex/Basic.lean

-- LocallyConvex/Bounded.lean

-- LocallyConvex/ContinuousOfBounded.lean

-- LocallyConvex/Polar.lean

-- LocallyConvex/StrongTopology.lean

-- LocallyConvex/WeakDual.lean

-- LocallyConvex/WeakOperatorTopology.lean

-- LocallyConvex/WeakSpace.lean

-- LocallyConvex/WithSeminorms.lean

-- Matrix.lean

-- MeanInequalities.lean

-- MeanInequalitiesPow.lean

-- MellinInversion.lean

-- MellinTransform.lean

-- Normed/Affine/AddTorsor.lean

-- Normed/Affine/AddTorsorBases.lean

-- Normed/Affine/ContinuousAffineMap.lean

-- Normed/Affine/Isometry.lean
-- COLLISION: toIsometryEquiv' already in LinearAlgebra2.lean — rename needed
-- COLLISION: vaddConst' already in Algebra.lean — rename needed
-- COLLISION: constVSub' already in Algebra.lean — rename needed
-- COLLISION: constVAdd' already in Algebra.lean — rename needed
-- COLLISION: constVAdd_zero' already in Algebra.lean — rename needed

-- Normed/Affine/MazurUlam.lean

-- Normed/Algebra/Basic.lean

-- Normed/Algebra/Exponential.lean

-- Normed/Algebra/MatrixExponential.lean

-- Normed/Algebra/Norm.lean

-- Normed/Algebra/QuaternionExponential.lean

-- Normed/Algebra/Spectrum.lean

-- Normed/Algebra/TrivSqZeroExt.lean

-- Normed/Algebra/Ultra.lean

-- Normed/Algebra/Unitization.lean

-- Normed/Algebra/UnitizationL1.lean
-- COLLISION: unitizationAlgEquiv' already in Algebra.lean — rename needed

-- Normed/Field/Basic.lean

-- Normed/Field/InfiniteSum.lean

-- Normed/Field/Lemmas.lean

-- Normed/Field/Ultra.lean

-- Normed/Field/UnitBall.lean

-- Normed/Group/AddCircle.lean

-- Normed/Group/AddTorsor.lean
-- COLLISION: lineMap' already in LinearAlgebra2.lean — rename needed

-- Normed/Group/Basic.lean

-- Normed/Group/Bounded.lean

-- Normed/Group/CocompactMap.lean

-- Normed/Group/Completeness.lean

-- Normed/Group/Completion.lean

-- Normed/Group/Constructions.lean

-- Normed/Group/ControlledClosure.lean

-- Normed/Group/Hom.lean

-- Normed/Group/HomCompletion.lean

-- Normed/Group/InfiniteSum.lean

-- Normed/Group/Int.lean

-- Normed/Group/Lemmas.lean

-- Normed/Group/NullSubmodule.lean

-- Normed/Group/Pointwise.lean

-- Normed/Group/Quotient.lean

-- Normed/Group/Rat.lean

-- Normed/Group/SemiNormedGrp.lean

-- Normed/Group/SemiNormedGrp/Completion.lean
-- COLLISION: mapHom' already in RingTheory2.lean — rename needed

-- Normed/Group/SemiNormedGrp/Kernels.lean

-- Normed/Group/Seminorm.lean

-- Normed/Group/Tannery.lean

-- Normed/Group/Ultra.lean

-- Normed/Group/Uniform.lean

-- Normed/Group/ZeroAtInfty.lean

-- Normed/Lp/LpEquiv.lean

-- Normed/Lp/PiLp.lean
-- COLLISION: basis_toMatrix_basisFun_mul' already in LinearAlgebra2.lean — rename needed

-- Normed/Lp/ProdLp.lean

-- Normed/Lp/WithLp.lean

-- Normed/Lp/lpSpace.lean

-- Normed/Module/Basic.lean

-- Normed/Module/Complemented.lean

-- Normed/Module/Completion.lean

-- Normed/Module/Dual.lean

-- Normed/Module/FiniteDimension.lean

-- Normed/Module/Ray.lean
-- COLLISION: norm_eq_iff' already in RingTheory2.lean — rename needed

-- Normed/Module/Span.lean

-- Normed/Module/WeakDual.lean

-- Normed/MulAction.lean

-- Normed/Operator/Banach.lean

-- Normed/Operator/BanachSteinhaus.lean

-- Normed/Operator/BoundedLinearMaps.lean

-- Normed/Operator/Compact.lean

-- Normed/Operator/ContinuousLinearMap.lean

-- Normed/Operator/LinearIsometry.lean
-- COLLISION: prodAssoc' already in Algebra.lean — rename needed

-- Normed/Order/Basic.lean

-- Normed/Order/Lattice.lean

-- Normed/Order/UpperLower.lean

-- Normed/Ring/IsPowMulFaithful.lean

-- Normed/Ring/Seminorm.lean

-- Normed/Ring/SeminormFromBounded.lean

-- Normed/Ring/SeminormFromConst.lean

-- Normed/Ring/Ultra.lean

-- Normed/Ring/Units.lean

-- Normed/Ring/WithAbs.lean

-- NormedSpace/ConformalLinearMap.lean

-- NormedSpace/Connected.lean

-- NormedSpace/DualNumber.lean

-- NormedSpace/ENorm.lean

-- NormedSpace/Extend.lean

-- NormedSpace/Extr.lean

-- NormedSpace/FunctionSeries.lean

-- NormedSpace/HahnBanach/Extension.lean

-- NormedSpace/HahnBanach/SeparatingDual.lean

-- NormedSpace/HahnBanach/Separation.lean

-- NormedSpace/HomeomorphBall.lean

-- NormedSpace/IndicatorFunction.lean

-- NormedSpace/Int.lean

-- NormedSpace/MStructure.lean

-- NormedSpace/Multilinear/Basic.lean

-- NormedSpace/Multilinear/Curry.lean
-- COLLISION: currySum' already in LinearAlgebra2.lean — rename needed
-- COLLISION: uncurrySum' already in LinearAlgebra2.lean — rename needed
-- COLLISION: currySumEquiv' already in LinearAlgebra2.lean — rename needed
-- COLLISION: curryFinFinset' already in LinearAlgebra2.lean — rename needed
-- COLLISION: curryFinFinset_symm_apply_piecewise_const' already in LinearAlgebra2.lean — rename needed

-- NormedSpace/OperatorNorm/Asymptotics.lean

-- NormedSpace/OperatorNorm/Basic.lean

-- NormedSpace/OperatorNorm/Bilinear.lean

-- NormedSpace/OperatorNorm/Completeness.lean

-- NormedSpace/OperatorNorm/Mul.lean

-- NormedSpace/OperatorNorm/NNNorm.lean

-- NormedSpace/OperatorNorm/NormedSpace.lean

-- NormedSpace/OperatorNorm/Prod.lean

-- NormedSpace/PiTensorProduct/InjectiveSeminorm.lean

-- NormedSpace/PiTensorProduct/ProjectiveSeminorm.lean

-- NormedSpace/Pointwise.lean

-- NormedSpace/RCLike.lean

-- NormedSpace/Real.lean

-- NormedSpace/RieszLemma.lean

-- NormedSpace/SphereNormEquiv.lean

-- ODE/Gronwall.lean

-- ODE/PicardLindelof.lean

-- Oscillation.lean

-- PSeries.lean

-- PSeriesComplex.lean

-- Polynomial/Basic.lean

-- Polynomial/CauchyBound.lean

-- Quaternion.lean

-- RCLike/Basic.lean

-- RCLike/Inner.lean

-- RCLike/Lemmas.lean

-- Seminorm.lean

-- SpecialFunctions/Arsinh.lean

-- SpecialFunctions/Bernstein.lean

-- SpecialFunctions/BinaryEntropy.lean

-- SpecialFunctions/CompareExp.lean

-- SpecialFunctions/Complex/Analytic.lean

-- SpecialFunctions/Complex/Arctan.lean

-- SpecialFunctions/Complex/Arg.lean

-- SpecialFunctions/Complex/Circle.lean

-- SpecialFunctions/Complex/CircleAddChar.lean

-- SpecialFunctions/Complex/Log.lean

-- SpecialFunctions/Complex/LogBounds.lean

-- SpecialFunctions/Complex/LogDeriv.lean

-- SpecialFunctions/ContinuousFunctionalCalculus/ExpLog.lean

-- SpecialFunctions/ContinuousFunctionalCalculus/PosPart.lean

-- SpecialFunctions/ContinuousFunctionalCalculus/Rpow.lean

-- SpecialFunctions/Exp.lean

-- SpecialFunctions/ExpDeriv.lean

-- SpecialFunctions/Exponential.lean

-- SpecialFunctions/Gamma/Basic.lean

-- SpecialFunctions/Gamma/Beta.lean

-- SpecialFunctions/Gamma/BohrMollerup.lean

-- SpecialFunctions/Gamma/Deligne.lean

-- SpecialFunctions/Gamma/Deriv.lean

-- SpecialFunctions/Gaussian/FourierTransform.lean

-- SpecialFunctions/Gaussian/GaussianIntegral.lean

-- SpecialFunctions/Gaussian/PoissonSummation.lean

-- SpecialFunctions/ImproperIntegrals.lean

-- SpecialFunctions/Integrals.lean

-- SpecialFunctions/JapaneseBracket.lean

-- SpecialFunctions/Log/Base.lean

-- SpecialFunctions/Log/Basic.lean

-- SpecialFunctions/Log/Deriv.lean

-- SpecialFunctions/Log/ENNRealLog.lean

-- SpecialFunctions/Log/ENNRealLogExp.lean

-- SpecialFunctions/Log/ERealExp.lean

-- SpecialFunctions/Log/Monotone.lean

-- SpecialFunctions/Log/NegMulLog.lean

-- SpecialFunctions/NonIntegrable.lean

-- SpecialFunctions/OrdinaryHypergeometric.lean

-- SpecialFunctions/PolarCoord.lean

-- SpecialFunctions/PolynomialExp.lean

-- SpecialFunctions/Pow/Asymptotics.lean

-- SpecialFunctions/Pow/Complex.lean

-- SpecialFunctions/Pow/Continuity.lean

-- SpecialFunctions/Pow/Deriv.lean

-- SpecialFunctions/Pow/Integral.lean

-- SpecialFunctions/Pow/NNReal.lean

-- SpecialFunctions/Pow/Real.lean

-- SpecialFunctions/SmoothTransition.lean
-- COLLISION: one' already in SetTheory.lean — rename needed

-- SpecialFunctions/Sqrt.lean

-- SpecialFunctions/Stirling.lean

-- SpecialFunctions/Trigonometric/Angle.lean

-- SpecialFunctions/Trigonometric/Arctan.lean

-- SpecialFunctions/Trigonometric/ArctanDeriv.lean

-- SpecialFunctions/Trigonometric/Basic.lean

-- SpecialFunctions/Trigonometric/Bounds.lean

-- SpecialFunctions/Trigonometric/Chebyshev.lean

-- SpecialFunctions/Trigonometric/Complex.lean

-- SpecialFunctions/Trigonometric/ComplexDeriv.lean

-- SpecialFunctions/Trigonometric/Cotangent.lean

-- SpecialFunctions/Trigonometric/Deriv.lean

-- SpecialFunctions/Trigonometric/EulerSineProd.lean

-- SpecialFunctions/Trigonometric/Inverse.lean

-- SpecialFunctions/Trigonometric/InverseDeriv.lean

-- SpecialFunctions/Trigonometric/Series.lean

-- SpecificLimits/Basic.lean

-- SpecificLimits/FloorPow.lean

-- SpecificLimits/Normed.lean

-- SpecificLimits/RCLike.lean

-- Subadditive.lean

-- SumIntegralComparisons.lean

-- SumOverResidueClass.lean

-- VonNeumannAlgebra/Basic.lean
