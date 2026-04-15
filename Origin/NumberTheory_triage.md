# Mathlib NumberTheory Domain Triage

228 files analyzed. Pattern: `≠ 0 | NeZero | ne_zero | GroupWithZero | .ne' | inv_ne_zero | cast_ne_zero | succ_ne_zero | pos_of_ne_zero`

## Full File List (sorted by HITS descending)

```
TYPE | HITS | THEOREMS | LINES | PATH
-----|------|----------|-------|-----
B    | 111  |  63      |   995 | Cyclotomic/Basic.lean
B    |  91  |  90      |   687 | Padics/PadicVal/Basic.lean
B    |  65  |  61      |   955 | NumberField/Cyclotomic/Basic.lean
B    |  49  |  44      |   623 | NumberField/CanonicalEmbedding/ConvexBody.lean
B    |  48  |  80      |   782 | LSeries/HurwitzZetaEven.lean
B    |  48  | 117      |   522 | Real/Irrational.lean
B    |  47  | 113      |   771 | Divisors.lean
B    |  45  |  92      |   928 | Height/Basic.lean
B    |  44  |  13      |   273 | FLT/Polynomial.lean
B    |  42  |  31      |   418 | LSeries/Nonvanishing.lean
B    |  40  |  62      |   517 | SmoothNumbers.lean
B    |  37  |  39      |   582 | Cyclotomic/PrimitiveRoots.lean
B    |  37  |  56      |   600 | LegendreSymbol/JacobiSymbol.lean
B    |  33  |  20      |   285 | RatFunc/Ostrowski.lean
B    |  32  |  34      |   663 | RamificationInertia/Basic.lean
B    |  28  |  70      |   420 | DirichletCharacter/Basic.lean
B    |  28  |  35      |   530 | LSeries/ZMod.lean
B    |  28  |  37      |   646 | PythagoreanTriples.lean
B    |  27  |  80      |   771 | FLT/Three.lean
B    |  26  |  14      |   243 | LSeries/HurwitzZetaValues.lean
B    |  26  |  35      |   356 | ModularForms/CongruenceSubgroups.lean
B    |  26  |  61      |   613 | NumberField/CanonicalEmbedding/FundamentalCone.lean
B    |  26  |  77      |   879 | NumberField/CanonicalEmbedding/NormLeOne.lean
B    |  26  |  29      |   480 | Ostrowski.lean
B    |  26  |  86      |   597 | Padics/PadicIntegers.lean
B    |  25  | 141      |  1240 | Padics/PadicNumbers.lean
B    |  25  |  40      |   484 | ZetaValues.lean
B    |  24  |  44      |   397 | LSeries/Basic.lean
B    |  24  |  24      |   515 | NumberField/Discriminant/Basic.lean
B    |  24  |  49      |   340 | Transcendental/Liouville/LiouvilleWith.lean
B    |  23  |  18      |   281 | FLT/Four.lean
B    |  23  |  31      |   397 | LSeries/DirichletContinuation.lean
B    |  23  |  30      |   305 | LegendreSymbol/Basic.lean
B    |  22  |  21      |   374 | ClassNumber/Finite.lean
B    |  22  |  31      |   428 | Harmonic/ZetaAsymp.lean
B    |  22  |  64      |  1005 | Modular.lean
B    |  22  |  60      |   670 | Pell.lean
B    |  21  |  67      |   470 | ArithmeticFunction/Misc.lean
B    |  21  |  34      |   362 | ArithmeticFunction/Moebius.lean
B    |  21  |  28      |   365 | Cyclotomic/CyclotomicCharacter.lean
B    |  20  |  48      |   444 | LSeries/Dirichlet.lean
B    |  20  |  36      |   381 | RamificationInertia/Ramification.lean
B    |  19  |  38      |   475 | LSeries/AbstractFuncEq.lean
B    |  19  |  56      |   568 | LSeries/HurwitzZetaOdd.lean
B    |  19  |  19      |   375 | LSeries/SumCoeff.lean
B    |  19  |  26      |   318 | LegendreSymbol/AddCharacter.lean
B    |  19  |  28      |   280 | LegendreSymbol/QuadraticChar/Basic.lean
B    |  18  |  35      |   477 | Chebyshev.lean
B    |  18  |  28      |   525 | LSeries/PrimesInAP.lean
B    |  18  |  43      |   443 | NumberField/Completion/FinitePlace.lean
B    |  18  |  30      |   386 | NumberField/Cyclotomic/Ideal.lean
B    |  18  |  40      |   526 | NumberField/Units/DirichletTheorem.lean
B    |  17  |  19      |   353 | JacobiSum/Basic.lean
B    |  17  |  19      |   221 | LegendreSymbol/GaussEisensteinLemmas.lean
B    |  17  |  52      |   478 | ModularForms/Cusps.lean
B    |  16  |  16      |   206 | EulerProduct/DirichletLSeries.lean
B    |  15  |  59      |   652 | ArithmeticFunction/Defs.lean
B    |  15  |  14      |   197 | ModularForms/Discriminant.lean
B    |  15  |  34      |   411 | Multiplicity.lean
B    |  14  |  13      |   246 | LSeries/Injectivity.lean
B    |  14  |  39      |   302 | ModularForms/EisensteinSeries/Summable.lean
B    |  14  |  62      |   492 | Padics/Hensel.lean
B    |  14  |  87      |   937 | PellMatiyasevic.lean
B    |  13  |  96      |   752 | LucasLehmer.lean
B    |  13  |  27      |   371 | NumberField/Units/Regulator.lean
B    |  13  |  34      |   320 | Padics/PadicNorm.lean
B    |  12  |  32      |   385 | Bernoulli.lean
B    |  12  |  24      |   259 | FLT/Basic.lean
B    |  12  |  14      |   233 | Harmonic/GammaDeriv.lean
B    |  12  |  25      |   232 | ModularForms/EisensteinSeries/Defs.lean
B    |  12  | 126      |  1231 | NumberField/CanonicalEmbedding/Basic.lean
B    |  12  |  15      |   220 | NumberField/ClassNumber.lean
B    |  12  |  10      |   222 | SiegelsLemma.lean
B    |  11  |  18      |   158 | ArithmeticFunction/VonMangoldt.lean
B    |  11  |  34      |   241 | FactorisationProperties.lean
B    |  11  |  23      |   356 | ModularForms/EisensteinSeries/QExpansion.lean
B    |  11  |  19      |   250 | MulChar/Lemmas.lean
B    |  11  |  32      |   367 | NumberField/House.lean
B    |  10  |  34      |   551 | DiophantineApproximation/Basic.lean
B    |  10  |  16      |   344 | GaussSum.lean
B    |  10  |  17      |   166 | ModularForms/DedekindEta.lean
B    |  10  |  26      |   274 | ModularForms/EisensteinSeries/E2/Summable.lean
B    |  10  |  62      |   543 | ModularForms/QExpansion.lean
B    |   9  |  17      |   163 | ArithmeticFunction/Carmichael.lean
B    |   9  |  33      |   239 | ArithmeticFunction/Zeta.lean
B    |   9  |  27      |   217 | Fermat.lean
B    |   9  |  19      |   208 | LSeries/Convolution.lean
B    |   9  |  15      |   238 | MahlerMeasure.lean
B    |   9  |  76      |   638 | NumberField/InfinitePlace/Basic.lean
B    |   9  |   3      |   102 | NumberField/ProductFormula.lean
B    |   9  |  31      |   383 | RamificationInertia/Galois.lean
B    |   8  |   7      |   253 | ClassNumber/AdmissibleCardPowDegree.lean
B    |   8  |   6      |   205 | Cyclotomic/Discriminant.lean
B    |   8  |  28      |   624 | Height/MvPolynomial.lean
B    |   8  |   5      |   156 | LSeries/MellinEqDirichlet.lean
B    |   8  |   2      |   174 | LocalField/Basic.lean
B    |   8  |  14      |   243 | ModularForms/ArithmeticSubgroups.lean
B    |   8  |   6      |   118 | NumberField/FractionalIdeal.lean
B    |   8  |  16      |   244 | SumTwoSquares.lean
B    |   7  |  11      |   329 | ArithmeticFunction/LFunction.lean
B    |   7  |   4      |    56 | Harmonic/Int.lean
B    |   7  |  14      |   102 | Height/Projectivization.lean
B    |   7  |  14      |   320 | ModularForms/Bounds.lean
B    |   7  |  15      |   232 | ModularForms/EisensteinSeries/E2/Transform.lean
B    |   7  |  12      |   127 | ModularForms/JacobiTheta/OneVariable.lean
B    |   7  |   5      |   141 | NumberField/Cyclotomic/Galois.lean
B    |   7  |  17      |   260 | NumberField/Ideal/KummerDedekind.lean
B    |   7  |  28      |   260 | NumberField/Units/Basic.lean
B    |   7  |  10      |   102 | Padics/PadicVal/Defs.lean
B    |   7  |  12      |   207 | Padics/WithVal.lean
B    |   7  |   3      |    72 | PrimesCongruentOne.lean
B    |   7  |  11      |   211 | SumFourSquares.lean
B    |   6  |   5      |   101 | FLT/MasonStothers.lean
B    |   6  |   3      |    68 | MaricaSchoenheim.lean
B    |   6  |  10      |   115 | ModularForms/LevelOne.lean
B    |   6  |  49      |   450 | NumberField/Basic.lean
B    |   6  |  73      |   775 | Padics/RingHoms.lean
B    |   6  |  32      |   240 | Real/GoldenRatio.lean
B    |   6  |  22      |   226 | SelbergSieve.lean
B    |   6  |  10      |   213 | Transcendental/Lindemann/AnalyticalPart.lean
B    |   6  |  11      |   221 | Transcendental/Liouville/Basic.lean
B    |   5  |  23      |   307 | BernoulliPolynomials.lean
B    |   5  |   4      |    66 | DirichletCharacter/GaussSum.lean
B    |   5  |   6      |    84 | DirichletCharacter/Orthogonality.lean
B    |   5  |  23      |   230 | FrobeniusNumber.lean
B    |   5  |  11      |   233 | KummerDedekind.lean
B    |   5  |  19      |   191 | LSeries/HurwitzZeta.lean
B    |   5  |  33      |   245 | LSeries/RiemannZeta.lean
B    |   5  |  13      |   104 | ModularForms/EisensteinSeries/E2/Defs.lean
B    |   5  |  13      |   177 | ModularForms/NormTrace.lean
B    |   5  |  62      |   599 | MulChar/Basic.lean
B    |   5  |  37      |   388 | Padics/MahlerBasis.lean
B    |   5  |  36      |   259 | Zsqrtd/GaussianInt.lean
B    |   4  |  18      |   399 | AbelSummation.lean
B    |   4  |   3      |   127 | ClassNumber/AdmissibleAbsoluteValue.lean
B    |   4  |  10      |   171 | LegendreSymbol/QuadraticReciprocity.lean
B    |   4  |  24      |   280 | ModularForms/JacobiTheta/Bounds.lean
B    |   4  |  46      |   533 | ModularForms/JacobiTheta/TwoVariable.lean
B    |   4  |  25      |   258 | ModularForms/SlashActions.lean
B    |   4  |  46      |   589 | NumberField/CMField.lean
B    |   4  |   3      |    69 | NumberField/Cyclotomic/Embeddings.lean
B    |   4  |   7      |   169 | NumberField/Discriminant/Different.lean
B    |   4  |   9      |   122 | NumberField/Ideal/Basic.lean
B    |   4  |   2      |    48 | Padics/ValuativeRel.lean
B    |   4  |  13      |   143 | TsumDivisorsAntidiagonal.lean
B    |   4  |  25      |   363 | WellApproximable.lean
B    |   4  |  11      |   102 | Wilson.lean
B    |   4  | 111      |   931 | Zsqrtd/Basic.lean
B    |   3  |   9      |   243 | Bertrand.lean
B    |   3  |  14      |   144 | LSeries/Convergence.lean
B    |   3  |  14      |   163 | LSeries/Deriv.lean
B    |   3  |   8      |    74 | LSeries/ZetaZeros.lean
B    |   3  |   5      |    75 | LucasPrimality.lean
B    |   3  |  25      |   188 | Niven.lean
B    |   3  |  39      |   467 | NumberField/CanonicalEmbedding/PolarCoord.lean
B    |   3  |   6      |    89 | NumberField/DedekindZeta.lean
B    |   3  |   5      |    84 | NumberField/EquivReindex.lean
B    |   3  |   5      |   159 | NumberField/Ideal/Asymptotics.lean
B    |   3  |  18      |   225 | RamificationInertia/HilbertTheory.lean
B    |   3  |   3      |    87 | Zsqrtd/QuadraticReciprocity.lean
B    |   2  |   6      |   165 | Cyclotomic/Gal.lean
B    |   2  |  71      |   552 | EllipticDivisibilitySequence.lean
B    |   2  |  23      |   352 | FermatPsp.lean
B    |   2  |  18      |   174 | Harmonic/EulerMascheroni.lean
B    |   2  |  15      |   159 | Height/NumberField.lean
B    |   2  |  28      |   167 | LSeries/Linearity.lean
B    |   2  |   7      |   112 | LegendreSymbol/QuadraticChar/GaussSum.lean
B    |   2  |   3      |    78 | ModularForms/EisensteinSeries/IsBoundedAtImInfty.lean
B    |   2  |   5      |    67 | ModularForms/EisensteinSeries/MDifferentiable.lean
B    |   2  |  15      |   143 | ModularForms/Petersson.lean
B    |   2  |  45      |   382 | NumberField/InfinitePlace/Embeddings.lean
B    |   2  |  11      |   123 | NumberField/Norm.lean
B    |   2  |  22      |   258 | Padics/Complex.lean
B    |   2  |  19      |   138 | Primorial.lean
B    |   2  |  17      |   185 | RamificationInertia/Inertia.lean
B    |   2  |  15      |   193 | Transcendental/Liouville/LiouvilleNumber.lean
B    |   2  |   6      |   124 | Transcendental/Liouville/Measure.lean
B    |   1  |   2      |    65 | ClassNumber/AdmissibleAbs.lean
B    |   1  |  77      |   704 | Dioph.lean
B    |   1  |   2      |    40 | DirichletCharacter/Bounds.lean
B    |   1  |   2      |    48 | EulerProduct/ExpLog.lean
B    |   1  |   5      |    76 | Harmonic/Bounds.lean
B    |   1  |   6      |   113 | LSeries/Positivity.lean
B    |   1  |  25      |   195 | LegendreSymbol/ZModChar.lean
B    |   1  |  63      |   671 | ModularForms/Basic.lean
B    |   1  |   2      |    50 | ModularForms/EisensteinSeries/Basic.lean
B    |   1  |   1      |    37 | ModularForms/EisensteinSeries/E2/MDifferentiable.lean
B    |   1  |  33      |   314 | ModularForms/SlashInvariantForms.lean
B    |   1  |   7      |   127 | NumberField/Discriminant/Defs.lean
B    |   1  |   8      |   135 | NumberField/InfiniteAdeleRing.lean
B    |   1  | 107      |   780 | NumberField/InfinitePlace/Ramification.lean
B    |   1  |  20      |   269 | Padics/HeightOneSpectrum.lean
B    |   1  |  19      |   144 | PrimeCounting.lean
B    |   1  |  19      |   180 | Rayleigh.lean
B    |   1  |   5      |    78 | Transcendental/Liouville/Residual.lean
A    |   0  |  26      |   255 | ADEInequality.lean
A    |   0  |   0      |     9 | ArithmeticFunction.lean
A    |   0  |   2      |    45 | Basic.lean
A    |   0  |   2      |    57 | ClassNumber/FunctionField.lean
A    |   0  |   2      |    61 | DiophantineApproximation/ContinuedFractions.lean
A    |   0  |  25      |   381 | EulerProduct/Basic.lean
A    |   0  |  10      |   199 | FunctionField.lean
A    |   0  |   3      |    31 | Harmonic/Defs.lean
A    |   0  |   3      |    52 | Height/Northcott.lean
A    |   0  |  16      |   124 | ModularForms/BoundedAtCusp.lean
A    |   0  |   0      |     8 | ModularForms/Delta.lean
A    |   0  |  17      |   174 | ModularForms/Derivative.lean
A    |   0  |   4      |    70 | ModularForms/EisensteinSeries/UniformConvergence.lean
A    |   0  |   5      |    68 | ModularForms/Identities.lean
A    |   0  |   1      |    29 | ModularForms/JacobiTheta/Manifold.lean
A    |   0  |  11      |   136 | MulChar/Duality.lean
A    |   0  |   4      |    81 | NumberField/AdeleRing.lean
A    |   0  |  32      |   295 | NumberField/Completion/InfinitePlace.lean
A    |   0  |   0      |    46 | NumberField/Completion/LiesOverInstances.lean
A    |   0  |   8      |   126 | NumberField/Completion/Ramification.lean
A    |   0  |   2      |    61 | NumberField/Cyclotomic/PID.lean
A    |   0  |  15      |   209 | NumberField/Cyclotomic/Three.lean
A    |   0  |   0      |    10 | NumberField/FinitePlaces.lean
A    |   0  |   0      |    10 | NumberField/InfinitePlace/Completion.lean
A    |   0  |  21      |   246 | NumberField/InfinitePlace/TotallyRealComplex.lean
A    |   0  |  14      |   140 | Padics/AddChar.lean
A    |   0  |   1      |    71 | Padics/ProperSpace.lean
A    |   0  |   6      |    55 | PowModTotient.lean
A    |   0  |   4      |   100 | RamificationInertia/Unramified.lean
A    |   0  |   5      |   102 | SumPrimeReciprocals.lean
A    |   0  |   0      |    10 | TsumDivsorsAntidiagonal.lean
A    |   0  |   0      |     6 | VonMangoldt.lean
A    |   0  |   3      |    34 | Zsqrtd/ToReal.lean
```

## Summary Statistics

### Type A (0 zero-management hits): 33 files, 3,301 lines

These files contain no zero-management patterns. They would be unaffected by
the foundational change.

### Type B (>0 zero-management hits): 195 files, 65,553 lines, 2,488 total hits

These files contain at least one zero-management pattern.

| Metric | Value |
|--------|-------|
| Type B files | 195 / 228 (85.5%) |
| Type B lines | 65,553 / 68,854 (95.2%) |
| Total zero-management hits | 2,488 |
| Average hits per Type B file | 12.8 |

### Top 10 Most Affected Files

| Rank | HITS | THEOREMS | LINES | PATH |
|------|------|----------|-------|------|
| 1    | 111  |  63      |   995 | Cyclotomic/Basic.lean |
| 2    |  91  |  90      |   687 | Padics/PadicVal/Basic.lean |
| 3    |  65  |  61      |   955 | NumberField/Cyclotomic/Basic.lean |
| 4    |  49  |  44      |   623 | NumberField/CanonicalEmbedding/ConvexBody.lean |
| 5    |  48  |  80      |   782 | LSeries/HurwitzZetaEven.lean |
| 6    |  48  | 117      |   522 | Real/Irrational.lean |
| 7    |  47  | 113      |   771 | Divisors.lean |
| 8    |  45  |  92      |   928 | Height/Basic.lean |
| 9    |  44  |  13      |   273 | FLT/Polynomial.lean |
| 10   |  42  |  31      |   418 | LSeries/Nonvanishing.lean |

These 10 files account for 590 hits (23.7% of all 2,488 hits) across 6,954 lines.

### Import-Only / Deprecated Files (THEOREMS = 0)

| LINES | PATH |
|-------|------|
|   9   | ArithmeticFunction.lean |
|   8   | ModularForms/Delta.lean |
|  46   | NumberField/Completion/LiesOverInstances.lean |
|  10   | NumberField/FinitePlaces.lean |
|  10   | NumberField/InfinitePlace/Completion.lean |
|  10   | TsumDivsorsAntidiagonal.lean |
|   6   | VonMangoldt.lean |

7 files, 99 lines total. All are Type A (pure import redirects or deprecated stubs).

### Domain Clusters by Hit Density

| Cluster | Files | Total Hits | Avg Hits/File |
|---------|-------|-----------|---------------|
| Cyclotomic/ | 5 | 184 | 36.8 |
| NumberField/CanonicalEmbedding/ | 5 | 166 | 33.2 |
| FLT/ | 5 | 112 | 22.4 |
| Height/ | 5 | 72 | 14.4 |
| Padics/ | 13 | 196 | 15.1 |
| NumberField/Cyclotomic/ | 6 | 97 | 16.2 |
| LSeries/ | 20 | 341 | 17.1 |
| LegendreSymbol/ | 7 | 107 | 15.3 |
| RamificationInertia/ | 6 | 70 | 11.7 |
| ArithmeticFunction/ | 7 | 87 | 12.4 |
| ModularForms/ | 25 | 209 | 8.4 |
| NumberField/ (all) | 35 | 550 | 15.7 |
