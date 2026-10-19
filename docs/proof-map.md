# Mathematical claims and formal interfaces

This map follows the [manuscript](../paper/paper-en.tex), rather than listing every imported module. Paths are relative to the repository layout. The final statement concerns the explicit Pauli Hamiltonian, not an abstract family with an assumed seed.

## Final theorem

[`BilayerDressed.CubicPhysicalGap.standard_spin_uniform_gap`](../lean/Dressed/CubicPhysicalGap.lean) states the uniform result for every real `0 ≤ g ≤ 1/10` and every even `L ≥ 256`. Its eigenvalues include multiplicities; the proof constructs a complete invertible complex eigenbasis, a unique lowest energy, and strict separation by `log(200/13)/1024`.

The preceding declarations `quartic_inputs`, `trial_bounds` and `coordinate_bounds` discharge the actual finite inputs. They are not hypotheses of the final theorem. The broader generic criterion elsewhere in the source must not be mistaken for this fully instantiated endpoint.

Final source SHA-256: `6dbac3e70a6429287618d19c9fb180d403c9c7216d3d62b25b5d712fb0f85a79`.

## 1. Model and exact representations

| Manuscript claim | Source and exact declaration | Role |
|---|---|---|
| Pauli/2 spin convention and rung basis | [`Gap/LocalRungBasis.lean`](../lean/vendor/first_project_v2/Gap/LocalRungBasis.lean): `BilayerGap.LocalRung.physical_spin_intertwines`, `basis_inverse_left`, `basis_inverse_right` | Exact complex basis similarity; no phenomenological effective Hamiltonian. |
| Cartesian bond and global real-rung equivalence | [`LocalBondAction.lean`](../lean/Dressed/LocalBondAction.lean), [`GlobalCartesianBasis.lean`](../lean/Dressed/GlobalCartesianBasis.lean) | Literal local operators and the global number-dependent diagonal involution. |
| Complete physical spectrum with multiplicities | [`Gap/PhysicalGapTheorem.lean`](../lean/vendor/first_project_v2/Gap/PhysicalGapTheorem.lean): `BilayerGap.PhysicalGap.physical_complete_eigenbasis` | Transfers the real finite spectrum to the standard complex Pauli matrix. The older gap endpoint in this file is not the enlarged-interval final theorem. |

## 2. Finite spectral reference

| Manuscript claim | Source and exact declaration |
|---|---|
| Local normal-bond sum of squares and physical comparison | [`CoupledQuadraticComparison.lean`](../lean/Dressed/CoupledQuadraticComparison.lean): `BilayerDressed.CoupledQuadratic.localNormalGram_identity`, `physical_graphHamiltonian_coupled_inner_lower` |
| Finite orthogonal mode change, including the top-degree boundary | [`FiniteOccupationModeRotation.lean`](../lean/Dressed/FiniteOccupationModeRotation.lean): `BilayerDressed.FiniteOccupation.ModeRotation.unitary_transpose_mul`, `unitary_mul_transpose`, `unitary_inverse_create_conjugation` |
| Finite Jacobi Gram factorization and ordered levels | [`FiniteJacobi.lean`](../lean/Dressed/FiniteJacobi.lean): `BilayerDressed.FiniteJacobi.gramFactor_transpose_mul`, `gramFactor_mul_transpose_leading`, `ascendingEigenvalue_lower` |
| Both parity blocks and the full cutoff oscillator spectrum | [`FiniteOscillatorSpectrum.lean`](../lean/Dressed/FiniteOscillatorSpectrum.lean): `occupationMatrix_ascendingEigenvalue_lower`, `occupationMatrix_common_frequency_lower` in namespace `BilayerDressed.FiniteOscillator` |
| Actual finite embedding into the product reference | [`PhysicalProductComparison.lean`](../lean/Dressed/PhysicalProductComparison.lean): `BilayerDressed.PhysicalProduct.graph_product_compression_identity`, `graphHamiltonian_spectral_number_lower` |
| The fixed constants `a = 387/500`, `c_A = −750 A g²/787` | [`PhysicalReferencePointOne.lean`](../lean/Dressed/PhysicalReferencePointOne.lean): `BilayerDressed.PhysicalReferencePointOne.fullHamiltonian_number_lower_fixed`, `fullHamiltonian_nonlowest_energy_fixed`, `fullHamiltonian_thermal_fixed_geometric` |

The reference label number is the number of ordered one-mode eigenvalue labels after the actual mode and oscillator basis changes. It is not silently identified with original site occupation. The thermal comparison removes exactly one reference ground label. All occupation spaces and maps used here are finite.

## 3. Cubic trial, complete residual, and finite norm estimates

| Manuscript claim | Source and exact declaration |
|---|---|
| Actual cubic pair kernel | [`CubicKernelSupersolution.lean`](../lean/Dressed/CubicKernelSupersolution.lean), [`CubicSeedGraphChecks.lean`](../lean/Dressed/CubicSeedGraphChecks.lean) |
| Exact residual of creation degrees 0, 2, 4 and 6 | [`GlobalResidualDegrees.lean`](../lean/Dressed/GlobalResidualDegrees.lean): `BilayerDressed.GlobalResidual.transformed_degree_decomposition`; [`GlobalDressedResidual.lean`](../lean/Dressed/GlobalDressedResidual.lean): `graph_dressed_residual` |
| Commuting the residual through the actual finite trial | [`CreationResidualAction.lean`](../lean/Dressed/CreationResidualAction.lean): `BilayerDressed.GlobalResidual.graph_dressed_residual_action` |
| Signed hard-core trial equals the exact finite projected Taylor vector | [`FiniteDressedProjection.lean`](../lean/Dressed/FiniteDressedProjection.lean): `BilayerDressed.FiniteDressed.dressedVector_eq_projected_trial`, `physical_transpose_word` |
| Pair-norm finite recurrence | [`FinitePairNormRecursion.lean`](../lean/Dressed/FinitePairNormRecursion.lean): `action_norm_sq_le`, `pairVector_norm_sq_le_majorant`, `finiteTrial_norm_sq_le_rational` in namespace `BilayerDressed.FiniteOccupation.TotalCutoff.PairNorm` |
| Occupation convolution and Vandermonde amplification | [`FiniteHomogeneousCreationNorm.lean`](../lean/Dressed/FiniteHomogeneousCreationNorm.lean): `multivariate_vandermonde`, `homogeneous_multiplication_bound`, `actual_homogeneous_vacuum_bound_truncated` in namespace `BilayerDressed.FiniteOccupation.Homogeneous` |
| Four-site matching Gram matrix `9` on the diagonal and `3` off it | [`QuarticFaithfulLift.lean`](../lean/Dressed/QuarticFaithfulLift.lean): `matching_gram`, `matching_combination_norm_sq`; [`QuarticResidualSupportNorm.lean`](../lean/Dressed/QuarticResidualSupportNorm.lean): `residual_vacuum_norm_sq_rooted` |
| Faithful sixth-degree support and its actual mass bounds | [`SexticFaithfulLift.lean`](../lean/Dressed/SexticFaithfulLift.lean), [`CubicSexticMass.lean`](../lean/Dressed/CubicSexticMass.lean), [`CubicSexticAction.lean`](../lean/Dressed/CubicSexticAction.lean) |

The cubic choice of kernel is not a truncation of the transformed Hamiltonian. All resulting coefficient powers, including the full sextic creation residual, are retained. The faithful bosonic vacuum norm is an upper-bound tool transported through a proved one-sided intertwiner; arbitrary compression multiplicativity is never used.

## 4. Actual positive finite moments and physical means

| Manuscript claim | Source and exact declaration |
|---|---|
| Finite Taylor derivative and moment recurrence with boundary signs | [`FinitePositiveMoments.lean`](../lean/Dressed/FinitePositiveMoments.lean): `annihilate_pairState_le`, `pairState_moment_recurrence_positions`, `pairState_wick_step` in namespace `BilayerDressed.FiniteOccupation.TotalCutoff.PositiveMoments` |
| Row-square covariance supersolution and finite maximum principle | [`FiniteWickSupersolution.lean`](../lean/Dressed/FiniteWickSupersolution.lean): `BilayerDressed.FiniteWick.covarianceMajorant_supersolution`, `weighted_column_comparison` |
| Perfect-matching upper bound and color factors `9/3/3`, `405` | [`FiniteWickPairings.lean`](../lean/Dressed/FiniteWickPairings.lean): `pairState_wick_bound`, `color_wick_four`, `color_wick_six_le` |
| Separate signed-state and signed-polynomial absolute majorization | [`FinitePositiveComparison.lean`](../lean/Dressed/FinitePositiveComparison.lean) |
| Physical hard-core polynomial mean dominated by the actual positive finite state | [`FinitePhysicalWick.lean`](../lean/Dressed/FinitePhysicalWick.lean): `BilayerDressed.FinitePhysicalWick.physical_polynomial_mean_bound` |
| Actual positive-state norm ceilings | [`FinitePairStateNormBridge.lean`](../lean/Dressed/FinitePairStateNormBridge.lean): `BilayerDressed.CubicPositiveStateNorm.positive16_dot_self_le`, `positive32_dot_self_le`, `positive64_dot_self_le` |

These are finite Wick **inequalities**, not exact finite Gaussian identities. The norm of the positive absolute-kernel state remains as a factor. It is not identified with the norm of the signed physical trial.

## 5. Exact graph and whole-interval certificate chain

The certificate has distinct proof obligations:

1. **Literal coefficient identification.** The residual is regrouped into its actual signed canonical support/matching fibers.
2. **Exact finite graph membership.** Each actual rooted fiber is identified with an integer polynomial row in the finite dictionary. Zero supports remain covered; ordering and cardinality prove completeness.
3. **All-real interval bounds.** Bernstein and algebraic certificates bound each polynomial for every real `g ∈ [0,1/10]`, not merely at sampled points.
4. **Exact aggregate evaluation.** The Gram norms or nonnegative covariance-weighted means are summed with the proved rooted incidence factor `A/4`.
5. **Physical action.** Projection, finite amplification and the mean/norm triangle inequalities produce the actual trial bounds.

| Obligation | Principal source interface |
|---|---|
| Pair coefficient and literal operator | [`CubicResidualPair.lean`](../lean/Dressed/CubicResidualPair.lean), [`CubicResidualIntervalBounds.lean`](../lean/Dressed/CubicResidualIntervalBounds.lean): `physical_residual2_norm_sq_bound16/32`, `pairMeanCoefficient_bound16/32/64`, `physical_residualShift_eq16/32/64` |
| Signed quartic canonical coefficients | [`QuarticActualCoefficients.lean`](../lean/Dressed/QuarticActualCoefficients.lean): `coefficient`, `residual4_eq_canonical`, `coefficient_equiv` in namespace `BilayerDressed.QuarticActualCoefficients` |
| Actual integer polynomial membership | [`QuarticIntegerTable.lean`](../lean/Dressed/QuarticIntegerTable.lean): `BilayerDressed.QuarticIntegerTable.Checked`, `actual_coefficient`, `physical_norm_eq` |
| Scalar quartic dictionaries and every real coupling | [`CubicQuarticEnvelopes/Seed16.lean`](../lean/Dressed/CubicQuarticEnvelopes/Seed16.lean), [`Seed32.lean`](../lean/Dressed/CubicQuarticEnvelopes/Seed32.lean), [`Seed64.lean`](../lean/Dressed/CubicQuarticEnvelopes/Seed64.lean) |
| Actual endpoint covariance cache | [`QuarticIntegerCovarianceCache.lean`](../lean/Dressed/QuarticIntegerCovarianceCache.lean): `cache16_eq`, `cache32_eq`, `cache64_eq` and `actual_weight16/32/64` |
| Translation of both coefficients and matching weights, including stabilizers | [`QuarticMeanTransport.lean`](../lean/Dressed/QuarticMeanTransport.lean): `canonical_matchingWeight_transport`, `canonicalMeanWeight_transport`, `canonicalMeanWeight_total_rooted` |
| Physical weighted mean to exact integer aggregate | [`QuarticIntegerMeanEvaluation.lean`](../lean/Dressed/QuarticIntegerMeanEvaluation.lean): `BilayerDressed.QuarticIntegerMeanEvaluation.meanCoefficient_eq_rows`, `meanCoefficient_le_integer` |
| Completed physical quartic endpoints | [`QuarticIntegerActualNorm16.lean`](../lean/Dressed/QuarticIntegerActualNorm16.lean), [`QuarticIntegerActualNorm32.lean`](../lean/Dressed/QuarticIntegerActualNorm32.lean), [`QuarticIntegerActualMean16.lean`](../lean/Dressed/QuarticIntegerActualMean16.lean), [`QuarticIntegerActualMean32.lean`](../lean/Dressed/QuarticIntegerActualMean32.lean), [`QuarticIntegerActualMean64.lean`](../lean/Dressed/QuarticIntegerActualMean64.lean) |

The completed quartic endpoint declarations are `BilayerDressed.QuarticIntegerActual.vacuum16`, `vacuum32`, `mean16`, `mean32` and `mean64` in the five corresponding files above.

The normalization `524288` belongs to the actual polynomial coefficient and is already included in the scalar envelope. The subsequent weighted mean denominator is the envelope denominator times the square of the covariance denominator; there is no second factor of `524288`.

The scalar ceilings printed in the paper are defined and proved in [`ScalarTrialMajorants.lean`](../lean/Dressed/ScalarTrialMajorants.lean), namespace `BilayerDressed.ScalarTrial`: in particular `root16_2`, `root16_4`, `root16_6`, `root32_2`, `root32_4`, `root32_6`, `epsilon16`, `epsilon32`, and `mean16/32/64`. These connect squared faithful vacuum bounds and finite norm moments to the stated rational action and mean ceilings.

Python generation and exploratory checks are diagnostic. Acceptance is supplied by the kernel-checked finite source identities, interval certificates and aggregate evaluations. The final theorem does not assume the truth of a JSON file or a floating-point calculation. Large exact arrays remain in their proved source modules so that the human-readable manuscript need not reproduce tens of thousands of rows.

## 6. Actual energy and thermal seed

| Manuscript claim | Source and exact declaration |
|---|---|
| Mean-aware Rayleigh/Temple bounds | [`MeanTrialCertificate.lean`](../lean/Dressed/MeanTrialCertificate.lean): `BilayerDressed.mean_trial_energy_upper`, `mean_trial_energy_lower`; [`CubicTrialEnergy.lean`](../lean/Dressed/CubicTrialEnergy.lean): `physical_upper`, `physical_lower` |
| Positive Temple denominators and the two distinct shift cancellations | [`ScalarIntervalBounds.lean`](../lean/Dressed/ScalarIntervalBounds.lean): `BilayerDressed.ScalarInterval.denominator16_lower`, `denominator32_lower`, `denominator64_lower`, `shift_dx`, `shift_dy` |
| Exact Taylor and rational thermal inequalities | [`ScalarThermalCertificate.lean`](../lean/Dressed/ScalarThermalCertificate.lean): `BilayerDressed.ScalarThermal.taylor_a`, `taylor_16`, `taylor_32`, `taylor_64`, `tail16`, `tail32`, `tail64` |
| Actual physical thermal tails | [`CubicSeedThermal.lean`](../lean/Dressed/CubicSeedThermal.lean): `BilayerDressed.CubicSeedThermal.thermal16`, `thermal32`, `thermal64` |
| The five completed quartic endpoints imply the full trial inputs | [`CubicQuarticSeedReduction.lean`](../lean/Dressed/CubicQuarticSeedReduction.lean): `BilayerDressed.CubicQuarticSeed.trial_bounds` |
| Physical staircase initialization | [`CubicTrialSeedCriterion.lean`](../lean/Dressed/CubicTrialSeedCriterion.lean): `BilayerDressed.CubicTrialSeed.coordinate_bounds`; fully instantiated by `CubicPhysicalGap.coordinate_bounds` |

Temple's threshold is an absolute lower bound on every nonlowest energy. The extensive residual reference shift is not asserted to equal the normalized Rayleigh quotient. Means are needed on all three boxes; residual norms are needed only on the two smaller boxes.

## 7. Spatial moments, ordered propagation, and all even sizes

| Manuscript claim | Source and exact declaration |
|---|---|
| Finite symmetric collision-excluding transfer and exact network contraction | [`Gap/HistoryTransfer.lean`](../lean/vendor/first_project_v2/Gap/HistoryTransfer.lean): `BilayerGap.History.collisionTransfer_symmetric`, `trace_powers_space_time_exchange_rotate` |
| Finite transfer trace converges to the physical partition function | [`Gap/HistoryApproximation.lean`](../lean/vendor/first_project_v2/Gap/HistoryApproximation.lean): `transferApprox_trace_limit`; [`Gap/HistoryStripTorus.lean`](../lean/vendor/first_project_v2/Gap/HistoryStripTorus.lean): `column_stripPartition_eq_full`, `fullHamiltonian_spatial_limits` |
| Probability purity squaring | [`Gap/Squaring.lean`](../lean/vendor/first_project_v2/Gap/Squaring.lean): `finite_purity_squaring` |
| Staggered three-coordinate update and uniform bootstrap | [`Gap/Staircase.lean`](../lean/vendor/first_project_v2/Gap/Staircase.lean): `coordinate_staircase_update`, `coordinate_staircase_bootstrap` |
| Six ordered unequal-error updates | [`CoordinateWarmup.lean`](../lean/Dressed/CoordinateWarmup.lean): `BilayerDressed.CoordinateWarmup.six_steps`, `seed_256_1024`, `common_G7_bound` |
| Rectangular moment interpolation | [`Gap/LimitCriterion.lean`](../lean/vendor/first_project_v2/Gap/LimitCriterion.lean): `SpectralFamily.limit_rectangle_purity`, `limit_scaled_box_purity`, `square_gap_of_limit_seed` in namespace `BilayerGap` |
| Dyadic boxes cover every sufficiently large even square; finite Gibbs gap extraction | [`Gap/Assembly.lean`](../lean/vendor/first_project_v2/Gap/Assembly.lean): `exists_dyadic_size_box`, `finite_gibbs_gap_of_scaled_purity` |
| Final physical transfer to Pauli Hamiltonian | [`PhysicalStandardCriterion.lean`](../lean/Dressed/PhysicalStandardCriterion.lean): `BilayerDressed.PhysicalStandard.standard_spin_gap_of_seed`; [`CubicPhysicalGap.lean`](../lean/Dressed/CubicPhysicalGap.lean): final theorem |

Even powers, not an assumed nonnegative transfer spectrum, make the spatial moment weights nonnegative. Each transverse width may have a different transfer matrix. The dimension-independent probability inequalities do not require a joint spectrum across widths or directions.

## Reproduction scope

The corrected 556-module project rebuild and all-declaration audit completed on 19 October 2026. It checked 77,040 constants, including 50,494 theorem constants, with axiom union `propext`, `Classical.choice`, `Quot.sound`. No old project objects were reused; pinned external dependency caches were reused. See [VERIFICATION.md](../VERIFICATION.md) for the receipt and trust boundary.

The source-input manifest has SHA-256 `cbe4e29cf66b6a3a161e5ecac13b25c0c5465d32454966c1b2760c617844ae2b`. The layout prefix `lean/` is a presentation choice; the selected proof-source bytes and inner module names are unchanged. Local relative paths are repository links, not claims that the files have a particular public web URL.
