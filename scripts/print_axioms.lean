-- Live axiom audit input, consumed by scripts/check-axioms.sh.
-- Run after `lake build`:   lake env lean scripts/print_axioms.lean
--
-- Append one `#print axioms` line for every public theorem a PR claims as a result.
-- APPEND-ONLY: removing or renaming a line is a `needs-decision` change.
import MobiusCPT

#print axioms MobiusCPT.placeholder_add_zero
#print axioms MobiusCPT.WightmanData.boost_add
#print axioms MobiusCPT.WightmanStruct.smearedProductOn_append
#print axioms MobiusCPT.WightmanStruct.smearedProduct_append
#print axioms MobiusCPT.WightmanStruct.isCompatibleVac_of_isCompatible
#print axioms MobiusCPT.WightmanStruct.isCompatible_of_isCompatibleVac
#print axioms MobiusCPT.WightmanStruct.isCompatible_iff_isCompatibleVac

-- Issue #4: [T26], Definitions 2.4-2.5 interface, minus (W2), `IsWightmanCFT`,
-- and the (W3) vacuum-annihilation bridge; deferred pending a general support predicate
-- and test-function monomials from Issue #3.
-- MobiusCPT/Wightman/Basic.lean — algebraic interface, D*_F, regularity, P(I_±)Ω.
#print axioms MobiusCPT.WightmanStruct.smear_linear
#print axioms MobiusCPT.WightmanStruct.smear_addLinear
#print axioms MobiusCPT.WightmanStruct.smearedProductOn_nil
#print axioms MobiusCPT.WightmanStruct.smearedProductOn_cons
#print axioms MobiusCPT.WightmanStruct.smearedProduct_nil
#print axioms MobiusCPT.WightmanStruct.smearedProduct_cons
#print axioms MobiusCPT.WightmanStruct.smearedProductOn_linear
#print axioms MobiusCPT.WightmanStruct.compatApply_linear
#print axioms MobiusCPT.WightmanStruct.actsRegularly_iff
#print axioms MobiusCPT.WightmanStruct.memPUpperOmega_iff
#print axioms MobiusCPT.WightmanStruct.memPLowerOmega_iff
#print axioms MobiusCPT.WightmanStruct.memPUpperOmega_add
#print axioms MobiusCPT.WightmanStruct.memPUpperOmega_smul
#print axioms MobiusCPT.WightmanStruct.memPLowerOmega_add
#print axioms MobiusCPT.WightmanStruct.memPLowerOmega_smul
#print axioms MobiusCPT.WightmanStruct.memPUpperOmega_vac
#print axioms MobiusCPT.WightmanStruct.memPLowerOmega_vac

-- MobiusCPT/Wightman/Mobius.lean — Möbius interface, boost, conformal dimension, (W3), (W4).
#print axioms MobiusCPT.WightmanData.U_inv_apply
#print axioms MobiusCPT.WightmanData.boost_linear
#print axioms MobiusCPT.WightmanData.boost_zero
#print axioms MobiusCPT.WightmanData.hasConformalDim_zero
#print axioms MobiusCPT.WightmanData.hasConformalDim_add
#print axioms MobiusCPT.WightmanData.hasConformalDim_smul
#print axioms MobiusCPT.WightmanData.w4_vacuum_invariant
#print axioms MobiusCPT.WightmanData.w4_rotation_invariant

-- MobiusCPT/Wightman/StrongTopology.lean — the F-strong topology and its two consequences.
#print axioms MobiusCPT.WightmanStruct.fStrongTopology_isTopologicalAddGroup
#print axioms MobiusCPT.WightmanStruct.fStrongTopology_continuousSMul
#print axioms MobiusCPT.WightmanStruct.fStrongTopology_locallyConvex
#print axioms MobiusCPT.WightmanStruct.fStrongTopology_continuous_multiSmear
#print axioms MobiusCPT.WightmanStruct.fStrongTopology_isFStrongAdmissible
#print axioms MobiusCPT.WightmanStruct.fStrongTopology_le
#print axioms MobiusCPT.WightmanStruct.isCompatible_of_continuous
#print axioms MobiusCPT.WightmanStruct.continuous_of_isCompatible
#print axioms MobiusCPT.WightmanStruct.continuous_iff_isCompatible
#print axioms MobiusCPT.WightmanStruct.t2Space_of_actsRegularly
#print axioms MobiusCPT.WightmanStruct.actsRegularly_of_t2Space
#print axioms MobiusCPT.WightmanStruct.actsRegularly_iff_t2Space

-- MobiusCPT/Wightman/Axioms.lean — Wightman axiom (W1).
#print axioms MobiusCPT.WightmanData.W1.continuous
#print axioms MobiusCPT.WightmanData.W1.covariant
#print axioms MobiusCPT.WightmanData.w1_U_bicontinuous
#print axioms MobiusCPT.WightmanData.w1_continuous_boost

-- Issue #3 — circle test functions, semicircle support, inversion, C^N seminorms.
-- Smooth gluing of endpoint-flat functions ([T26] §3, zero-extension of C_0^∞(I_±)).
#print axioms MobiusCPT.contDiff_stepRight
#print axioms MobiusCPT.iteratedDeriv_stepRight
#print axioms MobiusCPT.contDiff_cutIcc
#print axioms MobiusCPT.contDiff_periodize
#print axioms MobiusCPT.periodic_periodize
#print axioms MobiusCPT.periodize_eq_self
-- The angle bridge: f ↦ f ∘ Circle.exp is a bijection onto 2π-periodic smooth functions.
#print axioms MobiusCPT.contDiff_toAngle
#print axioms MobiusCPT.periodic_toAngle
#print axioms MobiusCPT.toAngle_injective
#print axioms MobiusCPT.exists_toAngle_eq
#print axioms MobiusCPT.toAngle_bijOn
-- The C^N family: ‖f‖_{C^N} = Σ_{j≤N} ‖d^j f/dθ^j‖_∞, a norm, and the Fréchet topology.
#print axioms MobiusCPT.withSeminorms_angleDerivs
#print axioms MobiusCPT.withSeminorms_cnorm
#print axioms MobiusCPT.cnorm_eq
#print axioms MobiusCPT.cnorm_add_le
#print axioms MobiusCPT.cnorm_smul
#print axioms MobiusCPT.cnorm_mono
#print axioms MobiusCPT.cnorm_eq_zero
#print axioms MobiusCPT.tendsto_iff_cnorm
-- Semicircle support, the open-semicircle convention, and the four equivalence lemmas.
#print axioms MobiusCPT.suppUpper_iff_angle
#print axioms MobiusCPT.suppLower_iff_angle
#print axioms MobiusCPT.iteratedDeriv_toAngle_eq_zero_of_suppUpper
#print axioms MobiusCPT.iteratedDeriv_toAngle_eq_zero_of_suppLower
#print axioms MobiusCPT.IsUpperFlat.iteratedDeriv_zero
#print axioms MobiusCPT.IsLowerFlat.iteratedDeriv_zero
#print axioms MobiusCPT.suppUpper_iff_zeroExtension
#print axioms MobiusCPT.suppLower_iff_zeroExtension
#print axioms MobiusCPT.closure_upperArc
#print axioms MobiusCPT.suppUpper_iff_tsupport
#print axioms MobiusCPT.suppUpper_of_tsupport_subset
#print axioms MobiusCPT.exists_suppUpper_not_tsupport_subset
-- Inversion f ↦ f ∘ z⁻¹ ([T26] §3 and Lemma 3.9).
#print axioms MobiusCPT.toAngle_inv
#print axioms MobiusCPT.inv_add
#print axioms MobiusCPT.inv_smul
#print axioms MobiusCPT.inv_involutive
#print axioms MobiusCPT.inv_supp
#print axioms MobiusCPT.angleDeriv_inv
#print axioms MobiusCPT.norm_angleDerivB_inv
#print axioms MobiusCPT.cnorm_inv

-- Issue #3 × #4 join: the concrete C^∞(S¹) is a model of the abstract interface.
#print axioms MobiusCPT.instTestFunctionsTestFn
-- General closed support and the disjointness relation Wightman locality (W2) is stated with.
#print axioms MobiusCPT.support_def
#print axioms MobiusCPT.isClosed_support
#print axioms MobiusCPT.notMem_support
#print axioms MobiusCPT.support_zero
#print axioms MobiusCPT.support_neg
#print axioms MobiusCPT.support_smul_subset
#print axioms MobiusCPT.support_add_subset
#print axioms MobiusCPT.disjointSupport_comm
#print axioms MobiusCPT.DisjointSupport.eq_zero_or_eq_zero
#print axioms MobiusCPT.disjointSupport_zero_left
#print axioms MobiusCPT.suppUpper_iff_support
#print axioms MobiusCPT.suppLower_iff_support
-- Monomials z^n as test functions ([T26] §2.2), the basis the Fourier expansion is taken in.
#print axioms MobiusCPT.monomial_apply
#print axioms MobiusCPT.monomial_apply'
#print axioms MobiusCPT.monomial_zero
#print axioms MobiusCPT.toAngle_monomial
#print axioms MobiusCPT.monomial_ne_zero
#print axioms MobiusCPT.support_monomial
#print axioms MobiusCPT.inv_monomial

-- Issue #28: the joint-vs-separate continuity adapter ([T26] Def. 2.4 vs [CRTT25] Def. 2.5).
-- MobiusCPT/TestFunctions/Complete.lean — C^∞(S¹) is Fréchet: Baire, hence barrelled.
#print axioms MobiusCPT.angleDerivsₗ_injective
#print axioms MobiusCPT.isInducing_angleDerivs
#print axioms MobiusCPT.contDiff_of_tendstoUniformly_iteratedDeriv
#print axioms MobiusCPT.isClosed_range_angleDerivs
#print axioms MobiusCPT.isCompletelyMetrizableSpace_testFn
#print axioms MobiusCPT.testFnBaireSpace
#print axioms MobiusCPT.testFnBarrelledSpace
#print axioms MobiusCPT.testFnRealBarrelledSpace
-- MobiusCPT/Analysis/SeparateJoint.lean — Banach-Steinhaus and [Treves, Thm. 34.1].
#print axioms MobiusCPT.exists_nhds_zero_forall_norm_le
#print axioms MobiusCPT.MultilinearMap.continuous_of_continuous_update
#print axioms MobiusCPT.continuous_of_separately_continuous_multilinear
-- MobiusCPT/Wightman/Continuity.lean — the two readings of D*_F and of ActsRegularly coincide.
#print axioms MobiusCPT.WightmanStruct.multiSmear_succ
#print axioms MobiusCPT.WightmanStruct.multiSmear_update_add
#print axioms MobiusCPT.WightmanStruct.multiSmear_update_smul
#print axioms MobiusCPT.WightmanStruct.multiSmearMultilinear_apply
#print axioms MobiusCPT.WightmanStruct.isCompatibleSep_of_isCompatible
#print axioms MobiusCPT.WightmanStruct.isCompatible_of_isCompatibleSep
#print axioms MobiusCPT.WightmanStruct.isCompatible_iff_isCompatibleSep
#print axioms MobiusCPT.WightmanStruct.setOf_isCompatible_eq
#print axioms MobiusCPT.WightmanStruct.actsRegularly_iff_actsRegularlySep
#print axioms MobiusCPT.WightmanStruct.actsRegularlySep_iff

-- Issue #30: Fourier series in C^∞(S¹) — rapid decay and C^∞ convergence.
-- MobiusCPT/TestFunctions/Fourier.lean
#print axioms MobiusCPT.toAddCircle_coe
#print axioms MobiusCPT.continuous_toAddCircle
#print axioms MobiusCPT.angleDerivCircle_coe
#print axioms MobiusCPT.angleDerivCircle_zero
#print axioms MobiusCPT.fourierCoefDeriv_zero
#print axioms MobiusCPT.fourier_eq_toAngle_monomial
#print axioms MobiusCPT.toAddCircle_monomial
#print axioms MobiusCPT.fourierCoef_monomial
#print axioms MobiusCPT.norm_fourierCoefDeriv_le
#print axioms MobiusCPT.norm_fourierCoef_le
#print axioms MobiusCPT.fourierCoefDeriv_succ
#print axioms MobiusCPT.fourierCoefDeriv_eq
#print axioms MobiusCPT.norm_fourierCoef_mul_pow_le
#print axioms MobiusCPT.norm_fourierCoef_mul_pow_le_cnorm
#print axioms MobiusCPT.summable_norm_fourierCoef_mul_pow
#print axioms MobiusCPT.angleDeriv_monomial
#print axioms MobiusCPT.hasSum_angleDeriv
#print axioms MobiusCPT.hasSum_fourierSeries
#print axioms MobiusCPT.tendsto_fourierPartialSum
#print axioms MobiusCPT.tendsto_cnorm_fourierPartialSum
#print axioms MobiusCPT.exists_suppUpper_toAngle_eq_periodize
#print axioms MobiusCPT.exists_suppLower_toAngle_eq_periodize
#print axioms MobiusCPT.exists_suppUpper_add_suppLower_of_flat
#print axioms MobiusCPT.closure_lowerArc
#print axioms MobiusCPT.suppLower_iff_tsupport
#print axioms MobiusCPT.suppLower_of_tsupport_subset
#print axioms MobiusCPT.exists_suppLower_not_tsupport_subset
#print axioms MobiusCPT.not_forall_exists_suppUpper_add_suppLower
#print axioms MobiusCPT.norm_angleDerivB_eq

-- Issue #25: locality and the Wightman CFT bundle — Basic.lean and Axioms.lean.
#print axioms MobiusCPT.WightmanStruct.W2
#print axioms MobiusCPT.WightmanStruct.w2_comp
#print axioms MobiusCPT.WightmanStruct.w2_symm
#print axioms MobiusCPT.WightmanData.IsWightmanCFT
#print axioms MobiusCPT.WightmanData.isWightmanCFT_iff
#print axioms MobiusCPT.WightmanData.IsWightmanCFT.actsRegularly
#print axioms MobiusCPT.WightmanData.IsWightmanCFT.w1
#print axioms MobiusCPT.WightmanData.IsWightmanCFT.w2
#print axioms MobiusCPT.WightmanData.IsWightmanCFT.w3
#print axioms MobiusCPT.WightmanData.IsWightmanCFT.w4

-- Issue #5: the Mobius boost subgroup and the conformal test-function action beta_d.
-- [T26] Sections 2.2 and 3, Definitions 2.4 and 3.5, equations (3.4)-(3.5), Lemmas 3.6-3.7.

-- MobiusCPT/Mobius/Basic.lean — SU(1,1), the circle action, rotations, boosts, and Mob = PSU(1,1).
#print axioms MobiusCPT.SU11.ext
#print axioms MobiusCPT.SU11.instOne
#print axioms MobiusCPT.SU11.instMul
#print axioms MobiusCPT.SU11.instInv
#print axioms MobiusCPT.SU11.neg
#print axioms MobiusCPT.SU11.one_alpha
#print axioms MobiusCPT.SU11.one_beta
#print axioms MobiusCPT.SU11.mul_alpha
#print axioms MobiusCPT.SU11.mul_beta
#print axioms MobiusCPT.SU11.inv_alpha
#print axioms MobiusCPT.SU11.inv_beta
#print axioms MobiusCPT.SU11.neg_alpha
#print axioms MobiusCPT.SU11.neg_beta
#print axioms MobiusCPT.SU11.neg_neg
#print axioms MobiusCPT.SU11.neg_mul
#print axioms MobiusCPT.SU11.mul_neg
#print axioms MobiusCPT.SU11.instGroup
#print axioms MobiusCPT.SU11.neg_one_mul
#print axioms MobiusCPT.SU11.mul_neg_one
#print axioms MobiusCPT.j
#print axioms MobiusCPT.j_ne_zero
#print axioms MobiusCPT.num_eq
#print axioms MobiusCPT.norm_num_eq_norm_j
#print axioms MobiusCPT.instSMulSU11Circle
#print axioms MobiusCPT.coe_smul
#print axioms MobiusCPT.j_one
#print axioms MobiusCPT.j_mul
#print axioms MobiusCPT.instMulActionSU11Circle
#print axioms MobiusCPT.smul_neg_eq
#print axioms MobiusCPT.j_neg
#print axioms MobiusCPT.rotMat
#print axioms MobiusCPT.rotMat_zero
#print axioms MobiusCPT.rotMat_add
#print axioms MobiusCPT.rotMat_two_pi
#print axioms MobiusCPT.rotMat_smul
#print axioms MobiusCPT.boostMat
#print axioms MobiusCPT.boostMat_alpha
#print axioms MobiusCPT.boostMat_beta
#print axioms MobiusCPT.boostMat_zero
#print axioms MobiusCPT.boostMat_add
#print axioms MobiusCPT.j_boostMat
#print axioms MobiusCPT.j_boostMat_neg
#print axioms MobiusCPT.im_boostMat_smul
#print axioms MobiusCPT.boostMat_smul_mem_upperArc
#print axioms MobiusCPT.boostMat_smul_mem_lowerArc
#print axioms MobiusCPT.signSubgroup
#print axioms MobiusCPT.signSubgroupNormal
#print axioms MobiusCPT.Mob
#print axioms MobiusCPT.instGroupMob
#print axioms MobiusCPT.Mob.mk
#print axioms MobiusCPT.Mob.mk_mul
#print axioms MobiusCPT.Mob.mk_one
#print axioms MobiusCPT.Mob.mk_eq_mk
#print axioms MobiusCPT.Mob.mk_neg
#print axioms MobiusCPT.Mob.mk_surjective
#print axioms MobiusCPT.Mob.instSMulCircle
#print axioms MobiusCPT.Mob.mk_smul
#print axioms MobiusCPT.Mob.instMulActionCircle
#print axioms MobiusCPT.Mob.rot
#print axioms MobiusCPT.Mob.boost
#print axioms MobiusCPT.Mob.rot_zero
#print axioms MobiusCPT.Mob.rot_add
#print axioms MobiusCPT.Mob.rot_smul
#print axioms MobiusCPT.Mob.boost_zero
#print axioms MobiusCPT.Mob.boost_add
#print axioms MobiusCPT.Mob.rot_two_pi
#print axioms MobiusCPT.Mob.rot_pi_ne_one
#print axioms MobiusCPT.Mob.exists_int_of_rot_eq_one
#print axioms MobiusCPT.Mob.boost_ne_one

-- MobiusCPT/Mobius/ComplexBoost.lean — the complex boost v_tau, the closed strip and v_{i*pi} = inversion.
#print axioms MobiusCPT.cnum
#print axioms MobiusCPT.cden
#print axioms MobiusCPT.vApply
#print axioms MobiusCPT.cnum_neg
#print axioms MobiusCPT.cden_neg
#print axioms MobiusCPT.cosh_mul_cden_add_sinh_mul_cnum
#print axioms MobiusCPT.not_and_cnum_cden_eq_zero
#print axioms MobiusCPT.normSq_sub_normSq_general
#print axioms MobiusCPT.im_cosh_mul_conj_sinh
#print axioms MobiusCPT.normSq_cnum_neg_sub_normSq_cden_neg
#print axioms MobiusCPT.norm_cden_neg_le_norm_cnum_neg
#print axioms MobiusCPT.one_le_norm_vApply_neg
#print axioms MobiusCPT.one_le_norm_vApply_neg_of_mem_upperArc
#print axioms MobiusCPT.Oset
#print axioms MobiusCPT.vApplyNegSphere
#print axioms MobiusCPT.vApplyNegSphere_mem_Oset
#print axioms MobiusCPT.normSq_cosh_sub_normSq_sinh
#print axioms MobiusCPT.cden_neg_ne_zero_of_im_ne
#print axioms MobiusCPT.cosh_I_mul_pi_div_two
#print axioms MobiusCPT.sinh_I_mul_pi_div_two
#print axioms MobiusCPT.cden_I_mul_pi_ne_zero
#print axioms MobiusCPT.vApply_I_mul_pi
#print axioms MobiusCPT.vApply_I_mul_pi_circle
#print axioms MobiusCPT.cosh_add_re_mul_sinh
#print axioms MobiusCPT.normSq_cden_neg_ofReal

-- MobiusCPT/Mobius/Factor.lean — the conformal factor X_gamma, its cocycle and the boost formula.
#print axioms MobiusCPT.X
#print axioms MobiusCPT.X_pos
#print axioms MobiusCPT.X_one
#print axioms MobiusCPT.X_neg
#print axioms MobiusCPT.X_mul
#print axioms MobiusCPT.X_inv_smul
#print axioms MobiusCPT.hasDerivAt_smul_circleExp
#print axioms MobiusCPT.X_eq_logDeriv
#print axioms MobiusCPT.boostMat_inv
#print axioms MobiusCPT.j_boostMat_eq_cden
#print axioms MobiusCPT.X_boostMat_inv_smul
#print axioms MobiusCPT.coe_boostMat_smul
#print axioms MobiusCPT.X_rotMat
#print axioms MobiusCPT.Mob.X
#print axioms MobiusCPT.Mob.X_mk
#print axioms MobiusCPT.Mob.X_pos
#print axioms MobiusCPT.Mob.X_mul
#print axioms MobiusCPT.Mob.X_one

-- MobiusCPT/Mobius/Beta.lean — the conformal action beta_d and the MobiusAction instance.
#print axioms MobiusCPT.contMDiff_smul
#print axioms MobiusCPT.betaFun
#print axioms MobiusCPT.betaFun_eq
#print axioms MobiusCPT.contMDiff_betaFun
#print axioms MobiusCPT.beta
#print axioms MobiusCPT.beta_apply
#print axioms MobiusCPT.beta_one
#print axioms MobiusCPT.beta_mul
#print axioms MobiusCPT.beta_neg
#print axioms MobiusCPT.Mob.beta
#print axioms MobiusCPT.Mob.beta_mk
#print axioms MobiusCPT.mobiusActionMobTestFn
#print axioms MobiusCPT.rotMat_inv
#print axioms MobiusCPT.beta_rotMat_monomial
#print axioms MobiusCPT.Mob.beta_rot_monomial
#print axioms MobiusCPT.beta_boostMat_apply
#print axioms MobiusCPT.Mob.beta_boost_apply

-- MobiusCPT/Mobius/Covariance.lean — the covariance rewrite moving U(gamma) through smeared products.
#print axioms MobiusCPT.WightmanData.IsCovariant.smear_comm
#print axioms MobiusCPT.WightmanData.U_smearedProductOn
#print axioms MobiusCPT.WightmanData.U_smearedProduct
#print axioms MobiusCPT.WightmanData.boost_smearedProduct
#print axioms MobiusCPT.WightmanData.rotation_smearedProduct

-- Issue #26: [T26], proof of Lemma 3.7 — the (W3) vacuum-annihilation bridge.
-- MobiusCPT/Wightman/Modes.lean — conformal dimension of smeared rotation eigenvectors,
-- and the mode-by-mode application of the (W3) spectrum condition (abstract MobiusAction).
#print axioms MobiusCPT.IsRotWeight
#print axioms MobiusCPT.WightmanData.hasConformalDim_smear_vac
#print axioms MobiusCPT.WightmanData.smear_vac_eq_zero_of_rotWeight_pos
#print axioms MobiusCPT.WightmanData.weightedProduct
#print axioms MobiusCPT.WightmanData.weightedProduct_nil
#print axioms MobiusCPT.WightmanData.weightedProduct_cons
#print axioms MobiusCPT.WightmanData.hasConformalDim_weightedProduct
#print axioms MobiusCPT.WightmanData.weightedProduct_eq_zero_of_sum_pos

-- MobiusCPT/Wightman/W3Bridge.lean — the bridge on the concrete instance (Mob, TestFn):
-- modes, (W3) mode by mode, and the passage to a general test function through D*_F and regularity.
#print axioms MobiusCPT.isRotWeight_monomial
#print axioms MobiusCPT.WightmanData.hasConformalDim_smear_monomial_vac
#print axioms MobiusCPT.WightmanData.smear_monomial_vac_eq_zero
#print axioms MobiusCPT.WightmanData.hasConformalDim_smearedProduct_monomial
#print axioms MobiusCPT.WightmanData.smearedProduct_monomial_eq_zero
#print axioms MobiusCPT.WightmanData.smearVac
#print axioms MobiusCPT.WightmanData.smearVac_apply
#print axioms MobiusCPT.WightmanData.continuous_compatApply_smearVac
#print axioms MobiusCPT.WightmanData.hasSum_compatApply_smearVac
#print axioms MobiusCPT.WightmanData.compatApply_smear_vac_eq_zero
#print axioms MobiusCPT.WightmanData.smear_vac_eq_zero_of_fourierCoef_eq_zero
#print axioms MobiusCPT.WightmanData.smear_vac_eq_zero_of_fourierCoef_eq_zero'

-- Issue #7: [T26], Definitions 3.2-3.3 and Lemma 3.4.
-- MobiusCPT/TestFunctions/Split.lean — the endpoint-flat semicircle split, as named functions.
#print axioms MobiusCPT.IsEndpointFlat.of_suppUpper
#print axioms MobiusCPT.IsEndpointFlat.of_suppLower
#print axioms MobiusCPT.IsEndpointFlat.two_pi
#print axioms MobiusCPT.IsEndpointFlat.isUpperFlat_cutIcc
#print axioms MobiusCPT.IsEndpointFlat.isLowerFlat_cutIcc
#print axioms MobiusCPT.splitUpper
#print axioms MobiusCPT.splitLower
#print axioms MobiusCPT.toAngle_splitUpper
#print axioms MobiusCPT.toAngle_splitLower
#print axioms MobiusCPT.suppUpper_splitUpper
#print axioms MobiusCPT.suppLower_splitLower
#print axioms MobiusCPT.toAngle_splitUpper_of_mem
#print axioms MobiusCPT.splitUpper_of_suppUpper
#print axioms MobiusCPT.splitLower_of_suppLower
#print axioms MobiusCPT.splitUpper_add_splitLower
-- MobiusCPT/TestFunctions/Analytic.lean — the class `𝓧` and its restrictions.
#print axioms MobiusCPT.isOpen_OexteriorInterior
#print axioms MobiusCPT.isClosed_Oexterior
#print axioms MobiusCPT.OexteriorInterior_subset_Oexterior
#print axioms MobiusCPT.circle_subset_Oexterior
#print axioms MobiusCPT.uniqueDiffOn_Oexterior
#print axioms MobiusCPT.contDiff_circle_map
#print axioms MobiusCPT.exists_bound_iteratedFDeriv_circle_map
#print axioms MobiusCPT.AnalyticTestFn.contDiff_boundary
#print axioms MobiusCPT.AnalyticTestFn.periodic_boundary
#print axioms MobiusCPT.xRestrictS1
#print axioms MobiusCPT.toAngle_xRestrictS1
#print axioms MobiusCPT.xRestrictS1_apply
#print axioms MobiusCPT.AnalyticTestFn.iteratedDeriv_boundary_eq_zero
#print axioms MobiusCPT.AnalyticTestFn.isEndpointFlat
#print axioms MobiusCPT.xRestrictUpper
#print axioms MobiusCPT.xRestrictLower
#print axioms MobiusCPT.xRestrictUpper_supp
#print axioms MobiusCPT.xRestrictLower_supp
#print axioms MobiusCPT.xRestrict_split
#print axioms MobiusCPT.AnalyticTestFn.evalSphere
#print axioms MobiusCPT.AnalyticTestFn.evalSphere_infty
#print axioms MobiusCPT.AnalyticTestFn.evalSphere_coe
#print axioms MobiusCPT.AnalyticTestFn.differentiableAt_inv

-- Issue #7 (continued): the analytic machinery behind [T26], Lemma 3.4.
-- MobiusCPT/Analysis/FlatCalculus.lean — Taylor and flat-extension lemmas (endpoint smoothness).
#print axioms MobiusCPT.exists_norm_le_pow_of_iteratedDeriv_eq_zero
#print axioms MobiusCPT.contDiff_of_flat_at_zero
#print axioms MobiusCPT.flatSeries
#print axioms MobiusCPT.contDiffWithinAt_of_flat_holomorphic
#print axioms MobiusCPT.iteratedFDerivWithin_eq_zero_of_flat_holomorphic
-- MobiusCPT/Analysis/GaussianConv.lean — the Gaussian kernel, the decay class, and the convolution
-- (differentiation under the integral and dominated convergence are discharged here).
#print axioms MobiusCPT.gaussKernel
#print axioms MobiusCPT.gaussKernel_ofReal
#print axioms MobiusCPT.norm_gaussKernel
#print axioms MobiusCPT.gaussKernel_ofReal'
#print axioms MobiusCPT.integrable_gaussKernel
#print axioms MobiusCPT.integral_gaussKernel
#print axioms MobiusCPT.hasDerivAt_gaussKernel
#print axioms MobiusCPT.differentiable_gaussKernel
#print axioms MobiusCPT.gaussKernel_scale
#print axioms MobiusCPT.IsRapidlyDecaying.iteratedDeriv
#print axioms MobiusCPT.IsRapidlyDecaying.exists_bound
#print axioms MobiusCPT.integrable_exp_neg_abs
#print axioms MobiusCPT.IsRapidlyDecaying.integrable
#print axioms MobiusCPT.iteratedDeriv_iteratedDeriv
#print axioms MobiusCPT.gaussConvReal
#print axioms MobiusCPT.integrable_gaussConvReal_integrand
#print axioms MobiusCPT.gaussConvReal_sub
#print axioms MobiusCPT.iteratedDeriv_gaussConvReal
#print axioms MobiusCPT.integrable_norm_gaussKernel_mul_abs
#print axioms MobiusCPT.integral_norm_gaussKernel_mul_abs_scale
#print axioms MobiusCPT.integrable_gaussKernel_mul_exp
#print axioms MobiusCPT.tendsto_integral_abs_tail
#print axioms MobiusCPT.tendsto_gaussKernel_weighted_far
#print axioms MobiusCPT.exists_norm_isRapidlyDecaying_sub_le
#print axioms MobiusCPT.exists_norm_isRapidlyDecaying_far_le
#print axioms MobiusCPT.exists_norm_gaussConvReal_sub_le
#print axioms MobiusCPT.gaussConv
#print axioms MobiusCPT.integrable_gaussKernel_sub
#print axioms MobiusCPT.integrable_gaussConv_integrand
#print axioms MobiusCPT.gaussConv_ofReal
#print axioms MobiusCPT.differentiable_gaussConv
#print axioms MobiusCPT.exists_norm_gaussConv_le
-- MobiusCPT/Analysis/BoostChart.lean — the Cayley/boost chart and its branch logarithm.
#print axioms MobiusCPT.cayley
#print axioms MobiusCPT.cayley_vApply_neg
#print axioms MobiusCPT.cayley_re_formula
#print axioms MobiusCPT.cayley_im_formula
#print axioms MobiusCPT.cutSegment
#print axioms MobiusCPT.notMem_cutSegment_of_one_le_norm
#print axioms MobiusCPT.neg_cayley_mem_slitPlane
#print axioms MobiusCPT.boostCoord
#print axioms MobiusCPT.analyticAt_boostCoord
#print axioms MobiusCPT.exp_boostCoord
#print axioms MobiusCPT.re_boostCoord
#print axioms MobiusCPT.exp_neg_re_boostCoord
#print axioms MobiusCPT.exp_re_boostCoord
#print axioms MobiusCPT.abs_im_boostCoord_le
#print axioms MobiusCPT.angleToBoost
#print axioms MobiusCPT.boostToAngle
#print axioms MobiusCPT.sin_half_angle_pos
#print axioms MobiusCPT.cos_half_angle_pos
#print axioms MobiusCPT.neg_cos_half_angle_pos
#print axioms MobiusCPT.boostToAngle_mem_Ioo
#print axioms MobiusCPT.boostToAngle_eq_pi_sub
#print axioms MobiusCPT.contDiff_boostToAngle
#print axioms MobiusCPT.hasDerivAt_boostToAngle
#print axioms MobiusCPT.sin_boostToAngle_pos
#print axioms MobiusCPT.sin_half_boostToAngle_pos
#print axioms MobiusCPT.angleToBoost_boostToAngle
#print axioms MobiusCPT.boostToAngle_angleToBoost
#print axioms MobiusCPT.boostCoord_circleExp
#print axioms MobiusCPT.boostCoord_circleExp_lower
-- MobiusCPT/Analysis/BoostWeights.lean — the weighted derivative dictionary of the chart.
#print axioms MobiusCPT.exists_bound_boostChart
#print axioms MobiusCPT.exists_norm_iteratedDeriv_boostChart_le
-- MobiusCPT/Analysis/BoostDictionary.lean — endpoint flatness becomes super-exponential decay.
#print axioms MobiusCPT.exists_norm_iteratedDeriv_comp_boostToAngle_nonneg
#print axioms MobiusCPT.exists_norm_iteratedDeriv_comp_boostToAngle_nonpos
#print axioms MobiusCPT.isRapidlyDecaying_comp_boostToAngle
-- MobiusCPT/TestFunctions/AnalyticApprox.lean — the approximants of Lemma 3.4 as elements of `𝓧`.
#print axioms MobiusCPT.isClosed_cutSegment
#print axioms MobiusCPT.isOpen_compl_cutSegment
#print axioms MobiusCPT.stripApprox
#print axioms MobiusCPT.stripApprox_of_notMem_cutSegment
#print axioms MobiusCPT.analyticAt_stripApprox
#print axioms MobiusCPT.real_exp_neg_nat_mul
#print axioms MobiusCPT.real_exp_nat_mul
#print axioms MobiusCPT.exists_norm_stripApprox_le_one
#print axioms MobiusCPT.exists_norm_stripApprox_le_neg_one
#print axioms MobiusCPT.le_dist_cutSegment_one
#print axioms MobiusCPT.le_dist_cutSegment_neg_one
#print axioms MobiusCPT.exists_norm_iteratedDeriv_stripApprox_le_one
#print axioms MobiusCPT.exists_norm_iteratedDeriv_stripApprox_le_neg_one
#print axioms MobiusCPT.tendsto_stripApprox
#print axioms MobiusCPT.differentiableOn_stripApprox
#print axioms MobiusCPT.contDiffOn_stripApprox
#print axioms MobiusCPT.iteratedFDerivWithin_stripApprox_one
#print axioms MobiusCPT.iteratedFDerivWithin_stripApprox_neg_one
#print axioms MobiusCPT.stripApproxX
#print axioms MobiusCPT.stripApprox_circleExp
-- MobiusCPT/TestFunctions/AnalyticDensity.lean — [T26], Lemma 3.4 for `I_+`.
#print axioms MobiusCPT.upperAnglePicture
#print axioms MobiusCPT.isUpperFlat_upperAnglePicture
#print axioms MobiusCPT.toAngle_sub
#print axioms MobiusCPT.boostPicture
#print axioms MobiusCPT.isRapidlyDecaying_boostPicture
#print axioms MobiusCPT.approx
#print axioms MobiusCPT.errorAngle
#print axioms MobiusCPT.contDiff_errorAngle
#print axioms MobiusCPT.errorAngle_boostToAngle
#print axioms MobiusCPT.norm_iteratedFDeriv_circle_map_eq
#print axioms MobiusCPT.norm_iteratedFDeriv_circle_map_neg_eq
#print axioms MobiusCPT.cnorm_le_of_forall
#print axioms MobiusCPT.angleDeriv_eq_zero_of_suppUpper
#print axioms MobiusCPT.toAngle_error_eq
#print axioms MobiusCPT.exists_norm_angleDeriv_le
#print axioms MobiusCPT.contDiff_gaussConvReal
#print axioms MobiusCPT.eventually_boost_error_le
#print axioms MobiusCPT.tendsto_xRestrictUpper_approx
#print axioms MobiusCPT.lemma_3_4_density_upper
-- MobiusCPT/TestFunctions/AnalyticReflect.lean — the reflection `z ↦ conj z` and [T26], Lemma 3.4
-- for `I_-`.
#print axioms MobiusCPT.starTestFn
#print axioms MobiusCPT.toAngle_starTestFn
#print axioms MobiusCPT.starTestFn_starTestFn
#print axioms MobiusCPT.starTestFn_sub
#print axioms MobiusCPT.angleDeriv_starTestFn
#print axioms MobiusCPT.norm_angleDeriv_starTestFn
#print axioms MobiusCPT.cnorm_starTestFn
#print axioms MobiusCPT.suppUpper_starTestFn
#print axioms MobiusCPT.suppLower_starTestFn
#print axioms MobiusCPT.tendsto_starTestFn
#print axioms MobiusCPT.hasDerivAt_conj_conj
#print axioms MobiusCPT.AnalyticTestFn.conj
#print axioms MobiusCPT.xRestrictLower_conj
#print axioms MobiusCPT.lemma_3_4_density_lower
-- Issue #7, answering the adversarial review: the source's injectivity of `F ↦ F|_{S¹}` on `𝕆`.
#print axioms MobiusCPT.AnalyticTestFn.invExt
#print axioms MobiusCPT.AnalyticTestFn.invExt_of_ne
#print axioms MobiusCPT.AnalyticTestFn.diffContOnCl_invExt
#print axioms MobiusCPT.eqOn_Oexterior_of_xRestrictS1_eq
#print axioms MobiusCPT.AnalyticTestFn.evalSphere_congr
#print axioms MobiusCPT.periodic_eq_of_eq_on_Ico

-- MobiusCPT/Analysis/Strip.lean — [T26] Def. 3.1: the closed strip and the boundary-uniqueness
-- lemma behind "necessarily unique" (Issue #6).
#print axioms MobiusCPT.strip_eq
#print axioms MobiusCPT.mem_strip
#print axioms MobiusCPT.strip_eq_reProdIm
#print axioms MobiusCPT.interior_strip
#print axioms MobiusCPT.ofReal_mem_strip
#print axioms MobiusCPT.add_ofReal_mem_strip
#print axioms MobiusCPT.strip_add_ofReal
#print axioms MobiusCPT.add_ofReal_mem_strip_iff
#print axioms MobiusCPT.neg_mem_strip_iff
#print axioms MobiusCPT.strip_ofReal
#print axioms MobiusCPT.interior_strip_ofReal
#print axioms MobiusCPT.eqOn_zero_strip_of_ofReal
#print axioms MobiusCPT.eqOn_strip_of_eqOn_ofReal

-- MobiusCPT/Wightman/Vtilde.lean — [T26] Def. 3.1: `D(Ṽ_τ)`, uniqueness of the companion vector
-- via separation of points, and the compatible-functional characterisation (Issue #6).
#print axioms MobiusCPT.WightmanData.isBoostContinuation_eqOn
#print axioms MobiusCPT.WightmanData.vtildeVal_unique
#print axioms MobiusCPT.WightmanData.existsUnique_vtildeVal
#print axioms MobiusCPT.WightmanData.vtildeVal_vtildeMap
#print axioms MobiusCPT.WightmanData.vtildeMap_eq
#print axioms MobiusCPT.WightmanData.vtildeDom_and_vtildeMap_eq
#print axioms MobiusCPT.WightmanData.vtildeDom_iff
#print axioms MobiusCPT.WightmanData.vtilde_spec

-- MobiusCPT/Wightman/VtildeLinear.lean — [T26] Def. 3.1: `D(Ṽ_τ)` is a `ℂ`-submodule, `Ṽ_τ` is
-- linear on it, and the `LinearPMap` packaging (Issue #6).
#print axioms MobiusCPT.WightmanData.isBoostContinuation_zero
#print axioms MobiusCPT.WightmanData.IsBoostContinuation.add
#print axioms MobiusCPT.WightmanData.IsBoostContinuation.smul
#print axioms MobiusCPT.WightmanData.mem_vtildeDomain
#print axioms MobiusCPT.WightmanData.vtildeMap_add
#print axioms MobiusCPT.WightmanData.vtildeMap_smul
#print axioms MobiusCPT.WightmanData.vtildeMap_zero
#print axioms MobiusCPT.WightmanData.vtildePMap_domain
#print axioms MobiusCPT.WightmanData.vtildePMap_apply
#print axioms MobiusCPT.WightmanData.mem_vtildePMap_domain

-- MobiusCPT/Wightman/VtildeLaws.lean — [T26] Def. 3.1 and footnote 7: vacuum membership and the
-- real-translation law (Issue #6).
#print axioms MobiusCPT.WightmanData.IsBoostContinuation.add_ofReal
#print axioms MobiusCPT.WightmanData.IsBoostContinuation.precomp_boost
#print axioms MobiusCPT.WightmanData.IsBoostContinuation.postcomp_boost
#print axioms MobiusCPT.WightmanData.vtildeDom_add_ofReal_iff
#print axioms MobiusCPT.WightmanData.vtildeDom_add_ofReal_iff_boost
#print axioms MobiusCPT.WightmanData.vtilde_vacuum
#print axioms MobiusCPT.WightmanData.vtilde_translation

-- MobiusCPT/Wightman/VtildeReal.lean — [T26] Def. 3.1 real-parameter case, conditional on the
-- boost-orbit continuity of [CRTT25] Lemma 2.10(i) (Issue #6).
#print axioms MobiusCPT.WightmanData.vtilde_real_of_boostOrbitContinuous
#print axioms MobiusCPT.WightmanData.boostOrbitContinuous_of_vtilde_real
#print axioms MobiusCPT.WightmanData.u_smear
#print axioms MobiusCPT.WightmanData.u_smearedProductOn
#print axioms MobiusCPT.WightmanData.u_smearedProduct
#print axioms MobiusCPT.WightmanData.boostOrbitContinuous_of_beta_continuous

-- MobiusCPT/Analysis/FlatCalculus.lean — closed-interval flat gluing and the general flatness
-- transfer lemmas the complex boost needs (Issue #8).
#print axioms MobiusCPT.iteratedDerivWithin_iteratedDerivWithin
#print axioms MobiusCPT.exists_norm_iteratedDerivWithin_le_pow
#print axioms MobiusCPT.contDiff_zeroExtend_of_flat_contDiffOn
#print axioms MobiusCPT.iteratedDeriv_zeroExtendIcc
#print axioms MobiusCPT.exists_pow_bound_iteratedFDerivWithin
#print axioms MobiusCPT.iteratedFDerivWithin_comp_eq_zero_of_flat
#print axioms MobiusCPT.iteratedFDerivWithin_mul_eq_zero_of_flat
#print axioms MobiusCPT.iteratedDerivWithin_eq_zero_of_iteratedFDerivWithin_eq_zero

-- MobiusCPT/Analysis/FlatGluing.lean — periodisation agrees with its generator near the origin
-- (Issue #8).
#print axioms MobiusCPT.eqOn_periodize_of_support_le_half
#print axioms MobiusCPT.iteratedDeriv_periodize_eqOn

-- MobiusCPT/Analysis/ParamSlice.lean — smooth dependence on a parameter: the slice derivatives of
-- a jointly smooth function, and uniformity over a compact second factor (Issue #8).
#print axioms MobiusCPT.contDiffOn_sliceDeriv
#print axioms MobiusCPT.continuousOn_sliceDeriv
#print axioms MobiusCPT.hasDerivWithinAt_slice
#print axioms MobiusCPT.sliceDeriv_eq_iteratedDerivWithin
#print axioms MobiusCPT.eventually_forall_norm_sub_lt
#print axioms MobiusCPT.uniqueDiffOn_of_convex

-- MobiusCPT/Analysis/TestFnCurve.lean — [T26] Lemma 3.6: differentiability of a curve of test
-- functions in the locally convex sense, and the multilinear chain rule (Issue #8).
#print axioms MobiusCPT.cnorm_le_of_forall_angleDeriv
#print axioms MobiusCPT.angleDeriv_sub
#print axioms MobiusCPT.tendsto_testFn_of_forall_eventually
#print axioms MobiusCPT.hasTestFnDerivAt_iff_tendsto_slope
#print axioms MobiusCPT.hasDerivAt_of_multilinear

-- MobiusCPT/Mobius/ComplexBetaCore.lean — [T26] eq. (3.5) in pole-free form and the divided
-- inverted function carrying the `d = 0` removable singularity (Issue #8).
#print axioms MobiusCPT.cosh_add_re_mul_sinh_div
#print axioms MobiusCPT.cnum_neg_ne_zero_of_upper
#print axioms MobiusCPT.norm_cden_div_cnum_le_one
#print axioms MobiusCPT.cden_div_cnum_mem_closedBall
#print axioms MobiusCPT.cden_div_cnum_of_coe_eq_one
#print axioms MobiusCPT.cden_div_cnum_of_coe_eq_neg_one
#print axioms MobiusCPT.AnalyticTestFn.mul_invQuot
#print axioms MobiusCPT.AnalyticTestFn.invQuot_apply
#print axioms MobiusCPT.AnalyticTestFn.differentiableOn_invQuot
#print axioms MobiusCPT.AnalyticTestFn.contDiffOn_invQuot
#print axioms MobiusCPT.mapsTo_cden_div_cnum_closedBall

-- MobiusCPT/Mobius/ComplexBeta.lean — [T26] Definition 3.5, eqs. (3.4)-(3.5): the pointwise
-- complex boost and its source correspondence (Issue #8).
#print axioms MobiusCPT.zpow_boost_identity
#print axioms MobiusCPT.betaBoostVal_eq_mul_inv
#print axioms MobiusCPT.betaBoostVal_eq_source
#print axioms MobiusCPT.betaBoostVal_eq_source_of_one_le
#print axioms MobiusCPT.subsingleton_cden_neg_eq_zero

-- MobiusCPT/Mobius/ComplexBetaSmooth.lean — joint smoothness of the complex boost in the strip
-- parameter and the circle angle (Issue #8).
#print axioms MobiusCPT.mem_strip_I_mul_pi
#print axioms MobiusCPT.im_circleExp_nonneg
#print axioms MobiusCPT.uniqueDiffOn_strip_I_mul_pi
#print axioms MobiusCPT.uniqueDiffOn_stripUpper
#print axioms MobiusCPT.contDiffOn_betaBoostJoint
#print axioms MobiusCPT.contDiffOn_betaBoostAngle

-- MobiusCPT/Mobius/ComplexBetaFlat.lean — [T26] Definition 3.2: the divided inverted function
-- inherits the endpoint flatness of `F` (Issue #8).
#print axioms MobiusCPT.AnalyticTestFn.iteratedFDerivWithin_invQuot_eq_zero
#print axioms MobiusCPT.AnalyticTestFn.iteratedFDerivWithin_invQuot_one
#print axioms MobiusCPT.AnalyticTestFn.iteratedFDerivWithin_invQuot_neg_one
#print axioms MobiusCPT.AnalyticTestFn.toFun_one
#print axioms MobiusCPT.AnalyticTestFn.toFun_neg_one
#print axioms MobiusCPT.AnalyticTestFn.invQuot_one
#print axioms MobiusCPT.AnalyticTestFn.invQuot_neg_one

-- MobiusCPT/Mobius/ComplexBetaDef.lean — [T26] Definition 3.5: `β_d(v_τ)F|_{I_+}` as an element
-- of `C_0^∞(I_+)` (Issue #8).
#print axioms MobiusCPT.betaBoostVal_circleExp_eq
#print axioms MobiusCPT.contDiffOn_betaBoostPre
#print axioms MobiusCPT.contDiffOn_betaBoostRatio
#print axioms MobiusCPT.mapsTo_betaBoostRatio
#print axioms MobiusCPT.betaBoostRatio_zero
#print axioms MobiusCPT.betaBoostRatio_pi
#print axioms MobiusCPT.iteratedDerivWithin_betaBoostVal_circleExp_zero
#print axioms MobiusCPT.iteratedDerivWithin_betaBoostVal_circleExp_pi
#print axioms MobiusCPT.contDiff_betaBoostCut
#print axioms MobiusCPT.isUpperFlat_betaBoostCut
#print axioms MobiusCPT.toAngle_betaBoost
#print axioms MobiusCPT.suppUpper_betaBoost
#print axioms MobiusCPT.betaBoost_apply_circleExp

-- MobiusCPT/Mobius/ComplexBetaLawsCore.lean — the boundary parameters of the strip (Issue #8).
#print axioms MobiusCPT.cosh_add_re_mul_sinh_pos
#print axioms MobiusCPT.cden_neg_ofReal_ne_zero
#print axioms MobiusCPT.vApplyNegSphere_ofReal
#print axioms MobiusCPT.cden_neg_I_mul_pi_ne_zero
#print axioms MobiusCPT.vApplyNegSphere_I_mul_pi
#print axioms MobiusCPT.cosh_add_re_mul_sinh_I_mul_pi
#print axioms MobiusCPT.neg_one_zpow_sub_one

-- MobiusCPT/Mobius/ComplexBetaCont.lean — [T26] Lemma 3.6, first clause: continuity of
-- `τ ↦ β_d(v_τ)F|_{I_+}` on the closed strip (Issue #8).
#print axioms MobiusCPT.continuousOn_betaBoostSlice
#print axioms MobiusCPT.betaBoostSlice_eq
#print axioms MobiusCPT.angleDeriv_betaBoost_of_mem
#print axioms MobiusCPT.angleDeriv_betaBoost_of_notMem
#print axioms MobiusCPT.continuousOn_betaBoost

-- MobiusCPT/Mobius/ComplexBetaLaws.lean — [T26] eqs. (3.4)-(3.5) and Lemma 3.7: agreement with
-- the real conformal action, the semigroup law, and the value at `τ = iπ` (Issue #8).
#print axioms MobiusCPT.betaBoost_ofReal
#print axioms MobiusCPT.betaBoost_ofReal_mob
#print axioms MobiusCPT.cnum_neg_add_ofReal
#print axioms MobiusCPT.cden_neg_add_ofReal
#print axioms MobiusCPT.betaBoostVal_add_ofReal
#print axioms MobiusCPT.beta_boostMat_betaBoost
#print axioms MobiusCPT.betaBoost_I_mul_pi

-- MobiusCPT/Mobius/ComplexBetaHoloSlice.lean — [T26] Lemma 3.6: holomorphy in the strip parameter
-- of the complex boost and of each of its angle derivatives (Issue #8).
#print axioms MobiusCPT.norm_cden_div_cnum_lt_one
#print axioms MobiusCPT.differentiableOn_betaBoostVal
#print axioms MobiusCPT.differentiableOn_betaBoostSlice

-- MobiusCPT/Mobius/ComplexBetaDeriv.lean — [T26] Lemma 3.6: the parameter derivative of every
-- angle derivative of the complex boost, and its joint continuity (Issue #8).
#print axioms MobiusCPT.continuousOn_betaBoostSliceDot
#print axioms MobiusCPT.hasDerivAt_betaBoostSlice
#print axioms MobiusCPT.deriv_betaBoostSlice
#print axioms MobiusCPT.betaBoostSliceDot_eq_zero_of_endpoint

-- MobiusCPT/Mobius/ComplexBetaDerivFn.lean — [T26] Lemma 3.6: the angle and parameter derivatives
-- of the complex boost commute, and the parameter derivative is itself in C_0^∞(I_+) (Issue #8).
#print axioms MobiusCPT.betaBoostSliceDot_succ
#print axioms MobiusCPT.sliceDeriv_betaBoostSliceDot
#print axioms MobiusCPT.contDiffOn_betaBoostSliceDot_angle
#print axioms MobiusCPT.iteratedDerivWithin_betaBoostSliceDot_angle
#print axioms MobiusCPT.contDiff_betaBoostDerivCut
#print axioms MobiusCPT.isUpperFlat_betaBoostDerivCut
#print axioms MobiusCPT.toAngle_betaBoostDeriv
#print axioms MobiusCPT.suppUpper_betaBoostDeriv
#print axioms MobiusCPT.angleDeriv_betaBoostDeriv_of_mem
#print axioms MobiusCPT.angleDeriv_betaBoostDeriv_of_notMem

-- MobiusCPT/Mobius/ComplexBetaHolo.lean — [T26] Lemma 3.6: the complex boost is differentiable in
-- the strip parameter as a curve of test functions, in the locally convex sense (Issue #8).
#print axioms MobiusCPT.eventually_forall_norm_slice_diff_quotient_sub_lt
#print axioms MobiusCPT.eventually_forall_norm_angleDeriv_diff_quotient_sub_lt
#print axioms MobiusCPT.hasTestFnDerivAt_betaBoost
#print axioms MobiusCPT.differentiableOn_clm_comp_betaBoost

-- MobiusCPT/Wightman/BoostCurve.lean — [T26] Lemma 3.6, second clause: the scalar functions of
-- Definition 3.1 built from the complex boost are continuous on the closed strip and holomorphic
-- in its interior (Issue #8).
#print axioms MobiusCPT.continuousOn_compatApply_multiSmear_betaBoost
#print axioms MobiusCPT.differentiableOn_compatApply_multiSmear_betaBoost
#print axioms MobiusCPT.continuousOn_compatApply_smearedProduct_betaBoost
#print axioms MobiusCPT.differentiableOn_compatApply_smearedProduct_betaBoost

-- Audit completion for Issue #8: every remaining public theorem in the files this PR adds or
-- extends, so that the live audit covers the whole exported surface and not only the headline
-- results.  The five `FlatGluing` entries pre-date this PR and are added here for completeness,
-- the file having been extended by it.
#print axioms MobiusCPT.zeroExtend_eq_of_mem
#print axioms MobiusCPT.zeroExtend_eq_zero_of_notMem
#print axioms MobiusCPT.zeroExtendIcc_eqOn
#print axioms MobiusCPT.zeroExtendIcc_eq_zero_of_notMem
#print axioms MobiusCPT.iteratedDeriv_zeroExtendIcc_left
#print axioms MobiusCPT.iteratedDeriv_zeroExtendIcc_right
#print axioms MobiusCPT.iteratedDeriv_zeroExtendIcc_of_notMem
#print axioms MobiusCPT.stepRight_of_le
#print axioms MobiusCPT.stepRight_of_lt
#print axioms MobiusCPT.deriv_stepRight
#print axioms MobiusCPT.cutIcc_eq_of_mem
#print axioms MobiusCPT.cutIcc_eq_zero_of_notMem
#print axioms MobiusCPT.sliceDeriv_succ
#print axioms MobiusCPT.AnalyticTestFn.invQuot_of_ne
#print axioms MobiusCPT.AnalyticTestFn.invQuot_zero
#print axioms MobiusCPT.im_I_mul_pi
#print axioms MobiusCPT.cnum_neg_circleExp_ne_zero
#print axioms MobiusCPT.betaBoostVal_circleExp_zero
#print axioms MobiusCPT.betaBoostVal_circleExp_pi
#print axioms MobiusCPT.uniqueDiffOn_discNear
#print axioms MobiusCPT.zero_notMem_discNear
#print axioms MobiusCPT.discNear_eventuallyEq
#print axioms MobiusCPT.mapsTo_inv_discNear
#print axioms MobiusCPT.cosh_add_re_mul_sinh_ofReal
#print axioms MobiusCPT.ofReal_mem_strip_I_mul_pi
#print axioms MobiusCPT.cnum_neg_I_mul_pi
#print axioms MobiusCPT.cden_neg_I_mul_pi
#print axioms MobiusCPT.cosh_I_mul_pi
#print axioms MobiusCPT.sinh_I_mul_pi
#print axioms MobiusCPT.I_mul_pi_mem_strip
#print axioms MobiusCPT.forall_norm_angleDeriv_betaBoost_sub_lt
#print axioms MobiusCPT.betaBoost_apply_of_mem_upper

-- Issue #38 ([CRTT25], Lemma 2.10(i)): the real-parameter joint-smoothness-to-continuity core,
-- and boost/rotation continuity of the conformal action on test functions.
#print axioms MobiusCPT.continuous_of_jointlySmooth_periodic
#print axioms MobiusCPT.beta_rotMat_apply
#print axioms MobiusCPT.Mob.beta_rot_apply
#print axioms MobiusCPT.contDiff_betaRotJoint
#print axioms MobiusCPT.continuous_beta_rot
#print axioms MobiusCPT.boostMat_neg_alpha
#print axioms MobiusCPT.boostMat_neg_beta
#print axioms MobiusCPT.j_boostMat_neg_eq
#print axioms MobiusCPT.contMDiff_boostAngleNegSmul
#print axioms MobiusCPT.contDiff_betaBoostJoint
#print axioms MobiusCPT.continuous_beta_boost
#print axioms MobiusCPT.hbeta_mobiusActionMobTestFn

-- Issue #38, Contract.lean discharge: `vtilde_real`, byte-identical statement text, for the
-- `WightmanBundle` now fixed to `Mob`/`mobiusActionMobTestFn`
-- (docs/adr/0001-fix-mobius-group-in-bundle.md).
#print axioms MobiusCPT.WightmanBundle.vtilde_real

-- Issue #9, Block A ([T26], Lemma 3.7(i)): the `G_λ` continuation family built from `betaBoost`
-- is an `IsBoostContinuation` witness between the upper-restricted smeared product and the
-- `betaBoost`-smeared product, assembled from Issue #8/#38's landed Lemma 3.6 and covariance
-- infrastructure. Contract.lean discharge: `lemma_3_7`, byte-identical statement text.
#print axioms MobiusCPT.strip_subset_strip_I_mul_pi
#print axioms MobiusCPT.WightmanData.isBoostContinuation_betaBoost
#print axioms MobiusCPT.WightmanData.lemma_3_7
#print axioms MobiusCPT.WightmanBundle.lemma_3_7

-- Issue #9, Block B ([T26], owner bridge 1, 2026-08-28): the `n ≤ 0` Fourier coefficients of
-- `inv (xRestrictS1 F)` vanish, via the Cauchy integral formula (n = 0, the load-bearing zero
-- mode) and Cauchy's theorem (n < 0) applied to `F.invExt`'s `DiffContOnCl` extension (#7).
-- Composed with the landed (#26) `smear_vac_eq_zero_of_fourierCoef_eq_zero'`, this discharges
-- Contract.lean's `theorem_wanted w3_vacuum_annihilation`, byte-identical statement text.
#print axioms MobiusCPT.toAngle_inv_xRestrictS1
#print axioms MobiusCPT.fourierCoef_inv_xRestrictS1_eq
#print axioms MobiusCPT.fourierCoef_inv_xRestrictS1_eq_zero_of_le_zero
#print axioms MobiusCPT.WightmanData.w3_vacuum_annihilation
#print axioms MobiusCPT.WightmanBundle.w3_vacuum_annihilation

-- Issue #9, Block C infrastructure (owner bridge 2, 2026-08-28): the general (W2)-through-a-
-- limit bridge. Given a sequence of test functions with disjoint support from a fixed `f` at
-- every finite stage, converging to a limit `g` that need not itself have disjoint support
-- from `f`, the two smearing orders still agree — passed through every compatible functional
-- (never a direct vector limit in `𝓓`) and upgraded to a vector identity by regularity. Takes
-- the approximating sequence as given; does not itself build the endpoint cutoff sequence.
#print axioms MobiusCPT.WightmanStruct.continuous_compatApply_smear_smear_snd
#print axioms MobiusCPT.WightmanStruct.continuous_compatApply_smear_smear_fst
#print axioms MobiusCPT.WightmanStruct.compatApply_smear_comm_of_tendsto
#print axioms MobiusCPT.WightmanStruct.smear_comm_of_tendsto

-- Issue #9, Block C infrastructure: a pure single-variable calculus lemma, independent of
-- this project's TestFn/Circle types. Given a smooth function vanishing outside an open
-- interval, produces a sequence of smooth functions each vanishing outside a compact
-- sub-interval strictly inside it, converging together with every derivative order,
-- uniformly over all of ℝ. This is the real-analysis core of [T26]'s endpoint cutoff
-- construction (docs/math/pct-theorem.md's "cutoff-and-continuity argument" for Lemma 3.7).
#print axioms MobiusCPT.exists_contDiff_zero_outside_compact_tendstoUniformly

-- Issue #9, Block C: the TestFn-specific wiring completing the endpoint cutoff construction.
-- Builds an actual sequence of test functions, each supported strictly inside the open
-- semicircle (not just the closed one SuppLower/SuppUpper give), converging to a given
-- SuppLower/SuppUpper test function; and the two small connecting lemmas showing that a
-- tsupport bound inside the open opposite arc gives genuine DisjointSupport against a field
-- supported in the other closed semicircle -- the fact SuppUpper/SuppLower alone cannot give,
-- since closed supports may touch at +-1.
#print axioms MobiusCPT.exists_tendsto_of_suppLower
#print axioms MobiusCPT.exists_tendsto_of_suppUpper
#print axioms MobiusCPT.disjointSupport_of_suppUpper_of_tsupport_subset_lowerArc
#print axioms MobiusCPT.disjointSupport_of_suppLower_of_tsupport_subset_upperArc

-- Issue #9, Block D core: the combinatorial sign-reversal identity behind [T26] Lemma 3.7(ii),
-- [CRTT25]'s `phi_1(g_1)...phi_k(g_k)Omega = (-1)^k phi_k(h_k)...phi_1(h_1)Omega`. The first
-- lemma commutes one SuppLower operator past a whole product of SuppUpper-smeared operators
-- (induction on the list, invoking the (W2)-through-a-limit bridge at each step); the second
-- is the sign-reversal induction itself, using the vacuum-annihilation identity
-- (w3_vacuum_annihilation, on the sum of the two endpoint restrictions) once per list entry.
-- Final assembly into lemma_3_7_at_ipi is a separate, later step.
#print axioms MobiusCPT.WightmanStruct.smear_comm_smearedProductOn_of_suppLower_of_forall_suppUpper
#print axioms MobiusCPT.WightmanData.smearedProduct_invLower_eq_smearedProduct_invUpper_reverse

-- Issue #9, final assembly ([T26], Lemma 3.7(ii)): combines Lemma 3.7(i), the conformal-factor
-- sign betaBoost_I_mul_pi, and the sign-reversal core above into the analytic-core vector at
-- tau = i*pi. Contract.lean discharge: `lemma_3_7_at_ipi`, byte-identical statement text. This
-- completes Issue #9 -- both Lemma 3.7(i) and (ii) are now proved theorems.
#print axioms MobiusCPT.WightmanData.lemma_3_7_at_ipi
#print axioms MobiusCPT.WightmanBundle.lemma_3_7_at_ipi

-- Issue #10, Block A ([T26], Lemma 3.8): joint continuity of a finite multilinear functional
-- on TestFn gives a product bound in one common defining C^N norm.
#print axioms MobiusCPT.cnorm_bound_of_continuous_multilinear

-- Issue #10, Block B core: the real angle lift of the negative real boost v_{-t}, defined as
-- the antiderivative of the reciprocal automorphy-factor base and identified with the boost
-- action by an ODE-uniqueness argument (both sides solve y' = I y / boostP t with the same
-- value 1 at theta = 0). Valid on the whole circle, not the boost-chart route.
#print axioms MobiusCPT.sq_add_one_eq_two_mul_re
#print axioms MobiusCPT.boostPz_pos
#print axioms MobiusCPT.boostP_pos
#print axioms MobiusCPT.continuous_boostP
#print axioms MobiusCPT.continuous_boostPInv
#print axioms MobiusCPT.boostPz_smul_eq
#print axioms MobiusCPT.boostMat_neg_smul_one
#print axioms MobiusCPT.boostAngle_zero
#print axioms MobiusCPT.hasDerivAt_boostAngle
#print axioms MobiusCPT.hasDerivAt_boostSmulExp
#print axioms MobiusCPT.hasDerivAt_circleExp_boostAngle
#print axioms MobiusCPT.circleExp_boostAngle
#print axioms MobiusCPT.circleExp_boostAngle'

-- Issue #10, Block B growth bounds: exponential-in-|t| growth of the iterated angle
-- derivatives of boostP and its antiderivative boostAngle, via the Faa di Bruno bound
-- norm_iteratedFDeriv_comp_le' on the reciprocal restricted away from its zero.
#print axioms MobiusCPT.iteratedDeriv_cos_eq
#print axioms MobiusCPT.norm_iteratedDeriv_cos_le
#print axioms MobiusCPT.boostP_eq
#print axioms MobiusCPT.iteratedDeriv_boostP_succ_eq
#print axioms MobiusCPT.abs_sinh_le_exp_abs
#print axioms MobiusCPT.norm_iteratedDeriv_boostP_le
#print axioms MobiusCPT.contDiff_boostP
#print axioms MobiusCPT.exp_neg_abs_le_boostP
#print axioms MobiusCPT.iteratedDeriv_inv_eq
#print axioms MobiusCPT.norm_iteratedDeriv_inv_le_of_ge
#print axioms MobiusCPT.norm_iteratedDeriv_inv_le_exp
#print axioms MobiusCPT.contDiff_boostAngle
#print axioms MobiusCPT.norm_iteratedDeriv_boostAngle_le

-- Issue #10, Block B target: every fixed C^N seminorm of a real-boosted test function grows
-- at most exponentially in the boost parameter, uniformly in the test function.
#print axioms MobiusCPT.toAngle_beta_boost_eq
#print axioms MobiusCPT.cnorm_boost_le

-- Issue #10, Block C ([T26], Lemma 3.8): telescope the multilinear functional slot by slot,
-- bridge equal-length zipped lists to Fin-indexed tuples, and combine Blocks A and B into the
-- contract estimate. Contract.lean discharge: `lemma_3_8`, byte-identical statement text.
#print axioms MobiusCPT.MultilinearMap.norm_sub_le_of_cnorm_bound
#print axioms MobiusCPT.List.zip_eq_ofFn_get_of_length_eq
#print axioms MobiusCPT.WightmanData.lemma_3_8
#print axioms MobiusCPT.WightmanBundle.lemma_3_8

-- Issue #11, Block A: a Gaussian-weighted Phragmén–Lindelöf maximum principle on the closed
-- strip {0 ≤ Im τ ≤ π}, pure complex analysis independent of the Wightman/Möbius layers, used
-- to assemble [T26] Lemma 3.9's interior-to-boundary estimate in Block C.
#print axioms MobiusCPT.strip_max_principle

-- Issue #11, Block B: [T26] Lemma 3.9's interior growth estimate. Compactness of [0,π] gives a
-- uniform C^N bound for the complex boost, then the translation law for vtildeMap and Lemma 3.8
-- combine to give exponential growth of the continued-boost difference on the closed strip.
#print axioms MobiusCPT.WightmanData.lemma_3_9_interior_growth

-- Issue #11, Block B (part 2): the continued-boost difference is DiffContOnCl on the open
-- horizontal strip {0 < Im τ < π} — differentiable there, continuous on its closure. Follows
-- directly from Lemma 3.7(i) identifying the vectors with the complex-boost curves on the
-- whole closed strip, where Lemma 3.6 already gives continuity and interior holomorphy.
#print axioms MobiusCPT.WightmanData.lemma_3_9_diffContOnCl

-- Issue #11, Block C boundary estimates: [T26] Lemma 3.9's two boundary bounds. The lower
-- boundary reduces to Lemma 3.8 via the unconditional WightmanBundle.vtilde_real; the upper
-- boundary reduces to Lemma 3.8 applied to the reversed field list via Lemma 3.7(ii)'s sign
-- and reversal identity, with the reversed/inverted product and max controls shown equal to
-- the unreversed ones.
#print axioms MobiusCPT.WightmanBundle.lemma_3_9_lower_bound
#print axioms MobiusCPT.WightmanBundle.lemma_3_9_upper_bound

-- Issue #11, Block C final assembly: reconciles the two boundary estimates to common constants
-- and applies the Gaussian-weighted strip maximum principle to prove [T26] Lemma 3.9.
#print axioms MobiusCPT.WightmanBundle.lemma_3_9

-- Issue #12, Block L1 ([T26] Theorem 3.10, WLOG transport): the rotation-by-pi symmetry used to
-- derive part (iii) from part (ii). `Mob.rot_pi_conj_boost` conjugates the boost flow to its
-- negation; `negTestFn` is pullback by that rotation, equal to `beta_d(r_pi)` for every
-- conformal dimension, an involution, exchanges `SuppUpper`/`SuppLower`, commutes with
-- test-function inversion, and preserves every `C^N` seminorm (hence is continuous).
#print axioms MobiusCPT.Mob.rot_pi_conj_boost
#print axioms MobiusCPT.Mob.rot_pi_sq
#print axioms MobiusCPT.Mob.rot_pi_inv
#print axioms MobiusCPT.coe_smul_rot_pi
#print axioms MobiusCPT.beta_rot_pi_eq_negTestFn
#print axioms MobiusCPT.negTestFn_negTestFn
#print axioms MobiusCPT.suppLower_iff_suppUpper_negTestFn
#print axioms MobiusCPT.suppUpper_iff_suppLower_negTestFn
#print axioms MobiusCPT.inv_negTestFn
#print axioms MobiusCPT.toAngle_negTestFn
#print axioms MobiusCPT.angleDeriv_negTestFn
#print axioms MobiusCPT.norm_angleDerivB_negTestFn
#print axioms MobiusCPT.cnorm_negTestFn
#print axioms MobiusCPT.continuous_negTestFn

-- Issue #12, Block L2 ([T26] Theorem 3.10, WLOG transport): Compat transport under U(r_pi),
-- rotation intertwining a boost with its negation, and the resulting mirror lemma
-- VtildeDom(-tau) Phi <-> VtildeDom tau (U(r_pi) Phi), with the matching companion-value law
-- for vtildeMap.
#print axioms MobiusCPT.neg_mem_interior_strip_iff
#print axioms MobiusCPT.WightmanData.U_boost_rot_pi_comm
#print axioms MobiusCPT.WightmanData.isBoostContinuation_mirror
#print axioms MobiusCPT.WightmanData.vtildeDom_mirror_iff
#print axioms MobiusCPT.WightmanData.vtildeMap_mirror

-- Issue #12, Block U1 (part a) ([T26] Theorem 3.10, the limiting continuation family):
-- Lemma 3.4 analytic approximants of an arbitrary upper-supported list are uniformly Cauchy on
-- every compact subset of the closed strip via Lemma 3.9, giving a pointwise limit `limitG`
-- that is holomorphic on the open strip.
#print axioms MobiusCPT.WightmanData.approxList_length
#print axioms MobiusCPT.WightmanData.limG_eq
#print axioms MobiusCPT.WightmanData.continuousOn_limG
#print axioms MobiusCPT.WightmanData.differentiableOn_limG
#print axioms MobiusCPT.WightmanData.uniformCauchySeqOn_limG
#print axioms MobiusCPT.WightmanData.tendsto_limG
#print axioms MobiusCPT.WightmanData.tendstoLocallyUniformlyOn_limG
#print axioms MobiusCPT.WightmanData.differentiableOn_limitG

-- Issue #12, Block U1 (part b): closed-strip continuity of the limiting continuation family,
-- via a direct TendstoLocallyUniformlyOn construction on the closed strip (a compact
-- neighborhood strip ∩ closedBall at every point, since the strip is closed rather than open).
#print axioms MobiusCPT.WightmanData.tendstoLocallyUniformlyOn_limG_strip
#print axioms MobiusCPT.WightmanData.continuousOn_limitG

-- Issue #12, Block U2 ([T26] Theorem 3.10(ii), boundary identification): the two boundary
-- values of the limiting continuation family are identified with concrete vectors (the plain
-- boost orbit on the real axis via the real-parameter case of Vtilde, and the reversed,
-- inverted, sign-twisted product on the Im tau = pi line via Lemma 3.7(ii) and the real
-- translation law), packaging IsBoostContinuation and discharging thm_3_10_ii's core content
-- for smearedProduct l.
#print axioms MobiusCPT.continuous_inv
#print axioms MobiusCPT.WightmanData.tendsto_limG_ofReal
#print axioms MobiusCPT.WightmanData.tendsto_limG_ipi_add_ofReal
#print axioms MobiusCPT.WightmanData.limitG_ofReal
#print axioms MobiusCPT.WightmanData.limitG_ipi_add_ofReal
#print axioms MobiusCPT.WightmanData.isBoostContinuation_limitG
#print axioms MobiusCPT.WightmanData.thm_3_10_ii_core

-- Issue #12, Block A (assembly, [T26] Theorem 3.10 complete): part (iii) is derived from part
-- (ii) by the rotation-by-pi transport at the level of Definition 3.1 -- the encoding of the
-- source's "without loss of generality, we only consider I+" -- using U(r_pi) = negTestFn on
-- test functions (Block L1) and the mirror lemma for VtildeDom/vtildeMap (Block L2); part (i)
-- is derived from (ii)/(iii) by linearity of the continuation domain (a Submodule) applied to
-- the finite-linear-combination characterization of P(I+)Omega/P(I-)Omega. This discharges
-- MobiusCPT.Contract's `theorem_wanted thm_3_10_i/ii/iii`, byte-identical statement text,
-- completing [T26] Theorem 3.10.
#print axioms MobiusCPT.WightmanData.thm_3_10_iii_core
#print axioms MobiusCPT.WightmanData.thm_3_10_i_core
#print axioms MobiusCPT.WightmanBundle.thm_3_10_i
#print axioms MobiusCPT.WightmanBundle.thm_3_10_ii
#print axioms MobiusCPT.WightmanBundle.thm_3_10_iii
