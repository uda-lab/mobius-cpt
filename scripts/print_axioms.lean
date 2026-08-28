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
