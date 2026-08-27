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
#print axioms MobiusCPT.DisjointSupport.eq_zero_of_ne
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
