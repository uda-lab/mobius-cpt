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
