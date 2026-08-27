-- Live axiom audit input, consumed by scripts/check-axioms.sh.
-- Run after `lake build`:   lake env lean scripts/print_axioms.lean
--
-- Append one `#print axioms` line for every public theorem a PR claims as a result.
-- APPEND-ONLY: removing or renaming a line is a `needs-decision` change.
import MobiusCPT

#print axioms MobiusCPT.placeholder_add_zero

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
