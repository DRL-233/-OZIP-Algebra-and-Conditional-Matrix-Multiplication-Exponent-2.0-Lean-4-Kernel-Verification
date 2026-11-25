import OZIPVerification
import OZIPDecouplingN2
import OZIPDecouplingInductive
import OZIPTrialitySymmetrization
import OZIPTheorem5_1

namespace DRL233.OZIPUnified

/-! ## I. Finite N=2 spoke-decoupling certificate -/
abbrev n2_A_saturation := n2_A_bijective_saturation
abbrev n2_B_disjointness := n2_B_disjoint_bounds
abbrev n2_C_disjointness := n2_C_disjoint_bounds
abbrev n2_volume := n2_decoupled_volume

/-! ## II. All-N spoke-decoupling certificate -/
abbrev allN_spoke_coordinate_injectivity := psiN_injective
abbrev allN_spoke_block_disjointness := spoke_blocks_strictly_disjoint

/-! ## III. Z3 triality certificates -/
abbrev allN_triality_isotropy := z3_cyclic_symmetrization_isotropic
abbrev allN_triality_embedding_injective := trialityEmbed3N_injective

theorem triality_packing_bridge (N : Nat) :
    OZIPTheorem5_1.Z3TrialityPackingAt N (18 ^ N) := by
  simpa [OZIPTheorem5_1.Z3TrialityPackingAt, Z3TrialityFullPacking] using
    (z3_full_packing_block_count N)

theorem allN_packing_hypothesis :
    ∀ N : Nat,
      ∃ M_sym : Nat,
        OZIPTheorem5_1.Z3TrialityPackingAt N M_sym ∧ M_sym = 18 ^ N := by
  intro N
  exact ⟨18 ^ N, triality_packing_bridge N, rfl⟩

/-! ## IV. Exact rational triality exponent -/
theorem gamma_three_halves :
    OZIPTheorem5_1.IsTrialityExponentThreeHalves 3 2 := by
  unfold OZIPTheorem5_1.IsTrialityExponentThreeHalves
  omega

/-! ## V. Unified exact-exponent conclusion -/
theorem theorem_5_1_unified
    {w_num w_den : Nat}
    (h_schonhage_ozip : w_num * 3 ≤ 3 * 2 * w_den)
    (h_strassen_lower : 2 * w_den ≤ w_num) :
    w_num = 2 * w_den := by
  have hfinal :=
    OZIPTheorem5_1.theorem_5_1_omega_equals_two
      allN_packing_hypothesis
      gamma_three_halves
      h_schonhage_ozip
      h_strassen_lower
  exact hfinal.2

theorem theorem_5_1_full
    {w_num w_den : Nat}
    (h_schonhage_ozip : w_num * 3 ≤ 3 * 2 * w_den)
    (h_strassen_lower : 2 * w_den ≤ w_num) :
    (∀ N : Nat,
      OZIPTheorem5_1.Z3TrialityPackingAt N (18 ^ N)) ∧
      w_num = 2 * w_den := by
  exact OZIPTheorem5_1.theorem_5_1_omega_equals_two
    allN_packing_hypothesis
    gamma_three_halves
    h_schonhage_ozip
    h_strassen_lower

#print axioms theorem_5_1_unified
#print axioms theorem_5_1_full

end DRL233.OZIPUnified
