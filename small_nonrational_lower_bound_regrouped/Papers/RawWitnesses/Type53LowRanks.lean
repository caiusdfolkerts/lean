module
prelude
public import Papers.RawWitnesses.Type53Data

/-! Small ordinary kernel checks for Appendix B type 53. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Type53
open Papers.RationalWitnesses.Raw

theorem lowRanks_00 : (certificate.lowRanks 0).Valid coordinates := by decide +kernel

theorem lowRanks_01 : (certificate.lowRanks 1).Valid coordinates := by decide +kernel

theorem lowRanks_02 : (certificate.lowRanks 2).Valid coordinates := by decide +kernel

theorem lowRanks_03 : (certificate.lowRanks 3).Valid coordinates := by decide +kernel

theorem lowRanks_04 : (certificate.lowRanks 4).Valid coordinates := by decide +kernel

theorem lowRanks_05 : (certificate.lowRanks 5).Valid coordinates := by decide +kernel

theorem lowRanks_06 : (certificate.lowRanks 6).Valid coordinates := by decide +kernel

theorem low_ranks_check : ∀ k, (certificate.lowRanks k).Valid coordinates :=
  (Fin.cases lowRanks_00 (Fin.cases lowRanks_01 (Fin.cases lowRanks_02 (Fin.cases lowRanks_03 (Fin.cases lowRanks_04 (Fin.cases lowRanks_05 (Fin.cases lowRanks_06 (fun i => Fin.elim0 i))))))))

end Papers.RationalWitnesses.RawWitnesses.Type53
