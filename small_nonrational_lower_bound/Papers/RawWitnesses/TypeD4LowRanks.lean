module
prelude
public import Papers.RawWitnesses.TypeD4Data

/-! Small ordinary kernel checks for Appendix B type D4. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.TypeD4
open Papers.RationalWitnesses.Raw

theorem lowRanks_00 : (certificate.lowRanks 0).Valid coordinates := by decide +kernel

theorem lowRanks_01 : (certificate.lowRanks 1).Valid coordinates := by decide +kernel

theorem lowRanks_02 : (certificate.lowRanks 2).Valid coordinates := by decide +kernel

theorem low_ranks_check : ∀ k, (certificate.lowRanks k).Valid coordinates :=
  (Fin.cases lowRanks_00 (Fin.cases lowRanks_01 (Fin.cases lowRanks_02 (fun i => Fin.elim0 i))))

end Papers.RationalWitnesses.RawWitnesses.TypeD4
