module
prelude
public import Papers.RawWitnesses.Type452Data

/-! Small ordinary kernel checks for Appendix B type 452. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Type452
open Papers.RationalWitnesses.Raw

theorem lowRanks_00 : (certificate.lowRanks 0).Valid coordinates := by decide +kernel

theorem low_ranks_check : ∀ k, (certificate.lowRanks k).Valid coordinates :=
  (Fin.cases lowRanks_00 (fun i => Fin.elim0 i))

end Papers.RationalWitnesses.RawWitnesses.Type452
