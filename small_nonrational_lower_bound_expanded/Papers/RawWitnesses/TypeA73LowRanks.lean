module
prelude
public import Papers.RawWitnesses.TypeA73Data

/-! Small ordinary kernel checks for Appendix B type A73. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.TypeA73
open Papers.RationalWitnesses.Raw


theorem low_ranks_check : ∀ k, (certificate.lowRanks k).Valid coordinates :=
  (fun i => Fin.elim0 i)

end Papers.RationalWitnesses.RawWitnesses.TypeA73
