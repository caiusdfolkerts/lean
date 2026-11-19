module
prelude
public import Papers.RawWitnesses.TypeA14Data

/-! Small ordinary kernel checks for Appendix B type A14. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.TypeA14
open Papers.RationalWitnesses.Raw


theorem low_ranks_check : ∀ k, (certificate.lowRanks k).Valid coordinates :=
  (fun i => Fin.elim0 i)

end Papers.RationalWitnesses.RawWitnesses.TypeA14
