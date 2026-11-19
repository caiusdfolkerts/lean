module
prelude
import ResidualGraphKernel
import GraphInputsRow16Part00000Data
import GraphInputsRow19Part00000Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
open SharedGraphCellPool ResidualGraphKernel

namespace Diagnostic

theorem case00 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record006) 0 63 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record006 (by decide +kernel)

theorem case01 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record021) 0 63 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00000.record021 (by decide +kernel)

end Diagnostic
