module
prelude
import ResidualGraphKernel
import GraphInputsRow16Part00011Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
open SharedGraphCellPool ResidualGraphKernel

namespace Diagnostic

theorem case00 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016) 0 80 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record016 (by decide +kernel)

theorem case01 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record005) 0 78 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record005 (by decide +kernel)

theorem case02 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record004) 0 77 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record004 (by decide +kernel)

theorem case03 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record028) 0 71 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00011.record028 (by decide +kernel)

end Diagnostic
