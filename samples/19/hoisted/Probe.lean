module
prelude
import ResidualGraphKernel
import GraphInputsRow19Part00034Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
open SharedGraphCellPool ResidualGraphKernel

namespace Diagnostic

theorem case00 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053) 0 82 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053 (by decide +kernel)

theorem case01 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record046) 0 76 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record046 (by decide +kernel)

theorem case02 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record049) 0 79 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record049 (by decide +kernel)

theorem case03 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record024) 0 76 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record024 (by decide +kernel)

end Diagnostic
