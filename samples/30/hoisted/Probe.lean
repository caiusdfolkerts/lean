module
prelude
import ResidualGraphKernel
import GraphInputsRow30Part00030Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
open SharedGraphCellPool ResidualGraphKernel

namespace Diagnostic

theorem case00 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record033) 0 122 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record033 (by decide +kernel)

theorem case01 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record029) 0 115 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record029 (by decide +kernel)

theorem case02 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record038) 0 116 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record038 (by decide +kernel)

theorem case03 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record050) 0 119 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record050 (by decide +kernel)

end Diagnostic
