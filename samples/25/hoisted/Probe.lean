module
prelude
import ResidualGraphKernel
import GraphInputsRow25Part00022Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
open SharedGraphCellPool ResidualGraphKernel

namespace Diagnostic

theorem case00 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record037) 0 112 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record037 (by decide +kernel)

theorem case01 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record032) 0 111 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record032 (by decide +kernel)

theorem case02 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record057) 0 108 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record057 (by decide +kernel)

theorem case03 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record005) 0 112 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record005 (by decide +kernel)

end Diagnostic
