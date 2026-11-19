module
prelude
import ResidualGraphKernel
import GraphInputsRow31Part00048Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
open SharedGraphCellPool ResidualGraphKernel

namespace Diagnostic

theorem case00 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00048.record002) 0 150 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00048.record002 (by decide +kernel)

theorem case01 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00048.record005) 0 122 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00048.record005 (by decide +kernel)

theorem case02 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00048.record001) 0 126 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00048.record001 (by decide +kernel)

theorem case03 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00048.record003) 0 136 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00048.record003 (by decide +kernel)

end Diagnostic
