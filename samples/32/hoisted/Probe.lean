module
prelude
public import ResidualGraphKernel
public import GraphInputsSix0Part00089Data

public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
open SharedGraphCellPool ResidualGraphKernel

namespace Diagnostic

theorem case00 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record015) 0 127 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record015 (by decide +kernel)

theorem case01 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record029) 0 127 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record029 (by decide +kernel)

theorem case02 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record018) 0 129 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record018 (by decide +kernel)

theorem case03 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record016) 0 121 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record016 (by decide +kernel)

end Diagnostic
