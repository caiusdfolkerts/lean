module
prelude
public import ResidualGraphKernel
public import GraphInputsRow28Part00012Data

public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
open SharedGraphCellPool ResidualGraphKernel

namespace Diagnostic

theorem case00 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record055) 0 119 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record055 (by decide +kernel)

theorem case01 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record038) 0 118 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record038 (by decide +kernel)

theorem case02 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record048) 0 113 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record048 (by decide +kernel)

theorem case03 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record024) 0 108 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00012.record024 (by decide +kernel)

end Diagnostic
