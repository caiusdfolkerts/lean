module
prelude
public import ResidualGraphKernel
public import GraphInputsRow29Part00281Data
public import GraphLargeRow29Case01592Data

public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
open SharedGraphCellPool ResidualGraphKernel

namespace Diagnostic

theorem case00 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record005) 0 126 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record005 (by decide +kernel)

theorem case01 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record004) 0 142 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record004 (by decide +kernel)

theorem case02 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record003) 0 131 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record003 (by decide +kernel)

theorem case03 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record001) 0 120 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record001 (by decide +kernel)

theorem case04 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphLargeRow29Case01592.record000) 0 106 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphLargeRow29Case01592.record000 (by decide +kernel)

end Diagnostic
