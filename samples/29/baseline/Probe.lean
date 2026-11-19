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

private theorem case00_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record005) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case00_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record005) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem case00 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record005) 0 126 :=
  (interval_append _ 0 64 126 case00_0 case00_64)

private theorem case01_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record004) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case01_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record004) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
private theorem case01_128 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record004) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem case01 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record004) 0 142 :=
  (interval_append _ 0 128 142 (interval_append _ 0 64 128 case01_0 case01_64) case01_128)

private theorem case02_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record003) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case02_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record003) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
private theorem case02_128 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record003) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem case02 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record003) 0 131 :=
  (interval_append _ 0 128 131 (interval_append _ 0 64 128 case02_0 case02_64) case02_128)

private theorem case03_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record001) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case03_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record001) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem case03 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record001) 0 120 :=
  (interval_append _ 0 64 120 case03_0 case03_64)

private theorem case04_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphLargeRow29Case01592.record000) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case04_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphLargeRow29Case01592.record000) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem case04 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphLargeRow29Case01592.record000) 0 106 :=
  (interval_append _ 0 64 106 case04_0 case04_64)

end Diagnostic
