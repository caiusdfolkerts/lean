module
prelude
public import ResidualGraphKernel
public import GraphInputsRow26Part00077Data

public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
open SharedGraphCellPool ResidualGraphKernel

namespace Diagnostic

private theorem case00_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record014) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case00_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record014) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem case00 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record014) 0 103 :=
  (interval_append _ 0 64 103 case00_0 case00_64)

private theorem case01_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record001) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case01_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record001) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem case01 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record001) 0 103 :=
  (interval_append _ 0 64 103 case01_0 case01_64)

private theorem case02_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record007) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case02_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record007) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem case02 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record007) 0 106 :=
  (interval_append _ 0 64 106 case02_0 case02_64)

private theorem case03_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record004) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case03_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record004) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem case03 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record004) 0 105 :=
  (interval_append _ 0 64 105 case03_0 case03_64)

end Diagnostic
