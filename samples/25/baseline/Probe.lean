module
prelude
public import ResidualGraphKernel
public import GraphInputsRow25Part00022Data

public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
open SharedGraphCellPool ResidualGraphKernel

namespace Diagnostic

private theorem case00_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record037) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case00_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record037) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem case00 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record037) 0 112 :=
  (interval_append _ 0 64 112 case00_0 case00_64)

private theorem case01_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record032) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case01_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record032) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem case01 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record032) 0 111 :=
  (interval_append _ 0 64 111 case01_0 case01_64)

private theorem case02_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record057) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case02_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record057) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem case02 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record057) 0 108 :=
  (interval_append _ 0 64 108 case02_0 case02_64)

private theorem case03_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record005) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case03_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record005) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem case03 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record005) 0 112 :=
  (interval_append _ 0 64 112 case03_0 case03_64)

end Diagnostic
