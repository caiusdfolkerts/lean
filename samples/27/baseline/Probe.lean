module
prelude
import ResidualGraphKernel
import GraphInputsRow27Part00016Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
open SharedGraphCellPool ResidualGraphKernel

namespace Diagnostic

private theorem case00_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record029) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case00_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record029) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
private theorem case00_128 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record029) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem case00 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record029) 0 146 :=
  (interval_append _ 0 128 146 (interval_append _ 0 64 128 case00_0 case00_64) case00_128)

private theorem case01_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record026) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case01_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record026) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem case01 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record026) 0 120 :=
  (interval_append _ 0 64 120 case01_0 case01_64)

private theorem case02_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record002) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case02_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record002) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem case02 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record002) 0 111 :=
  (interval_append _ 0 64 111 case02_0 case02_64)

private theorem case03_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record009) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case03_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record009) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem case03 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record009) 0 106 :=
  (interval_append _ 0 64 106 case03_0 case03_64)

end Diagnostic
