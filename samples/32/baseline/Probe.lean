module
prelude
import ResidualGraphKernel
import GraphInputsSix0Part00089Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
open SharedGraphCellPool ResidualGraphKernel

namespace Diagnostic

private theorem case00_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record015) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case00_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record015) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem case00 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record015) 0 127 :=
  (interval_append _ 0 64 127 case00_0 case00_64)

private theorem case01_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record029) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case01_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record029) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem case01 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record029) 0 127 :=
  (interval_append _ 0 64 127 case01_0 case01_64)

private theorem case02_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record018) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case02_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record018) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
private theorem case02_128 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record018) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem case02 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record018) 0 129 :=
  (interval_append _ 0 128 129 (interval_append _ 0 64 128 case02_0 case02_64) case02_128)

private theorem case03_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record016) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case03_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record016) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem case03 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record016) 0 121 :=
  (interval_append _ 0 64 121 case03_0 case03_64)

end Diagnostic
