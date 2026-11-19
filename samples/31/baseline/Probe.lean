module
prelude
public import ResidualGraphKernel
public import GraphInputsRow31Part00048Data

public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
open SharedGraphCellPool ResidualGraphKernel

namespace Diagnostic

private theorem case00_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00048.record002) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case00_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00048.record002) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
private theorem case00_128 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00048.record002) 128 150 :=
  interval_of_check _ 128 22 (by decide +kernel)
theorem case00 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00048.record002) 0 150 :=
  (interval_append _ 0 128 150 (interval_append _ 0 64 128 case00_0 case00_64) case00_128)

private theorem case01_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00048.record005) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case01_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00048.record005) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem case01 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00048.record005) 0 122 :=
  (interval_append _ 0 64 122 case01_0 case01_64)

private theorem case02_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00048.record001) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case02_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00048.record001) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem case02 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00048.record001) 0 126 :=
  (interval_append _ 0 64 126 case02_0 case02_64)

private theorem case03_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00048.record003) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case03_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00048.record003) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
private theorem case03_128 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00048.record003) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem case03 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00048.record003) 0 136 :=
  (interval_append _ 0 128 136 (interval_append _ 0 64 128 case03_0 case03_64) case03_128)

end Diagnostic
