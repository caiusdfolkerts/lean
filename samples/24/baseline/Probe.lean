module
prelude
public import ResidualGraphKernel
public import GraphInputsRow24Part00141Data

public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
open SharedGraphCellPool ResidualGraphKernel

namespace Diagnostic

private theorem case00_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record007) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case00_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record007) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem case00 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record007) 0 93 :=
  (interval_append _ 0 64 93 case00_0 case00_64)

private theorem case01_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record009) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case01_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record009) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem case01 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record009) 0 96 :=
  (interval_append _ 0 64 96 case01_0 case01_64)

private theorem case02_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record008) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case02_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record008) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem case02 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record008) 0 96 :=
  (interval_append _ 0 64 96 case02_0 case02_64)

private theorem case03_0 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record010) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
private theorem case03_64 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record010) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem case03 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record010) 0 97 :=
  (interval_append _ 0 64 97 case03_0 case03_64)

end Diagnostic
