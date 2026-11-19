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

theorem case00 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record007) 0 93 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record007 (by decide +kernel)

theorem case01 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record009) 0 96 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record009 (by decide +kernel)

theorem case02 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record008) 0 96 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record008 (by decide +kernel)

theorem case03 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record010) 0 97 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141.record010 (by decide +kernel)

end Diagnostic
