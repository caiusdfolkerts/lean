module
prelude
public import ResidualGraphKernel
public import GraphInputsRow27Part00016Data

public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
open SharedGraphCellPool ResidualGraphKernel

namespace Diagnostic

theorem case00 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record029) 0 146 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record029 (by decide +kernel)

theorem case01 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record026) 0 120 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record026 (by decide +kernel)

theorem case02 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record002) 0 111 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record002 (by decide +kernel)

theorem case03 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record009) 0 106 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00016.record009 (by decide +kernel)

end Diagnostic
