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

theorem case00 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record014) 0 103 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record014 (by decide +kernel)

theorem case01 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record001) 0 103 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record001 (by decide +kernel)

theorem case02 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record007) 0 106 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record007 (by decide +kernel)

theorem case03 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record004) 0 105 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record004 (by decide +kernel)

end Diagnostic
