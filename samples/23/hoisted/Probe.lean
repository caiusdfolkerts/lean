module
prelude
import ResidualGraphKernel
import GraphInputsRow23Part00029Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
open SharedGraphCellPool ResidualGraphKernel

namespace Diagnostic

theorem case00 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record015) 0 95 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record015 (by decide +kernel)

theorem case01 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record009) 0 96 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record009 (by decide +kernel)

theorem case02 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record008) 0 91 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record008 (by decide +kernel)

theorem case03 : Interval (localCheck Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record011) 0 96 :=
  localChecked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record011 (by decide +kernel)

end Diagnostic
