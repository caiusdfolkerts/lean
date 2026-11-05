module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 1024 through 1151. -/
theorem checked_1024_1040 : Interval targetCheck 1024 1040 :=
  interval_of_check targetCheck 1024 16 (by decide +kernel)

theorem checked_1040_1056 : Interval targetCheck 1040 1056 :=
  interval_of_check targetCheck 1040 16 (by decide +kernel)

theorem checked_1056_1072 : Interval targetCheck 1056 1072 :=
  interval_of_check targetCheck 1056 16 (by decide +kernel)

theorem checked_1072_1088 : Interval targetCheck 1072 1088 :=
  interval_of_check targetCheck 1072 16 (by decide +kernel)

theorem checked_1088_1104 : Interval targetCheck 1088 1104 :=
  interval_of_check targetCheck 1088 16 (by decide +kernel)

theorem checked_1104_1120 : Interval targetCheck 1104 1120 :=
  interval_of_check targetCheck 1104 16 (by decide +kernel)

theorem checked_1120_1136 : Interval targetCheck 1120 1136 :=
  interval_of_check targetCheck 1120 16 (by decide +kernel)

theorem checked_1136_1152 : Interval targetCheck 1136 1152 :=
  interval_of_check targetCheck 1136 16 (by decide +kernel)

theorem chunk_008 : Interval targetCheck 1024 1152 :=
  (interval_append targetCheck 1024 1088 1152 (interval_append targetCheck 1024 1056 1088 (interval_append targetCheck 1024 1040 1056 checked_1024_1040 checked_1040_1056) (interval_append targetCheck 1056 1072 1088 checked_1056_1072 checked_1072_1088)) (interval_append targetCheck 1088 1120 1152 (interval_append targetCheck 1088 1104 1120 checked_1088_1104 checked_1104_1120) (interval_append targetCheck 1120 1136 1152 checked_1120_1136 checked_1136_1152)))

end Nonrational.TerminalVerification.PaperPolygon
