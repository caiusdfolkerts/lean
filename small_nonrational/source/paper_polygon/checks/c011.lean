module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 1408 through 1535. -/
theorem checked_1408_1424 : Interval targetCheck 1408 1424 :=
  interval_of_check targetCheck 1408 16 (by decide +kernel)

theorem checked_1424_1440 : Interval targetCheck 1424 1440 :=
  interval_of_check targetCheck 1424 16 (by decide +kernel)

theorem checked_1440_1456 : Interval targetCheck 1440 1456 :=
  interval_of_check targetCheck 1440 16 (by decide +kernel)

theorem checked_1456_1472 : Interval targetCheck 1456 1472 :=
  interval_of_check targetCheck 1456 16 (by decide +kernel)

theorem checked_1472_1488 : Interval targetCheck 1472 1488 :=
  interval_of_check targetCheck 1472 16 (by decide +kernel)

theorem checked_1488_1504 : Interval targetCheck 1488 1504 :=
  interval_of_check targetCheck 1488 16 (by decide +kernel)

theorem checked_1504_1520 : Interval targetCheck 1504 1520 :=
  interval_of_check targetCheck 1504 16 (by decide +kernel)

theorem checked_1520_1536 : Interval targetCheck 1520 1536 :=
  interval_of_check targetCheck 1520 16 (by decide +kernel)

theorem chunk_011 : Interval targetCheck 1408 1536 :=
  (interval_append targetCheck 1408 1472 1536 (interval_append targetCheck 1408 1440 1472 (interval_append targetCheck 1408 1424 1440 checked_1408_1424 checked_1424_1440) (interval_append targetCheck 1440 1456 1472 checked_1440_1456 checked_1456_1472)) (interval_append targetCheck 1472 1504 1536 (interval_append targetCheck 1472 1488 1504 checked_1472_1488 checked_1488_1504) (interval_append targetCheck 1504 1520 1536 checked_1504_1520 checked_1520_1536)))

end Nonrational.TerminalVerification.PaperPolygon
