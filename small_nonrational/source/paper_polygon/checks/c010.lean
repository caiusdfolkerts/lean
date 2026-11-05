module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 1280 through 1407. -/
theorem checked_1280_1296 : Interval targetCheck 1280 1296 :=
  interval_of_check targetCheck 1280 16 (by decide +kernel)

theorem checked_1296_1312 : Interval targetCheck 1296 1312 :=
  interval_of_check targetCheck 1296 16 (by decide +kernel)

theorem checked_1312_1328 : Interval targetCheck 1312 1328 :=
  interval_of_check targetCheck 1312 16 (by decide +kernel)

theorem checked_1328_1344 : Interval targetCheck 1328 1344 :=
  interval_of_check targetCheck 1328 16 (by decide +kernel)

theorem checked_1344_1360 : Interval targetCheck 1344 1360 :=
  interval_of_check targetCheck 1344 16 (by decide +kernel)

theorem checked_1360_1376 : Interval targetCheck 1360 1376 :=
  interval_of_check targetCheck 1360 16 (by decide +kernel)

theorem checked_1376_1392 : Interval targetCheck 1376 1392 :=
  interval_of_check targetCheck 1376 16 (by decide +kernel)

theorem checked_1392_1408 : Interval targetCheck 1392 1408 :=
  interval_of_check targetCheck 1392 16 (by decide +kernel)

theorem chunk_010 : Interval targetCheck 1280 1408 :=
  (interval_append targetCheck 1280 1344 1408 (interval_append targetCheck 1280 1312 1344 (interval_append targetCheck 1280 1296 1312 checked_1280_1296 checked_1296_1312) (interval_append targetCheck 1312 1328 1344 checked_1312_1328 checked_1328_1344)) (interval_append targetCheck 1344 1376 1408 (interval_append targetCheck 1344 1360 1376 checked_1344_1360 checked_1360_1376) (interval_append targetCheck 1376 1392 1408 checked_1376_1392 checked_1392_1408)))

end Nonrational.TerminalVerification.PaperPolygon
