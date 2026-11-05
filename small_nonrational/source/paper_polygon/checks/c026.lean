module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 3328 through 3455. -/
theorem checked_3328_3344 : Interval targetCheck 3328 3344 :=
  interval_of_check targetCheck 3328 16 (by decide +kernel)

theorem checked_3344_3360 : Interval targetCheck 3344 3360 :=
  interval_of_check targetCheck 3344 16 (by decide +kernel)

theorem checked_3360_3376 : Interval targetCheck 3360 3376 :=
  interval_of_check targetCheck 3360 16 (by decide +kernel)

theorem checked_3376_3392 : Interval targetCheck 3376 3392 :=
  interval_of_check targetCheck 3376 16 (by decide +kernel)

theorem checked_3392_3408 : Interval targetCheck 3392 3408 :=
  interval_of_check targetCheck 3392 16 (by decide +kernel)

theorem checked_3408_3424 : Interval targetCheck 3408 3424 :=
  interval_of_check targetCheck 3408 16 (by decide +kernel)

theorem checked_3424_3440 : Interval targetCheck 3424 3440 :=
  interval_of_check targetCheck 3424 16 (by decide +kernel)

theorem checked_3440_3456 : Interval targetCheck 3440 3456 :=
  interval_of_check targetCheck 3440 16 (by decide +kernel)

theorem chunk_026 : Interval targetCheck 3328 3456 :=
  (interval_append targetCheck 3328 3392 3456 (interval_append targetCheck 3328 3360 3392 (interval_append targetCheck 3328 3344 3360 checked_3328_3344 checked_3344_3360) (interval_append targetCheck 3360 3376 3392 checked_3360_3376 checked_3376_3392)) (interval_append targetCheck 3392 3424 3456 (interval_append targetCheck 3392 3408 3424 checked_3392_3408 checked_3408_3424) (interval_append targetCheck 3424 3440 3456 checked_3424_3440 checked_3440_3456)))

end Nonrational.TerminalVerification.PaperPolygon
