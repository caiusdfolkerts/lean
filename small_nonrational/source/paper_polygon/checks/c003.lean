module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 384 through 511. -/
theorem checked_384_400 : Interval targetCheck 384 400 :=
  interval_of_check targetCheck 384 16 (by decide +kernel)

theorem checked_400_416 : Interval targetCheck 400 416 :=
  interval_of_check targetCheck 400 16 (by decide +kernel)

theorem checked_416_432 : Interval targetCheck 416 432 :=
  interval_of_check targetCheck 416 16 (by decide +kernel)

theorem checked_432_448 : Interval targetCheck 432 448 :=
  interval_of_check targetCheck 432 16 (by decide +kernel)

theorem checked_448_464 : Interval targetCheck 448 464 :=
  interval_of_check targetCheck 448 16 (by decide +kernel)

theorem checked_464_480 : Interval targetCheck 464 480 :=
  interval_of_check targetCheck 464 16 (by decide +kernel)

theorem checked_480_496 : Interval targetCheck 480 496 :=
  interval_of_check targetCheck 480 16 (by decide +kernel)

theorem checked_496_512 : Interval targetCheck 496 512 :=
  interval_of_check targetCheck 496 16 (by decide +kernel)

theorem chunk_003 : Interval targetCheck 384 512 :=
  (interval_append targetCheck 384 448 512 (interval_append targetCheck 384 416 448 (interval_append targetCheck 384 400 416 checked_384_400 checked_400_416) (interval_append targetCheck 416 432 448 checked_416_432 checked_432_448)) (interval_append targetCheck 448 480 512 (interval_append targetCheck 448 464 480 checked_448_464 checked_464_480) (interval_append targetCheck 480 496 512 checked_480_496 checked_496_512)))

end Nonrational.TerminalVerification.PaperPolygon
