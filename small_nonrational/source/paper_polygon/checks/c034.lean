module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 4352 through 4479. -/
theorem checked_4352_4368 : Interval targetCheck 4352 4368 :=
  interval_of_check targetCheck 4352 16 (by decide +kernel)

theorem checked_4368_4384 : Interval targetCheck 4368 4384 :=
  interval_of_check targetCheck 4368 16 (by decide +kernel)

theorem checked_4384_4400 : Interval targetCheck 4384 4400 :=
  interval_of_check targetCheck 4384 16 (by decide +kernel)

theorem checked_4400_4416 : Interval targetCheck 4400 4416 :=
  interval_of_check targetCheck 4400 16 (by decide +kernel)

theorem checked_4416_4432 : Interval targetCheck 4416 4432 :=
  interval_of_check targetCheck 4416 16 (by decide +kernel)

theorem checked_4432_4448 : Interval targetCheck 4432 4448 :=
  interval_of_check targetCheck 4432 16 (by decide +kernel)

theorem checked_4448_4464 : Interval targetCheck 4448 4464 :=
  interval_of_check targetCheck 4448 16 (by decide +kernel)

theorem checked_4464_4480 : Interval targetCheck 4464 4480 :=
  interval_of_check targetCheck 4464 16 (by decide +kernel)

theorem chunk_034 : Interval targetCheck 4352 4480 :=
  (interval_append targetCheck 4352 4416 4480 (interval_append targetCheck 4352 4384 4416 (interval_append targetCheck 4352 4368 4384 checked_4352_4368 checked_4368_4384) (interval_append targetCheck 4384 4400 4416 checked_4384_4400 checked_4400_4416)) (interval_append targetCheck 4416 4448 4480 (interval_append targetCheck 4416 4432 4448 checked_4416_4432 checked_4432_4448) (interval_append targetCheck 4448 4464 4480 checked_4448_4464 checked_4464_4480)))

end Nonrational.TerminalVerification.PaperPolygon
