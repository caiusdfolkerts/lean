module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 2432 through 2559. -/
theorem checked_2432_2448 : Interval targetCheck 2432 2448 :=
  interval_of_check targetCheck 2432 16 (by decide +kernel)

theorem checked_2448_2464 : Interval targetCheck 2448 2464 :=
  interval_of_check targetCheck 2448 16 (by decide +kernel)

theorem checked_2464_2480 : Interval targetCheck 2464 2480 :=
  interval_of_check targetCheck 2464 16 (by decide +kernel)

theorem checked_2480_2496 : Interval targetCheck 2480 2496 :=
  interval_of_check targetCheck 2480 16 (by decide +kernel)

theorem checked_2496_2512 : Interval targetCheck 2496 2512 :=
  interval_of_check targetCheck 2496 16 (by decide +kernel)

theorem checked_2512_2528 : Interval targetCheck 2512 2528 :=
  interval_of_check targetCheck 2512 16 (by decide +kernel)

theorem checked_2528_2544 : Interval targetCheck 2528 2544 :=
  interval_of_check targetCheck 2528 16 (by decide +kernel)

theorem checked_2544_2560 : Interval targetCheck 2544 2560 :=
  interval_of_check targetCheck 2544 16 (by decide +kernel)

theorem chunk_019 : Interval targetCheck 2432 2560 :=
  (interval_append targetCheck 2432 2496 2560 (interval_append targetCheck 2432 2464 2496 (interval_append targetCheck 2432 2448 2464 checked_2432_2448 checked_2448_2464) (interval_append targetCheck 2464 2480 2496 checked_2464_2480 checked_2480_2496)) (interval_append targetCheck 2496 2528 2560 (interval_append targetCheck 2496 2512 2528 checked_2496_2512 checked_2512_2528) (interval_append targetCheck 2528 2544 2560 checked_2528_2544 checked_2544_2560)))

end Nonrational.TerminalVerification.PaperPolygon
