module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 512 through 639. -/
theorem checked_512_528 : Interval targetCheck 512 528 :=
  interval_of_check targetCheck 512 16 (by decide +kernel)

theorem checked_528_544 : Interval targetCheck 528 544 :=
  interval_of_check targetCheck 528 16 (by decide +kernel)

theorem checked_544_560 : Interval targetCheck 544 560 :=
  interval_of_check targetCheck 544 16 (by decide +kernel)

theorem checked_560_576 : Interval targetCheck 560 576 :=
  interval_of_check targetCheck 560 16 (by decide +kernel)

theorem checked_576_592 : Interval targetCheck 576 592 :=
  interval_of_check targetCheck 576 16 (by decide +kernel)

theorem checked_592_608 : Interval targetCheck 592 608 :=
  interval_of_check targetCheck 592 16 (by decide +kernel)

theorem checked_608_624 : Interval targetCheck 608 624 :=
  interval_of_check targetCheck 608 16 (by decide +kernel)

theorem checked_624_640 : Interval targetCheck 624 640 :=
  interval_of_check targetCheck 624 16 (by decide +kernel)

theorem chunk_004 : Interval targetCheck 512 640 :=
  (interval_append targetCheck 512 576 640 (interval_append targetCheck 512 544 576 (interval_append targetCheck 512 528 544 checked_512_528 checked_528_544) (interval_append targetCheck 544 560 576 checked_544_560 checked_560_576)) (interval_append targetCheck 576 608 640 (interval_append targetCheck 576 592 608 checked_576_592 checked_592_608) (interval_append targetCheck 608 624 640 checked_608_624 checked_624_640)))

end Nonrational.TerminalVerification.PaperPolygon
