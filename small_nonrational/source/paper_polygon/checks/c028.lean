module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 3584 through 3711. -/
theorem checked_3584_3600 : Interval targetCheck 3584 3600 :=
  interval_of_check targetCheck 3584 16 (by decide +kernel)

theorem checked_3600_3616 : Interval targetCheck 3600 3616 :=
  interval_of_check targetCheck 3600 16 (by decide +kernel)

theorem checked_3616_3632 : Interval targetCheck 3616 3632 :=
  interval_of_check targetCheck 3616 16 (by decide +kernel)

theorem checked_3632_3648 : Interval targetCheck 3632 3648 :=
  interval_of_check targetCheck 3632 16 (by decide +kernel)

theorem checked_3648_3664 : Interval targetCheck 3648 3664 :=
  interval_of_check targetCheck 3648 16 (by decide +kernel)

theorem checked_3664_3680 : Interval targetCheck 3664 3680 :=
  interval_of_check targetCheck 3664 16 (by decide +kernel)

theorem checked_3680_3696 : Interval targetCheck 3680 3696 :=
  interval_of_check targetCheck 3680 16 (by decide +kernel)

theorem checked_3696_3712 : Interval targetCheck 3696 3712 :=
  interval_of_check targetCheck 3696 16 (by decide +kernel)

theorem chunk_028 : Interval targetCheck 3584 3712 :=
  (interval_append targetCheck 3584 3648 3712 (interval_append targetCheck 3584 3616 3648 (interval_append targetCheck 3584 3600 3616 checked_3584_3600 checked_3600_3616) (interval_append targetCheck 3616 3632 3648 checked_3616_3632 checked_3632_3648)) (interval_append targetCheck 3648 3680 3712 (interval_append targetCheck 3648 3664 3680 checked_3648_3664 checked_3664_3680) (interval_append targetCheck 3680 3696 3712 checked_3680_3696 checked_3696_3712)))

end Nonrational.TerminalVerification.PaperPolygon
