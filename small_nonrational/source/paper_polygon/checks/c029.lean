module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 3712 through 3839. -/
theorem checked_3712_3728 : Interval targetCheck 3712 3728 :=
  interval_of_check targetCheck 3712 16 (by decide +kernel)

theorem checked_3728_3744 : Interval targetCheck 3728 3744 :=
  interval_of_check targetCheck 3728 16 (by decide +kernel)

theorem checked_3744_3760 : Interval targetCheck 3744 3760 :=
  interval_of_check targetCheck 3744 16 (by decide +kernel)

theorem checked_3760_3776 : Interval targetCheck 3760 3776 :=
  interval_of_check targetCheck 3760 16 (by decide +kernel)

theorem checked_3776_3792 : Interval targetCheck 3776 3792 :=
  interval_of_check targetCheck 3776 16 (by decide +kernel)

theorem checked_3792_3808 : Interval targetCheck 3792 3808 :=
  interval_of_check targetCheck 3792 16 (by decide +kernel)

theorem checked_3808_3824 : Interval targetCheck 3808 3824 :=
  interval_of_check targetCheck 3808 16 (by decide +kernel)

theorem checked_3824_3840 : Interval targetCheck 3824 3840 :=
  interval_of_check targetCheck 3824 16 (by decide +kernel)

theorem chunk_029 : Interval targetCheck 3712 3840 :=
  (interval_append targetCheck 3712 3776 3840 (interval_append targetCheck 3712 3744 3776 (interval_append targetCheck 3712 3728 3744 checked_3712_3728 checked_3728_3744) (interval_append targetCheck 3744 3760 3776 checked_3744_3760 checked_3760_3776)) (interval_append targetCheck 3776 3808 3840 (interval_append targetCheck 3776 3792 3808 checked_3776_3792 checked_3792_3808) (interval_append targetCheck 3808 3824 3840 checked_3808_3824 checked_3824_3840)))

end Nonrational.TerminalVerification.PaperPolygon
