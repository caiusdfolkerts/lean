module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 4096 through 4223. -/
theorem checked_4096_4112 : Interval targetCheck 4096 4112 :=
  interval_of_check targetCheck 4096 16 (by decide +kernel)

theorem checked_4112_4128 : Interval targetCheck 4112 4128 :=
  interval_of_check targetCheck 4112 16 (by decide +kernel)

theorem checked_4128_4144 : Interval targetCheck 4128 4144 :=
  interval_of_check targetCheck 4128 16 (by decide +kernel)

theorem checked_4144_4160 : Interval targetCheck 4144 4160 :=
  interval_of_check targetCheck 4144 16 (by decide +kernel)

theorem checked_4160_4176 : Interval targetCheck 4160 4176 :=
  interval_of_check targetCheck 4160 16 (by decide +kernel)

theorem checked_4176_4192 : Interval targetCheck 4176 4192 :=
  interval_of_check targetCheck 4176 16 (by decide +kernel)

theorem checked_4192_4208 : Interval targetCheck 4192 4208 :=
  interval_of_check targetCheck 4192 16 (by decide +kernel)

theorem checked_4208_4224 : Interval targetCheck 4208 4224 :=
  interval_of_check targetCheck 4208 16 (by decide +kernel)

theorem chunk_032 : Interval targetCheck 4096 4224 :=
  (interval_append targetCheck 4096 4160 4224 (interval_append targetCheck 4096 4128 4160 (interval_append targetCheck 4096 4112 4128 checked_4096_4112 checked_4112_4128) (interval_append targetCheck 4128 4144 4160 checked_4128_4144 checked_4144_4160)) (interval_append targetCheck 4160 4192 4224 (interval_append targetCheck 4160 4176 4192 checked_4160_4176 checked_4176_4192) (interval_append targetCheck 4192 4208 4224 checked_4192_4208 checked_4208_4224)))

end Nonrational.TerminalVerification.PaperPolygon
