module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 3200 through 3327. -/
theorem checked_3200_3216 : Interval targetCheck 3200 3216 :=
  interval_of_check targetCheck 3200 16 (by decide +kernel)

theorem checked_3216_3232 : Interval targetCheck 3216 3232 :=
  interval_of_check targetCheck 3216 16 (by decide +kernel)

theorem checked_3232_3248 : Interval targetCheck 3232 3248 :=
  interval_of_check targetCheck 3232 16 (by decide +kernel)

theorem checked_3248_3264 : Interval targetCheck 3248 3264 :=
  interval_of_check targetCheck 3248 16 (by decide +kernel)

theorem checked_3264_3280 : Interval targetCheck 3264 3280 :=
  interval_of_check targetCheck 3264 16 (by decide +kernel)

theorem checked_3280_3296 : Interval targetCheck 3280 3296 :=
  interval_of_check targetCheck 3280 16 (by decide +kernel)

theorem checked_3296_3312 : Interval targetCheck 3296 3312 :=
  interval_of_check targetCheck 3296 16 (by decide +kernel)

theorem checked_3312_3328 : Interval targetCheck 3312 3328 :=
  interval_of_check targetCheck 3312 16 (by decide +kernel)

theorem chunk_025 : Interval targetCheck 3200 3328 :=
  (interval_append targetCheck 3200 3264 3328 (interval_append targetCheck 3200 3232 3264 (interval_append targetCheck 3200 3216 3232 checked_3200_3216 checked_3216_3232) (interval_append targetCheck 3232 3248 3264 checked_3232_3248 checked_3248_3264)) (interval_append targetCheck 3264 3296 3328 (interval_append targetCheck 3264 3280 3296 checked_3264_3280 checked_3280_3296) (interval_append targetCheck 3296 3312 3328 checked_3296_3312 checked_3312_3328)))

end Nonrational.TerminalVerification.PaperPolygon
