module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 4224 through 4351. -/
theorem checked_4224_4240 : Interval targetCheck 4224 4240 :=
  interval_of_check targetCheck 4224 16 (by decide +kernel)

theorem checked_4240_4256 : Interval targetCheck 4240 4256 :=
  interval_of_check targetCheck 4240 16 (by decide +kernel)

theorem checked_4256_4272 : Interval targetCheck 4256 4272 :=
  interval_of_check targetCheck 4256 16 (by decide +kernel)

theorem checked_4272_4288 : Interval targetCheck 4272 4288 :=
  interval_of_check targetCheck 4272 16 (by decide +kernel)

theorem checked_4288_4304 : Interval targetCheck 4288 4304 :=
  interval_of_check targetCheck 4288 16 (by decide +kernel)

theorem checked_4304_4320 : Interval targetCheck 4304 4320 :=
  interval_of_check targetCheck 4304 16 (by decide +kernel)

theorem checked_4320_4336 : Interval targetCheck 4320 4336 :=
  interval_of_check targetCheck 4320 16 (by decide +kernel)

theorem checked_4336_4352 : Interval targetCheck 4336 4352 :=
  interval_of_check targetCheck 4336 16 (by decide +kernel)

theorem chunk_033 : Interval targetCheck 4224 4352 :=
  (interval_append targetCheck 4224 4288 4352 (interval_append targetCheck 4224 4256 4288 (interval_append targetCheck 4224 4240 4256 checked_4224_4240 checked_4240_4256) (interval_append targetCheck 4256 4272 4288 checked_4256_4272 checked_4272_4288)) (interval_append targetCheck 4288 4320 4352 (interval_append targetCheck 4288 4304 4320 checked_4288_4304 checked_4304_4320) (interval_append targetCheck 4320 4336 4352 checked_4320_4336 checked_4336_4352)))

end Nonrational.TerminalVerification.PaperPolygon
