module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 256 through 383. -/
theorem checked_256_272 : Interval targetCheck 256 272 :=
  interval_of_check targetCheck 256 16 (by decide +kernel)

theorem checked_272_288 : Interval targetCheck 272 288 :=
  interval_of_check targetCheck 272 16 (by decide +kernel)

theorem checked_288_304 : Interval targetCheck 288 304 :=
  interval_of_check targetCheck 288 16 (by decide +kernel)

theorem checked_304_320 : Interval targetCheck 304 320 :=
  interval_of_check targetCheck 304 16 (by decide +kernel)

theorem checked_320_336 : Interval targetCheck 320 336 :=
  interval_of_check targetCheck 320 16 (by decide +kernel)

theorem checked_336_352 : Interval targetCheck 336 352 :=
  interval_of_check targetCheck 336 16 (by decide +kernel)

theorem checked_352_368 : Interval targetCheck 352 368 :=
  interval_of_check targetCheck 352 16 (by decide +kernel)

theorem checked_368_384 : Interval targetCheck 368 384 :=
  interval_of_check targetCheck 368 16 (by decide +kernel)

theorem chunk_002 : Interval targetCheck 256 384 :=
  (interval_append targetCheck 256 320 384 (interval_append targetCheck 256 288 320 (interval_append targetCheck 256 272 288 checked_256_272 checked_272_288) (interval_append targetCheck 288 304 320 checked_288_304 checked_304_320)) (interval_append targetCheck 320 352 384 (interval_append targetCheck 320 336 352 checked_320_336 checked_336_352) (interval_append targetCheck 352 368 384 checked_352_368 checked_368_384)))

end Nonrational.TerminalVerification.PaperPolygon
