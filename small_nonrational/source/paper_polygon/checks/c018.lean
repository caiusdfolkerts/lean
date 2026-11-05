module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 2304 through 2431. -/
theorem checked_2304_2320 : Interval targetCheck 2304 2320 :=
  interval_of_check targetCheck 2304 16 (by decide +kernel)

theorem checked_2320_2336 : Interval targetCheck 2320 2336 :=
  interval_of_check targetCheck 2320 16 (by decide +kernel)

theorem checked_2336_2352 : Interval targetCheck 2336 2352 :=
  interval_of_check targetCheck 2336 16 (by decide +kernel)

theorem checked_2352_2368 : Interval targetCheck 2352 2368 :=
  interval_of_check targetCheck 2352 16 (by decide +kernel)

theorem checked_2368_2384 : Interval targetCheck 2368 2384 :=
  interval_of_check targetCheck 2368 16 (by decide +kernel)

theorem checked_2384_2400 : Interval targetCheck 2384 2400 :=
  interval_of_check targetCheck 2384 16 (by decide +kernel)

theorem checked_2400_2416 : Interval targetCheck 2400 2416 :=
  interval_of_check targetCheck 2400 16 (by decide +kernel)

theorem checked_2416_2432 : Interval targetCheck 2416 2432 :=
  interval_of_check targetCheck 2416 16 (by decide +kernel)

theorem chunk_018 : Interval targetCheck 2304 2432 :=
  (interval_append targetCheck 2304 2368 2432 (interval_append targetCheck 2304 2336 2368 (interval_append targetCheck 2304 2320 2336 checked_2304_2320 checked_2320_2336) (interval_append targetCheck 2336 2352 2368 checked_2336_2352 checked_2352_2368)) (interval_append targetCheck 2368 2400 2432 (interval_append targetCheck 2368 2384 2400 checked_2368_2384 checked_2384_2400) (interval_append targetCheck 2400 2416 2432 checked_2400_2416 checked_2416_2432)))

end Nonrational.TerminalVerification.PaperPolygon
