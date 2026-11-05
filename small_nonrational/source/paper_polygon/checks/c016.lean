module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 2048 through 2175. -/
theorem checked_2048_2064 : Interval targetCheck 2048 2064 :=
  interval_of_check targetCheck 2048 16 (by decide +kernel)

theorem checked_2064_2080 : Interval targetCheck 2064 2080 :=
  interval_of_check targetCheck 2064 16 (by decide +kernel)

theorem checked_2080_2096 : Interval targetCheck 2080 2096 :=
  interval_of_check targetCheck 2080 16 (by decide +kernel)

theorem checked_2096_2112 : Interval targetCheck 2096 2112 :=
  interval_of_check targetCheck 2096 16 (by decide +kernel)

theorem checked_2112_2128 : Interval targetCheck 2112 2128 :=
  interval_of_check targetCheck 2112 16 (by decide +kernel)

theorem checked_2128_2144 : Interval targetCheck 2128 2144 :=
  interval_of_check targetCheck 2128 16 (by decide +kernel)

theorem checked_2144_2160 : Interval targetCheck 2144 2160 :=
  interval_of_check targetCheck 2144 16 (by decide +kernel)

theorem checked_2160_2176 : Interval targetCheck 2160 2176 :=
  interval_of_check targetCheck 2160 16 (by decide +kernel)

theorem chunk_016 : Interval targetCheck 2048 2176 :=
  (interval_append targetCheck 2048 2112 2176 (interval_append targetCheck 2048 2080 2112 (interval_append targetCheck 2048 2064 2080 checked_2048_2064 checked_2064_2080) (interval_append targetCheck 2080 2096 2112 checked_2080_2096 checked_2096_2112)) (interval_append targetCheck 2112 2144 2176 (interval_append targetCheck 2112 2128 2144 checked_2112_2128 checked_2128_2144) (interval_append targetCheck 2144 2160 2176 checked_2144_2160 checked_2160_2176)))

end Nonrational.TerminalVerification.PaperPolygon
