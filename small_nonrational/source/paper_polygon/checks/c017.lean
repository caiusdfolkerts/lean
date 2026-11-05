module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 2176 through 2303. -/
theorem checked_2176_2192 : Interval targetCheck 2176 2192 :=
  interval_of_check targetCheck 2176 16 (by decide +kernel)

theorem checked_2192_2208 : Interval targetCheck 2192 2208 :=
  interval_of_check targetCheck 2192 16 (by decide +kernel)

theorem checked_2208_2224 : Interval targetCheck 2208 2224 :=
  interval_of_check targetCheck 2208 16 (by decide +kernel)

theorem checked_2224_2240 : Interval targetCheck 2224 2240 :=
  interval_of_check targetCheck 2224 16 (by decide +kernel)

theorem checked_2240_2256 : Interval targetCheck 2240 2256 :=
  interval_of_check targetCheck 2240 16 (by decide +kernel)

theorem checked_2256_2272 : Interval targetCheck 2256 2272 :=
  interval_of_check targetCheck 2256 16 (by decide +kernel)

theorem checked_2272_2288 : Interval targetCheck 2272 2288 :=
  interval_of_check targetCheck 2272 16 (by decide +kernel)

theorem checked_2288_2304 : Interval targetCheck 2288 2304 :=
  interval_of_check targetCheck 2288 16 (by decide +kernel)

theorem chunk_017 : Interval targetCheck 2176 2304 :=
  (interval_append targetCheck 2176 2240 2304 (interval_append targetCheck 2176 2208 2240 (interval_append targetCheck 2176 2192 2208 checked_2176_2192 checked_2192_2208) (interval_append targetCheck 2208 2224 2240 checked_2208_2224 checked_2224_2240)) (interval_append targetCheck 2240 2272 2304 (interval_append targetCheck 2240 2256 2272 checked_2240_2256 checked_2256_2272) (interval_append targetCheck 2272 2288 2304 checked_2272_2288 checked_2288_2304)))

end Nonrational.TerminalVerification.PaperPolygon
