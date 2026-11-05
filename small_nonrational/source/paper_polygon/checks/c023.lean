module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 2944 through 3071. -/
theorem checked_2944_2960 : Interval targetCheck 2944 2960 :=
  interval_of_check targetCheck 2944 16 (by decide +kernel)

theorem checked_2960_2976 : Interval targetCheck 2960 2976 :=
  interval_of_check targetCheck 2960 16 (by decide +kernel)

theorem checked_2976_2992 : Interval targetCheck 2976 2992 :=
  interval_of_check targetCheck 2976 16 (by decide +kernel)

theorem checked_2992_3008 : Interval targetCheck 2992 3008 :=
  interval_of_check targetCheck 2992 16 (by decide +kernel)

theorem checked_3008_3024 : Interval targetCheck 3008 3024 :=
  interval_of_check targetCheck 3008 16 (by decide +kernel)

theorem checked_3024_3040 : Interval targetCheck 3024 3040 :=
  interval_of_check targetCheck 3024 16 (by decide +kernel)

theorem checked_3040_3056 : Interval targetCheck 3040 3056 :=
  interval_of_check targetCheck 3040 16 (by decide +kernel)

theorem checked_3056_3072 : Interval targetCheck 3056 3072 :=
  interval_of_check targetCheck 3056 16 (by decide +kernel)

theorem chunk_023 : Interval targetCheck 2944 3072 :=
  (interval_append targetCheck 2944 3008 3072 (interval_append targetCheck 2944 2976 3008 (interval_append targetCheck 2944 2960 2976 checked_2944_2960 checked_2960_2976) (interval_append targetCheck 2976 2992 3008 checked_2976_2992 checked_2992_3008)) (interval_append targetCheck 3008 3040 3072 (interval_append targetCheck 3008 3024 3040 checked_3008_3024 checked_3024_3040) (interval_append targetCheck 3040 3056 3072 checked_3040_3056 checked_3056_3072)))

end Nonrational.TerminalVerification.PaperPolygon
