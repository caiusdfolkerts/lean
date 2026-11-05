module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 896 through 1023. -/
theorem checked_896_912 : Interval targetCheck 896 912 :=
  interval_of_check targetCheck 896 16 (by decide +kernel)

theorem checked_912_928 : Interval targetCheck 912 928 :=
  interval_of_check targetCheck 912 16 (by decide +kernel)

theorem checked_928_944 : Interval targetCheck 928 944 :=
  interval_of_check targetCheck 928 16 (by decide +kernel)

theorem checked_944_960 : Interval targetCheck 944 960 :=
  interval_of_check targetCheck 944 16 (by decide +kernel)

theorem checked_960_976 : Interval targetCheck 960 976 :=
  interval_of_check targetCheck 960 16 (by decide +kernel)

theorem checked_976_992 : Interval targetCheck 976 992 :=
  interval_of_check targetCheck 976 16 (by decide +kernel)

theorem checked_992_1008 : Interval targetCheck 992 1008 :=
  interval_of_check targetCheck 992 16 (by decide +kernel)

theorem checked_1008_1024 : Interval targetCheck 1008 1024 :=
  interval_of_check targetCheck 1008 16 (by decide +kernel)

theorem chunk_007 : Interval targetCheck 896 1024 :=
  (interval_append targetCheck 896 960 1024 (interval_append targetCheck 896 928 960 (interval_append targetCheck 896 912 928 checked_896_912 checked_912_928) (interval_append targetCheck 928 944 960 checked_928_944 checked_944_960)) (interval_append targetCheck 960 992 1024 (interval_append targetCheck 960 976 992 checked_960_976 checked_976_992) (interval_append targetCheck 992 1008 1024 checked_992_1008 checked_1008_1024)))

end Nonrational.TerminalVerification.PaperPolygon
