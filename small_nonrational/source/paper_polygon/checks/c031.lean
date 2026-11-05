module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 3968 through 4095. -/
theorem checked_3968_3984 : Interval targetCheck 3968 3984 :=
  interval_of_check targetCheck 3968 16 (by decide +kernel)

theorem checked_3984_4000 : Interval targetCheck 3984 4000 :=
  interval_of_check targetCheck 3984 16 (by decide +kernel)

theorem checked_4000_4016 : Interval targetCheck 4000 4016 :=
  interval_of_check targetCheck 4000 16 (by decide +kernel)

theorem checked_4016_4032 : Interval targetCheck 4016 4032 :=
  interval_of_check targetCheck 4016 16 (by decide +kernel)

theorem checked_4032_4048 : Interval targetCheck 4032 4048 :=
  interval_of_check targetCheck 4032 16 (by decide +kernel)

theorem checked_4048_4064 : Interval targetCheck 4048 4064 :=
  interval_of_check targetCheck 4048 16 (by decide +kernel)

theorem checked_4064_4080 : Interval targetCheck 4064 4080 :=
  interval_of_check targetCheck 4064 16 (by decide +kernel)

theorem checked_4080_4096 : Interval targetCheck 4080 4096 :=
  interval_of_check targetCheck 4080 16 (by decide +kernel)

theorem chunk_031 : Interval targetCheck 3968 4096 :=
  (interval_append targetCheck 3968 4032 4096 (interval_append targetCheck 3968 4000 4032 (interval_append targetCheck 3968 3984 4000 checked_3968_3984 checked_3984_4000) (interval_append targetCheck 4000 4016 4032 checked_4000_4016 checked_4016_4032)) (interval_append targetCheck 4032 4064 4096 (interval_append targetCheck 4032 4048 4064 checked_4032_4048 checked_4048_4064) (interval_append targetCheck 4064 4080 4096 checked_4064_4080 checked_4080_4096)))

end Nonrational.TerminalVerification.PaperPolygon
