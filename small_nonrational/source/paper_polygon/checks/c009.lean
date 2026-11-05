module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 1152 through 1279. -/
theorem checked_1152_1168 : Interval targetCheck 1152 1168 :=
  interval_of_check targetCheck 1152 16 (by decide +kernel)

theorem checked_1168_1184 : Interval targetCheck 1168 1184 :=
  interval_of_check targetCheck 1168 16 (by decide +kernel)

theorem checked_1184_1200 : Interval targetCheck 1184 1200 :=
  interval_of_check targetCheck 1184 16 (by decide +kernel)

theorem checked_1200_1216 : Interval targetCheck 1200 1216 :=
  interval_of_check targetCheck 1200 16 (by decide +kernel)

theorem checked_1216_1232 : Interval targetCheck 1216 1232 :=
  interval_of_check targetCheck 1216 16 (by decide +kernel)

theorem checked_1232_1248 : Interval targetCheck 1232 1248 :=
  interval_of_check targetCheck 1232 16 (by decide +kernel)

theorem checked_1248_1264 : Interval targetCheck 1248 1264 :=
  interval_of_check targetCheck 1248 16 (by decide +kernel)

theorem checked_1264_1280 : Interval targetCheck 1264 1280 :=
  interval_of_check targetCheck 1264 16 (by decide +kernel)

theorem chunk_009 : Interval targetCheck 1152 1280 :=
  (interval_append targetCheck 1152 1216 1280 (interval_append targetCheck 1152 1184 1216 (interval_append targetCheck 1152 1168 1184 checked_1152_1168 checked_1168_1184) (interval_append targetCheck 1184 1200 1216 checked_1184_1200 checked_1200_1216)) (interval_append targetCheck 1216 1248 1280 (interval_append targetCheck 1216 1232 1248 checked_1216_1232 checked_1232_1248) (interval_append targetCheck 1248 1264 1280 checked_1248_1264 checked_1264_1280)))

end Nonrational.TerminalVerification.PaperPolygon
