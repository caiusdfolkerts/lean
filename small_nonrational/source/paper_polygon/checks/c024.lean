module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 3072 through 3199. -/
theorem checked_3072_3088 : Interval targetCheck 3072 3088 :=
  interval_of_check targetCheck 3072 16 (by decide +kernel)

theorem checked_3088_3104 : Interval targetCheck 3088 3104 :=
  interval_of_check targetCheck 3088 16 (by decide +kernel)

theorem checked_3104_3120 : Interval targetCheck 3104 3120 :=
  interval_of_check targetCheck 3104 16 (by decide +kernel)

theorem checked_3120_3136 : Interval targetCheck 3120 3136 :=
  interval_of_check targetCheck 3120 16 (by decide +kernel)

theorem checked_3136_3152 : Interval targetCheck 3136 3152 :=
  interval_of_check targetCheck 3136 16 (by decide +kernel)

theorem checked_3152_3168 : Interval targetCheck 3152 3168 :=
  interval_of_check targetCheck 3152 16 (by decide +kernel)

theorem checked_3168_3184 : Interval targetCheck 3168 3184 :=
  interval_of_check targetCheck 3168 16 (by decide +kernel)

theorem checked_3184_3200 : Interval targetCheck 3184 3200 :=
  interval_of_check targetCheck 3184 16 (by decide +kernel)

theorem chunk_024 : Interval targetCheck 3072 3200 :=
  (interval_append targetCheck 3072 3136 3200 (interval_append targetCheck 3072 3104 3136 (interval_append targetCheck 3072 3088 3104 checked_3072_3088 checked_3088_3104) (interval_append targetCheck 3104 3120 3136 checked_3104_3120 checked_3120_3136)) (interval_append targetCheck 3136 3168 3200 (interval_append targetCheck 3136 3152 3168 checked_3136_3152 checked_3152_3168) (interval_append targetCheck 3168 3184 3200 checked_3168_3184 checked_3184_3200)))

end Nonrational.TerminalVerification.PaperPolygon
