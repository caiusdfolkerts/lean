module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 0 through 127. -/
theorem checked_0_16 : Interval targetCheck 0 16 :=
  interval_of_check targetCheck 0 16 (by decide +kernel)

theorem checked_16_32 : Interval targetCheck 16 32 :=
  interval_of_check targetCheck 16 16 (by decide +kernel)

theorem checked_32_48 : Interval targetCheck 32 48 :=
  interval_of_check targetCheck 32 16 (by decide +kernel)

theorem checked_48_64 : Interval targetCheck 48 64 :=
  interval_of_check targetCheck 48 16 (by decide +kernel)

theorem checked_64_80 : Interval targetCheck 64 80 :=
  interval_of_check targetCheck 64 16 (by decide +kernel)

theorem checked_80_96 : Interval targetCheck 80 96 :=
  interval_of_check targetCheck 80 16 (by decide +kernel)

theorem checked_96_112 : Interval targetCheck 96 112 :=
  interval_of_check targetCheck 96 16 (by decide +kernel)

theorem checked_112_128 : Interval targetCheck 112 128 :=
  interval_of_check targetCheck 112 16 (by decide +kernel)

theorem chunk_000 : Interval targetCheck 0 128 :=
  (interval_append targetCheck 0 64 128 (interval_append targetCheck 0 32 64 (interval_append targetCheck 0 16 32 checked_0_16 checked_16_32) (interval_append targetCheck 32 48 64 checked_32_48 checked_48_64)) (interval_append targetCheck 64 96 128 (interval_append targetCheck 64 80 96 checked_64_80 checked_80_96) (interval_append targetCheck 96 112 128 checked_96_112 checked_112_128)))

end Nonrational.TerminalVerification.PaperPolygon
