module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 128 through 255. -/
theorem checked_128_144 : Interval targetCheck 128 144 :=
  interval_of_check targetCheck 128 16 (by decide +kernel)

theorem checked_144_160 : Interval targetCheck 144 160 :=
  interval_of_check targetCheck 144 16 (by decide +kernel)

theorem checked_160_176 : Interval targetCheck 160 176 :=
  interval_of_check targetCheck 160 16 (by decide +kernel)

theorem checked_176_192 : Interval targetCheck 176 192 :=
  interval_of_check targetCheck 176 16 (by decide +kernel)

theorem checked_192_208 : Interval targetCheck 192 208 :=
  interval_of_check targetCheck 192 16 (by decide +kernel)

theorem checked_208_224 : Interval targetCheck 208 224 :=
  interval_of_check targetCheck 208 16 (by decide +kernel)

theorem checked_224_240 : Interval targetCheck 224 240 :=
  interval_of_check targetCheck 224 16 (by decide +kernel)

theorem checked_240_256 : Interval targetCheck 240 256 :=
  interval_of_check targetCheck 240 16 (by decide +kernel)

theorem chunk_001 : Interval targetCheck 128 256 :=
  (interval_append targetCheck 128 192 256 (interval_append targetCheck 128 160 192 (interval_append targetCheck 128 144 160 checked_128_144 checked_144_160) (interval_append targetCheck 160 176 192 checked_160_176 checked_176_192)) (interval_append targetCheck 192 224 256 (interval_append targetCheck 192 208 224 checked_192_208 checked_208_224) (interval_append targetCheck 224 240 256 checked_224_240 checked_240_256)))

end Nonrational.TerminalVerification.PaperPolygon
