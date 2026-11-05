module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 1920 through 2047. -/
theorem checked_1920_1936 : Interval targetCheck 1920 1936 :=
  interval_of_check targetCheck 1920 16 (by decide +kernel)

theorem checked_1936_1952 : Interval targetCheck 1936 1952 :=
  interval_of_check targetCheck 1936 16 (by decide +kernel)

theorem checked_1952_1968 : Interval targetCheck 1952 1968 :=
  interval_of_check targetCheck 1952 16 (by decide +kernel)

theorem checked_1968_1984 : Interval targetCheck 1968 1984 :=
  interval_of_check targetCheck 1968 16 (by decide +kernel)

theorem checked_1984_2000 : Interval targetCheck 1984 2000 :=
  interval_of_check targetCheck 1984 16 (by decide +kernel)

theorem checked_2000_2016 : Interval targetCheck 2000 2016 :=
  interval_of_check targetCheck 2000 16 (by decide +kernel)

theorem checked_2016_2032 : Interval targetCheck 2016 2032 :=
  interval_of_check targetCheck 2016 16 (by decide +kernel)

theorem checked_2032_2048 : Interval targetCheck 2032 2048 :=
  interval_of_check targetCheck 2032 16 (by decide +kernel)

theorem chunk_015 : Interval targetCheck 1920 2048 :=
  (interval_append targetCheck 1920 1984 2048 (interval_append targetCheck 1920 1952 1984 (interval_append targetCheck 1920 1936 1952 checked_1920_1936 checked_1936_1952) (interval_append targetCheck 1952 1968 1984 checked_1952_1968 checked_1968_1984)) (interval_append targetCheck 1984 2016 2048 (interval_append targetCheck 1984 2000 2016 checked_1984_2000 checked_2000_2016) (interval_append targetCheck 2016 2032 2048 checked_2016_2032 checked_2032_2048)))

end Nonrational.TerminalVerification.PaperPolygon
