module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 1792 through 1919. -/
theorem checked_1792_1808 : Interval targetCheck 1792 1808 :=
  interval_of_check targetCheck 1792 16 (by decide +kernel)

theorem checked_1808_1824 : Interval targetCheck 1808 1824 :=
  interval_of_check targetCheck 1808 16 (by decide +kernel)

theorem checked_1824_1840 : Interval targetCheck 1824 1840 :=
  interval_of_check targetCheck 1824 16 (by decide +kernel)

theorem checked_1840_1856 : Interval targetCheck 1840 1856 :=
  interval_of_check targetCheck 1840 16 (by decide +kernel)

theorem checked_1856_1872 : Interval targetCheck 1856 1872 :=
  interval_of_check targetCheck 1856 16 (by decide +kernel)

theorem checked_1872_1888 : Interval targetCheck 1872 1888 :=
  interval_of_check targetCheck 1872 16 (by decide +kernel)

theorem checked_1888_1904 : Interval targetCheck 1888 1904 :=
  interval_of_check targetCheck 1888 16 (by decide +kernel)

theorem checked_1904_1920 : Interval targetCheck 1904 1920 :=
  interval_of_check targetCheck 1904 16 (by decide +kernel)

theorem chunk_014 : Interval targetCheck 1792 1920 :=
  (interval_append targetCheck 1792 1856 1920 (interval_append targetCheck 1792 1824 1856 (interval_append targetCheck 1792 1808 1824 checked_1792_1808 checked_1808_1824) (interval_append targetCheck 1824 1840 1856 checked_1824_1840 checked_1840_1856)) (interval_append targetCheck 1856 1888 1920 (interval_append targetCheck 1856 1872 1888 checked_1856_1872 checked_1872_1888) (interval_append targetCheck 1888 1904 1920 checked_1888_1904 checked_1904_1920)))

end Nonrational.TerminalVerification.PaperPolygon
