module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 1664 through 1791. -/
theorem checked_1664_1680 : Interval targetCheck 1664 1680 :=
  interval_of_check targetCheck 1664 16 (by decide +kernel)

theorem checked_1680_1696 : Interval targetCheck 1680 1696 :=
  interval_of_check targetCheck 1680 16 (by decide +kernel)

theorem checked_1696_1712 : Interval targetCheck 1696 1712 :=
  interval_of_check targetCheck 1696 16 (by decide +kernel)

theorem checked_1712_1728 : Interval targetCheck 1712 1728 :=
  interval_of_check targetCheck 1712 16 (by decide +kernel)

theorem checked_1728_1744 : Interval targetCheck 1728 1744 :=
  interval_of_check targetCheck 1728 16 (by decide +kernel)

theorem checked_1744_1760 : Interval targetCheck 1744 1760 :=
  interval_of_check targetCheck 1744 16 (by decide +kernel)

theorem checked_1760_1776 : Interval targetCheck 1760 1776 :=
  interval_of_check targetCheck 1760 16 (by decide +kernel)

theorem checked_1776_1792 : Interval targetCheck 1776 1792 :=
  interval_of_check targetCheck 1776 16 (by decide +kernel)

theorem chunk_013 : Interval targetCheck 1664 1792 :=
  (interval_append targetCheck 1664 1728 1792 (interval_append targetCheck 1664 1696 1728 (interval_append targetCheck 1664 1680 1696 checked_1664_1680 checked_1680_1696) (interval_append targetCheck 1696 1712 1728 checked_1696_1712 checked_1712_1728)) (interval_append targetCheck 1728 1760 1792 (interval_append targetCheck 1728 1744 1760 checked_1728_1744 checked_1744_1760) (interval_append targetCheck 1760 1776 1792 checked_1760_1776 checked_1776_1792)))

end Nonrational.TerminalVerification.PaperPolygon
