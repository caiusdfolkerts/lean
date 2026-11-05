module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 1536 through 1663. -/
theorem checked_1536_1552 : Interval targetCheck 1536 1552 :=
  interval_of_check targetCheck 1536 16 (by decide +kernel)

theorem checked_1552_1568 : Interval targetCheck 1552 1568 :=
  interval_of_check targetCheck 1552 16 (by decide +kernel)

theorem checked_1568_1584 : Interval targetCheck 1568 1584 :=
  interval_of_check targetCheck 1568 16 (by decide +kernel)

theorem checked_1584_1600 : Interval targetCheck 1584 1600 :=
  interval_of_check targetCheck 1584 16 (by decide +kernel)

theorem checked_1600_1616 : Interval targetCheck 1600 1616 :=
  interval_of_check targetCheck 1600 16 (by decide +kernel)

theorem checked_1616_1632 : Interval targetCheck 1616 1632 :=
  interval_of_check targetCheck 1616 16 (by decide +kernel)

theorem checked_1632_1648 : Interval targetCheck 1632 1648 :=
  interval_of_check targetCheck 1632 16 (by decide +kernel)

theorem checked_1648_1664 : Interval targetCheck 1648 1664 :=
  interval_of_check targetCheck 1648 16 (by decide +kernel)

theorem chunk_012 : Interval targetCheck 1536 1664 :=
  (interval_append targetCheck 1536 1600 1664 (interval_append targetCheck 1536 1568 1600 (interval_append targetCheck 1536 1552 1568 checked_1536_1552 checked_1552_1568) (interval_append targetCheck 1568 1584 1600 checked_1568_1584 checked_1584_1600)) (interval_append targetCheck 1600 1632 1664 (interval_append targetCheck 1600 1616 1632 checked_1600_1616 checked_1616_1632) (interval_append targetCheck 1632 1648 1664 checked_1632_1648 checked_1648_1664)))

end Nonrational.TerminalVerification.PaperPolygon
