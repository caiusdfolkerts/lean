module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 4608 through 4725. -/
theorem checked_4608_4624 : Interval targetCheck 4608 4624 :=
  interval_of_check targetCheck 4608 16 (by decide +kernel)

theorem checked_4624_4640 : Interval targetCheck 4624 4640 :=
  interval_of_check targetCheck 4624 16 (by decide +kernel)

theorem checked_4640_4656 : Interval targetCheck 4640 4656 :=
  interval_of_check targetCheck 4640 16 (by decide +kernel)

theorem checked_4656_4672 : Interval targetCheck 4656 4672 :=
  interval_of_check targetCheck 4656 16 (by decide +kernel)

theorem checked_4672_4688 : Interval targetCheck 4672 4688 :=
  interval_of_check targetCheck 4672 16 (by decide +kernel)

theorem checked_4688_4704 : Interval targetCheck 4688 4704 :=
  interval_of_check targetCheck 4688 16 (by decide +kernel)

theorem checked_4704_4720 : Interval targetCheck 4704 4720 :=
  interval_of_check targetCheck 4704 16 (by decide +kernel)

theorem checked_4720_4726 : Interval targetCheck 4720 4726 :=
  interval_of_check targetCheck 4720 6 (by decide +kernel)

theorem chunk_036 : Interval targetCheck 4608 4726 :=
  (interval_append targetCheck 4608 4672 4726 (interval_append targetCheck 4608 4640 4672 (interval_append targetCheck 4608 4624 4640 checked_4608_4624 checked_4624_4640) (interval_append targetCheck 4640 4656 4672 checked_4640_4656 checked_4656_4672)) (interval_append targetCheck 4672 4704 4726 (interval_append targetCheck 4672 4688 4704 checked_4672_4688 checked_4688_4704) (interval_append targetCheck 4704 4720 4726 checked_4704_4720 checked_4720_4726)))

end Nonrational.TerminalVerification.PaperPolygon
