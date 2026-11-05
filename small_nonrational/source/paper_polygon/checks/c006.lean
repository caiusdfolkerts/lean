module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 768 through 895. -/
theorem checked_768_784 : Interval targetCheck 768 784 :=
  interval_of_check targetCheck 768 16 (by decide +kernel)

theorem checked_784_800 : Interval targetCheck 784 800 :=
  interval_of_check targetCheck 784 16 (by decide +kernel)

theorem checked_800_816 : Interval targetCheck 800 816 :=
  interval_of_check targetCheck 800 16 (by decide +kernel)

theorem checked_816_832 : Interval targetCheck 816 832 :=
  interval_of_check targetCheck 816 16 (by decide +kernel)

theorem checked_832_848 : Interval targetCheck 832 848 :=
  interval_of_check targetCheck 832 16 (by decide +kernel)

theorem checked_848_864 : Interval targetCheck 848 864 :=
  interval_of_check targetCheck 848 16 (by decide +kernel)

theorem checked_864_880 : Interval targetCheck 864 880 :=
  interval_of_check targetCheck 864 16 (by decide +kernel)

theorem checked_880_896 : Interval targetCheck 880 896 :=
  interval_of_check targetCheck 880 16 (by decide +kernel)

theorem chunk_006 : Interval targetCheck 768 896 :=
  (interval_append targetCheck 768 832 896 (interval_append targetCheck 768 800 832 (interval_append targetCheck 768 784 800 checked_768_784 checked_784_800) (interval_append targetCheck 800 816 832 checked_800_816 checked_816_832)) (interval_append targetCheck 832 864 896 (interval_append targetCheck 832 848 864 checked_832_848 checked_848_864) (interval_append targetCheck 864 880 896 checked_864_880 checked_880_896)))

end Nonrational.TerminalVerification.PaperPolygon
