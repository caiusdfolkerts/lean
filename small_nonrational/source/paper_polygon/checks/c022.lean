module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 2816 through 2943. -/
theorem checked_2816_2832 : Interval targetCheck 2816 2832 :=
  interval_of_check targetCheck 2816 16 (by decide +kernel)

theorem checked_2832_2848 : Interval targetCheck 2832 2848 :=
  interval_of_check targetCheck 2832 16 (by decide +kernel)

theorem checked_2848_2864 : Interval targetCheck 2848 2864 :=
  interval_of_check targetCheck 2848 16 (by decide +kernel)

theorem checked_2864_2880 : Interval targetCheck 2864 2880 :=
  interval_of_check targetCheck 2864 16 (by decide +kernel)

theorem checked_2880_2896 : Interval targetCheck 2880 2896 :=
  interval_of_check targetCheck 2880 16 (by decide +kernel)

theorem checked_2896_2912 : Interval targetCheck 2896 2912 :=
  interval_of_check targetCheck 2896 16 (by decide +kernel)

theorem checked_2912_2928 : Interval targetCheck 2912 2928 :=
  interval_of_check targetCheck 2912 16 (by decide +kernel)

theorem checked_2928_2944 : Interval targetCheck 2928 2944 :=
  interval_of_check targetCheck 2928 16 (by decide +kernel)

theorem chunk_022 : Interval targetCheck 2816 2944 :=
  (interval_append targetCheck 2816 2880 2944 (interval_append targetCheck 2816 2848 2880 (interval_append targetCheck 2816 2832 2848 checked_2816_2832 checked_2832_2848) (interval_append targetCheck 2848 2864 2880 checked_2848_2864 checked_2864_2880)) (interval_append targetCheck 2880 2912 2944 (interval_append targetCheck 2880 2896 2912 checked_2880_2896 checked_2896_2912) (interval_append targetCheck 2912 2928 2944 checked_2912_2928 checked_2928_2944)))

end Nonrational.TerminalVerification.PaperPolygon
