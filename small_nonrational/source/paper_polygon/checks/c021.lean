module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 2688 through 2815. -/
theorem checked_2688_2704 : Interval targetCheck 2688 2704 :=
  interval_of_check targetCheck 2688 16 (by decide +kernel)

theorem checked_2704_2720 : Interval targetCheck 2704 2720 :=
  interval_of_check targetCheck 2704 16 (by decide +kernel)

theorem checked_2720_2736 : Interval targetCheck 2720 2736 :=
  interval_of_check targetCheck 2720 16 (by decide +kernel)

theorem checked_2736_2752 : Interval targetCheck 2736 2752 :=
  interval_of_check targetCheck 2736 16 (by decide +kernel)

theorem checked_2752_2768 : Interval targetCheck 2752 2768 :=
  interval_of_check targetCheck 2752 16 (by decide +kernel)

theorem checked_2768_2784 : Interval targetCheck 2768 2784 :=
  interval_of_check targetCheck 2768 16 (by decide +kernel)

theorem checked_2784_2800 : Interval targetCheck 2784 2800 :=
  interval_of_check targetCheck 2784 16 (by decide +kernel)

theorem checked_2800_2816 : Interval targetCheck 2800 2816 :=
  interval_of_check targetCheck 2800 16 (by decide +kernel)

theorem chunk_021 : Interval targetCheck 2688 2816 :=
  (interval_append targetCheck 2688 2752 2816 (interval_append targetCheck 2688 2720 2752 (interval_append targetCheck 2688 2704 2720 checked_2688_2704 checked_2704_2720) (interval_append targetCheck 2720 2736 2752 checked_2720_2736 checked_2736_2752)) (interval_append targetCheck 2752 2784 2816 (interval_append targetCheck 2752 2768 2784 checked_2752_2768 checked_2768_2784) (interval_append targetCheck 2784 2800 2816 checked_2784_2800 checked_2800_2816)))

end Nonrational.TerminalVerification.PaperPolygon
