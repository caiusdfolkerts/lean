module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 640 through 767. -/
theorem checked_640_656 : Interval targetCheck 640 656 :=
  interval_of_check targetCheck 640 16 (by decide +kernel)

theorem checked_656_672 : Interval targetCheck 656 672 :=
  interval_of_check targetCheck 656 16 (by decide +kernel)

theorem checked_672_688 : Interval targetCheck 672 688 :=
  interval_of_check targetCheck 672 16 (by decide +kernel)

theorem checked_688_704 : Interval targetCheck 688 704 :=
  interval_of_check targetCheck 688 16 (by decide +kernel)

theorem checked_704_720 : Interval targetCheck 704 720 :=
  interval_of_check targetCheck 704 16 (by decide +kernel)

theorem checked_720_736 : Interval targetCheck 720 736 :=
  interval_of_check targetCheck 720 16 (by decide +kernel)

theorem checked_736_752 : Interval targetCheck 736 752 :=
  interval_of_check targetCheck 736 16 (by decide +kernel)

theorem checked_752_768 : Interval targetCheck 752 768 :=
  interval_of_check targetCheck 752 16 (by decide +kernel)

theorem chunk_005 : Interval targetCheck 640 768 :=
  (interval_append targetCheck 640 704 768 (interval_append targetCheck 640 672 704 (interval_append targetCheck 640 656 672 checked_640_656 checked_656_672) (interval_append targetCheck 672 688 704 checked_672_688 checked_688_704)) (interval_append targetCheck 704 736 768 (interval_append targetCheck 704 720 736 checked_704_720 checked_720_736) (interval_append targetCheck 736 752 768 checked_736_752 checked_752_768)))

end Nonrational.TerminalVerification.PaperPolygon
