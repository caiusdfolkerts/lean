module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 3456 through 3583. -/
theorem checked_3456_3472 : Interval targetCheck 3456 3472 :=
  interval_of_check targetCheck 3456 16 (by decide +kernel)

theorem checked_3472_3488 : Interval targetCheck 3472 3488 :=
  interval_of_check targetCheck 3472 16 (by decide +kernel)

theorem checked_3488_3504 : Interval targetCheck 3488 3504 :=
  interval_of_check targetCheck 3488 16 (by decide +kernel)

theorem checked_3504_3520 : Interval targetCheck 3504 3520 :=
  interval_of_check targetCheck 3504 16 (by decide +kernel)

theorem checked_3520_3536 : Interval targetCheck 3520 3536 :=
  interval_of_check targetCheck 3520 16 (by decide +kernel)

theorem checked_3536_3552 : Interval targetCheck 3536 3552 :=
  interval_of_check targetCheck 3536 16 (by decide +kernel)

theorem checked_3552_3568 : Interval targetCheck 3552 3568 :=
  interval_of_check targetCheck 3552 16 (by decide +kernel)

theorem checked_3568_3584 : Interval targetCheck 3568 3584 :=
  interval_of_check targetCheck 3568 16 (by decide +kernel)

theorem chunk_027 : Interval targetCheck 3456 3584 :=
  (interval_append targetCheck 3456 3520 3584 (interval_append targetCheck 3456 3488 3520 (interval_append targetCheck 3456 3472 3488 checked_3456_3472 checked_3472_3488) (interval_append targetCheck 3488 3504 3520 checked_3488_3504 checked_3504_3520)) (interval_append targetCheck 3520 3552 3584 (interval_append targetCheck 3520 3536 3552 checked_3520_3536 checked_3536_3552) (interval_append targetCheck 3552 3568 3584 checked_3552_3568 checked_3568_3584)))

end Nonrational.TerminalVerification.PaperPolygon
