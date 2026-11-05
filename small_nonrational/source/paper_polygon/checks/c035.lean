module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 4480 through 4607. -/
theorem checked_4480_4496 : Interval targetCheck 4480 4496 :=
  interval_of_check targetCheck 4480 16 (by decide +kernel)

theorem checked_4496_4512 : Interval targetCheck 4496 4512 :=
  interval_of_check targetCheck 4496 16 (by decide +kernel)

theorem checked_4512_4528 : Interval targetCheck 4512 4528 :=
  interval_of_check targetCheck 4512 16 (by decide +kernel)

theorem checked_4528_4544 : Interval targetCheck 4528 4544 :=
  interval_of_check targetCheck 4528 16 (by decide +kernel)

theorem checked_4544_4560 : Interval targetCheck 4544 4560 :=
  interval_of_check targetCheck 4544 16 (by decide +kernel)

theorem checked_4560_4576 : Interval targetCheck 4560 4576 :=
  interval_of_check targetCheck 4560 16 (by decide +kernel)

theorem checked_4576_4592 : Interval targetCheck 4576 4592 :=
  interval_of_check targetCheck 4576 16 (by decide +kernel)

theorem checked_4592_4608 : Interval targetCheck 4592 4608 :=
  interval_of_check targetCheck 4592 16 (by decide +kernel)

theorem chunk_035 : Interval targetCheck 4480 4608 :=
  (interval_append targetCheck 4480 4544 4608 (interval_append targetCheck 4480 4512 4544 (interval_append targetCheck 4480 4496 4512 checked_4480_4496 checked_4496_4512) (interval_append targetCheck 4512 4528 4544 checked_4512_4528 checked_4528_4544)) (interval_append targetCheck 4544 4576 4608 (interval_append targetCheck 4544 4560 4576 checked_4544_4560 checked_4560_4576) (interval_append targetCheck 4576 4592 4608 checked_4576_4592 checked_4592_4608)))

end Nonrational.TerminalVerification.PaperPolygon
