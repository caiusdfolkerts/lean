module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 2560 through 2687. -/
theorem checked_2560_2576 : Interval targetCheck 2560 2576 :=
  interval_of_check targetCheck 2560 16 (by decide +kernel)

theorem checked_2576_2592 : Interval targetCheck 2576 2592 :=
  interval_of_check targetCheck 2576 16 (by decide +kernel)

theorem checked_2592_2608 : Interval targetCheck 2592 2608 :=
  interval_of_check targetCheck 2592 16 (by decide +kernel)

theorem checked_2608_2624 : Interval targetCheck 2608 2624 :=
  interval_of_check targetCheck 2608 16 (by decide +kernel)

theorem checked_2624_2640 : Interval targetCheck 2624 2640 :=
  interval_of_check targetCheck 2624 16 (by decide +kernel)

theorem checked_2640_2656 : Interval targetCheck 2640 2656 :=
  interval_of_check targetCheck 2640 16 (by decide +kernel)

theorem checked_2656_2672 : Interval targetCheck 2656 2672 :=
  interval_of_check targetCheck 2656 16 (by decide +kernel)

theorem checked_2672_2688 : Interval targetCheck 2672 2688 :=
  interval_of_check targetCheck 2672 16 (by decide +kernel)

theorem chunk_020 : Interval targetCheck 2560 2688 :=
  (interval_append targetCheck 2560 2624 2688 (interval_append targetCheck 2560 2592 2624 (interval_append targetCheck 2560 2576 2592 checked_2560_2576 checked_2576_2592) (interval_append targetCheck 2592 2608 2624 checked_2592_2608 checked_2608_2624)) (interval_append targetCheck 2624 2656 2688 (interval_append targetCheck 2624 2640 2656 checked_2624_2640 checked_2640_2656) (interval_append targetCheck 2656 2672 2688 checked_2656_2672 checked_2672_2688)))

end Nonrational.TerminalVerification.PaperPolygon
