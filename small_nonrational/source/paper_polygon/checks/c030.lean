module
public import PaperPolygon.RawBounds

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Nonrational.TerminalVerification.PaperPolygon
open Papers.RationalityTen.FiniteChecks

/- Exact target indices 3840 through 3967. -/
theorem checked_3840_3856 : Interval targetCheck 3840 3856 :=
  interval_of_check targetCheck 3840 16 (by decide +kernel)

theorem checked_3856_3872 : Interval targetCheck 3856 3872 :=
  interval_of_check targetCheck 3856 16 (by decide +kernel)

theorem checked_3872_3888 : Interval targetCheck 3872 3888 :=
  interval_of_check targetCheck 3872 16 (by decide +kernel)

theorem checked_3888_3904 : Interval targetCheck 3888 3904 :=
  interval_of_check targetCheck 3888 16 (by decide +kernel)

theorem checked_3904_3920 : Interval targetCheck 3904 3920 :=
  interval_of_check targetCheck 3904 16 (by decide +kernel)

theorem checked_3920_3936 : Interval targetCheck 3920 3936 :=
  interval_of_check targetCheck 3920 16 (by decide +kernel)

theorem checked_3936_3952 : Interval targetCheck 3936 3952 :=
  interval_of_check targetCheck 3936 16 (by decide +kernel)

theorem checked_3952_3968 : Interval targetCheck 3952 3968 :=
  interval_of_check targetCheck 3952 16 (by decide +kernel)

theorem chunk_030 : Interval targetCheck 3840 3968 :=
  (interval_append targetCheck 3840 3904 3968 (interval_append targetCheck 3840 3872 3904 (interval_append targetCheck 3840 3856 3872 checked_3840_3856 checked_3856_3872) (interval_append targetCheck 3872 3888 3904 checked_3872_3888 checked_3888_3904)) (interval_append targetCheck 3904 3936 3968 (interval_append targetCheck 3904 3920 3936 checked_3904_3920 checked_3920_3936) (interval_append targetCheck 3936 3952 3968 checked_3936_3952 checked_3952_3968)))

end Nonrational.TerminalVerification.PaperPolygon
