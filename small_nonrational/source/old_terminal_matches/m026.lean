module
prelude
public import InducedTerminalMatches.Basic

@[expose] public section

/-! Exact full-boundary matches, batch 26. Both facet and polygon
families are checked in both directions after the recorded permutation. -/

namespace Nonrational.OldTerminalMatches.M026
open Nonrational.InducedTerminalMatches
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- six_extra_orbit_dags/full_m15e11q3_types5.json.gz, graph 870, terminal 117; gp:PrismNine.
noncomputable def r1664 : Entry :=
  ⟨⟨[63,91,173,201,310,338,420,519,568,707,728,838,880,901,936],[7,27,45,54,56,67,73,82,88,133,137,164,168,193,200,262,274,292,304,322,336,388,416,515,517,518,536,552,560,578,592,641,648,704,772,800,832,896]⟩,
   ⟨2041,654820258320,654820258320⟩⟩
theorem r1664_checked : check r1664 = true := by decide +kernel

-- six_extra_orbit_dags/full_m15e11q3_types5.json.gz, graph 870, terminal 118; projection:R_new_prism_0118.
noncomputable def r1665 : Entry :=
  ⟨⟨[63,91,173,201,310,338,420,519,568,707,744,838,856,901,944],[7,27,45,54,56,67,73,82,88,133,137,164,168,193,200,262,274,292,304,322,336,388,416,515,517,518,536,552,560,578,584,641,672,704,772,784,832,896]⟩,
   ⟨1571,654720713505,654802362630⟩⟩
theorem r1665_checked : check r1665 = true := by decide +kernel

-- six_extra_orbit_dags/full_m15e11q3_types5.json.gz, graph 870, terminal 396; integer:D0.
noncomputable def r1666 : Entry :=
  ⟨⟨[63,155,199,201,248,452,480,557,566,585,658,837,872,902,944],[7,27,45,54,56,69,73,104,131,134,137,146,152,176,193,196,200,224,324,352,388,416,448,517,518,521,530,548,552,560,577,584,642,656,772,800,832,896]⟩,
   ⟨1990,556002195090,109292433540⟩⟩
theorem r1666_checked : check r1666 = true := by decide +kernel

-- six_extra_orbit_dags/full_m15e11q3_types5.json.gz, graph 870, terminal 397; projection:R_new_prism_0397.
noncomputable def r1667 : Entry :=
  ⟨⟨[63,155,201,248,263,451,480,557,566,585,658,837,872,902,944],[7,27,45,54,56,73,104,131,137,146,152,176,193,200,224,259,261,262,321,352,386,416,448,517,518,521,530,548,552,560,577,584,642,656,772,800,832,896]⟩,
   ⟨1572,620746851105,650238959880⟩⟩
theorem r1667_checked : check r1667 = true := by decide +kernel

-- six_extra_orbit_dags/full_m15e11q3_types5.json.gz, graph 870, terminal 398; integer:D4.
noncomputable def r1668 : Entry :=
  ⟨⟨[63,155,201,263,312,451,472,557,566,585,658,837,872,902,944],[7,27,45,54,56,73,131,137,146,152,193,200,259,261,262,280,296,304,321,328,386,400,448,517,518,521,530,548,552,560,577,584,642,656,772,800,832,896]⟩,
   ⟨1991,517033054260,380493632610⟩⟩
theorem r1668_checked : check r1668 = true := by decide +kernel

-- six_extra_orbit_dags/full_m15e11q3_types5.json.gz, graph 870, terminal 502; projection:R_new_prism_0502.
noncomputable def r1669 : Entry :=
  ⟨⟨[63,91,118,195,228,344,457,496,519,557,710,777,824,899,932],[7,27,45,54,56,67,70,73,82,88,100,112,131,164,193,194,196,224,265,280,304,328,336,385,416,448,515,517,518,521,548,552,642,644,769,776,800,896]⟩,
   ⟨1573,654815085345,654819139845⟩⟩
theorem r1669_checked : check r1669 = true := by decide +kernel

-- six_extra_orbit_dags/full_m15e11q3_types5.json.gz, graph 870, terminal 677; projection:R_new_prism_0677.
noncomputable def r1670 : Entry :=
  ⟨⟨[63,91,118,228,329,344,451,496,519,557,643,710,824,905,932],[7,27,45,54,56,67,70,73,82,88,100,112,131,164,194,196,224,265,280,304,321,328,336,385,416,448,515,517,518,521,548,552,641,642,644,776,800,896]⟩,
   ⟨1574,654815085345,654819139845⟩⟩
theorem r1670_checked : check r1670 = true := by decide +kernel

-- six_extra_orbit_dags/full_m15e11q3_types5.json.gz, graph 870, terminal 706; projection:R_new_prism_0706.
noncomputable def r1671 : Entry :=
  ⟨⟨[63,155,182,195,201,216,323,454,496,557,632,775,841,864,932],[7,27,45,54,56,67,73,88,112,131,134,137,146,152,164,176,193,194,200,208,259,262,321,322,352,388,416,448,517,521,548,552,584,608,769,772,800,832]⟩,
   ⟨1575,654820257825,654820258050⟩⟩
theorem r1671_checked : check r1671 = true := by decide +kernel

-- six_extra_orbit_dags/full_m15e11q3_types5.json.gz, graph 870, terminal 711; projection:R_new_prism_0711.
noncomputable def r1672 : Entry :=
  ⟨⟨[63,155,182,195,201,216,323,454,557,632,688,775,841,932,976],[7,27,45,54,56,67,73,88,131,134,137,146,152,164,176,193,194,200,208,259,262,321,322,388,448,517,521,548,552,560,584,592,656,672,769,772,832,896]⟩,
   ⟨1576,654820257825,654820258050⟩⟩
theorem r1672_checked : check r1672 = true := by decide +kernel

-- six_extra_orbit_dags/full_m15e11q3_types5.json.gz, graph 870, terminal 741; projection:R_new_prism_0741.
noncomputable def r1673 : Entry :=
  ⟨⟨[63,155,182,195,201,216,323,344,454,496,557,775,824,841,932],[7,27,45,54,56,67,73,88,131,134,137,146,152,164,176,193,194,200,208,259,262,280,304,321,322,328,336,388,416,448,517,521,548,552,769,772,776,800]⟩,
   ⟨1577,654820257825,654820258050⟩⟩
theorem r1673_checked : check r1673 = true := by decide +kernel

#print axioms r1664_checked

end Nonrational.OldTerminalMatches.M026
