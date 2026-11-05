module
prelude
public import InducedTerminalMatches.Basic

@[expose] public section

/-! Exact full-boundary matches, batch 105. Both facet and polygon
families are checked in both directions after the recorded permutation. -/

namespace Nonrational.InducedTerminalMatches.M105
open Nonrational.InducedTerminalMatches
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- m14_e11_q2_type0.jsonl.gz, graph 7915, terminal 1; projection:R_one_six_0506.
noncomputable def r3360 : Entry :=
  ⟨⟨[139,198,218,236,277,293,342,419,422,597,613,632,681,795],[11,21,26,37,70,82,84,88,100,104,131,134,137,138,161,164,168,194,196,200,259,261,262,273,274,276,289,292,418,521,529,536,545,552,581,592,608]⟩,
   ⟨1043,92214069570,165180162195⟩⟩
theorem r3360_checked : check r3360 = true := by decide +kernel

-- m14_e11_q2_type0.jsonl.gz, graph 7938, terminal 0; projection:R_one_six_0516.
noncomputable def r3361 : Entry :=
  ⟨⟨[105,181,202,236,263,278,301,410,412,535,625,690,738,843],[7,21,22,37,41,44,49,73,74,97,104,138,140,146,148,164,176,194,200,224,259,261,262,265,266,268,274,276,408,515,529,530,560,577,578,608,674]⟩,
   ⟨1045,350114883120,306328245120⟩⟩
theorem r3361_checked : check r3361 = true := by decide +kernel

-- m14_e11_q2_type0.jsonl.gz, graph 7960, terminal 0; projection:R_one_six_0502.
noncomputable def r3362 : Entry :=
  ⟨⟨[141,153,174,234,285,291,310,485,542,586,611,721,728,787],[13,14,22,25,28,35,38,74,97,98,133,137,140,145,152,164,170,193,200,224,259,261,273,274,276,289,290,292,515,522,529,530,536,577,578,584,720]⟩,
   ⟨1039,619636486530,623649443880⟩⟩
theorem r3362_checked : check r3362 = true := by decide +kernel

-- m14_e11_q2_type0.jsonl.gz, graph 8125, terminal 0; projection:R_one_six_0360.
noncomputable def r3363 : Entry :=
  ⟨⟨[169,188,201,213,275,327,361,362,433,535,554,572,718,818],[7,19,21,41,42,60,69,70,73,74,137,140,145,148,161,168,176,193,196,200,259,273,274,289,290,304,321,322,360,518,522,524,530,532,546,552,560]⟩,
   ⟨932,378235462470,379040375670⟩⟩
theorem r3363_checked : check r3363 = true := by decide +kernel

-- m14_e11_q2_type0.jsonl.gz, graph 8125, terminal 1; projection:R_one_six_0524.
noncomputable def r3364 : Entry :=
  ⟨⟨[149,197,203,204,341,342,355,441,534,555,590,684,692,818],[11,21,22,35,41,67,69,70,74,76,133,137,140,145,148,168,176,193,196,200,273,274,289,290,304,321,322,340,518,522,524,530,532,546,552,560,676]⟩,
   ⟨1052,486556194915,423343096965⟩⟩
theorem r3364_checked : check r3364 = true := by decide +kernel

-- m14_e11_q2_type0.jsonl.gz, graph 8232, terminal 0; projection:R_one_six_0474.
noncomputable def r3365 : Entry :=
  ⟨⟨[105,198,203,213,277,357,364,435,555,562,590,662,796,824],[11,21,35,41,50,69,70,73,74,76,97,104,131,134,145,146,148,193,194,196,261,268,273,276,289,296,304,356,518,522,524,530,532,546,552,560,792]⟩,
   ⟨1031,502649755155,234386424855⟩⟩
theorem r3365_checked : check r3365 = true := by decide +kernel

-- m14_e11_q2_type0.jsonl.gz, graph 8238, terminal 0; projection:R_one_six_0562.
noncomputable def r3366 : Entry :=
  ⟨⟨[199,210,236,240,263,301,339,398,553,629,682,690,793,794],[7,37,41,44,67,69,81,82,100,112,134,138,140,146,168,176,194,196,208,224,259,261,262,265,266,268,273,274,521,522,529,530,545,552,560,674,792]⟩,
   ⟨4715,383881867395,554983228770⟩⟩
theorem r3366_checked : check r3366 = true := by decide +kernel

-- m14_e11_q2_type0.jsonl.gz, graph 8238, terminal 1; projection:R_one_six_0531.
noncomputable def r3367 : Entry :=
  ⟨⟨[198,211,236,240,275,301,327,398,553,629,682,690,793,794],[19,37,41,44,67,69,70,81,100,112,134,138,140,146,168,176,194,196,208,224,259,261,262,265,266,268,273,274,521,522,529,530,545,552,560,674,792]⟩,
   ⟨4686,383881867395,554983228770⟩⟩
theorem r3367_checked : check r3367 = true := by decide +kernel

#print axioms r3360_checked

end Nonrational.InducedTerminalMatches.M105
