module
public import PaperPolygon.Checks.C000
public import PaperPolygon.Checks.C001
public import PaperPolygon.Checks.C002
public import PaperPolygon.Checks.C003
public import PaperPolygon.Checks.C004
public import PaperPolygon.Checks.C005
public import PaperPolygon.Checks.C006
public import PaperPolygon.Checks.C007
public import PaperPolygon.Checks.C008
public import PaperPolygon.Checks.C009
public import PaperPolygon.Checks.C010
public import PaperPolygon.Checks.C011
public import PaperPolygon.Checks.C012
public import PaperPolygon.Checks.C013
public import PaperPolygon.Checks.C014
public import PaperPolygon.Checks.C015
public import PaperPolygon.Checks.C016
public import PaperPolygon.Checks.C017
public import PaperPolygon.Checks.C018
public import PaperPolygon.Checks.C019
public import PaperPolygon.Checks.C020
public import PaperPolygon.Checks.C021
public import PaperPolygon.Checks.C022
public import PaperPolygon.Checks.C023
public import PaperPolygon.Checks.C024
public import PaperPolygon.Checks.C025
public import PaperPolygon.Checks.C026
public import PaperPolygon.Checks.C027
public import PaperPolygon.Checks.C028
public import PaperPolygon.Checks.C029
public import PaperPolygon.Checks.C030
public import PaperPolygon.Checks.C031
public import PaperPolygon.Checks.C032
public import PaperPolygon.Checks.C033
public import PaperPolygon.Checks.C034
public import PaperPolygon.Checks.C035
public import PaperPolygon.Checks.C036

@[expose] public section

namespace Nonrational.TerminalVerification.PaperPolygon
open Nonrational.TerminalData Papers.RationalityTen.FiniteChecks

theorem all_targets : Interval targetCheck 0 4726 :=
  (interval_append targetCheck 0 2304 4726 (interval_append targetCheck 0 1152 2304 (interval_append targetCheck 0 512 1152 (interval_append targetCheck 0 256 512 (interval_append targetCheck 0 128 256 chunk_000 chunk_001) (interval_append targetCheck 256 384 512 chunk_002 chunk_003)) (interval_append targetCheck 512 768 1152 (interval_append targetCheck 512 640 768 chunk_004 chunk_005) (interval_append targetCheck 768 896 1152 chunk_006 (interval_append targetCheck 896 1024 1152 chunk_007 chunk_008)))) (interval_append targetCheck 1152 1664 2304 (interval_append targetCheck 1152 1408 1664 (interval_append targetCheck 1152 1280 1408 chunk_009 chunk_010) (interval_append targetCheck 1408 1536 1664 chunk_011 chunk_012)) (interval_append targetCheck 1664 1920 2304 (interval_append targetCheck 1664 1792 1920 chunk_013 chunk_014) (interval_append targetCheck 1920 2048 2304 chunk_015 (interval_append targetCheck 2048 2176 2304 chunk_016 chunk_017))))) (interval_append targetCheck 2304 3456 4726 (interval_append targetCheck 2304 2816 3456 (interval_append targetCheck 2304 2560 2816 (interval_append targetCheck 2304 2432 2560 chunk_018 chunk_019) (interval_append targetCheck 2560 2688 2816 chunk_020 chunk_021)) (interval_append targetCheck 2816 3072 3456 (interval_append targetCheck 2816 2944 3072 chunk_022 chunk_023) (interval_append targetCheck 3072 3200 3456 chunk_024 (interval_append targetCheck 3200 3328 3456 chunk_025 chunk_026)))) (interval_append targetCheck 3456 4096 4726 (interval_append targetCheck 3456 3712 4096 (interval_append targetCheck 3456 3584 3712 chunk_027 chunk_028) (interval_append targetCheck 3712 3840 4096 chunk_029 (interval_append targetCheck 3840 3968 4096 chunk_030 chunk_031))) (interval_append targetCheck 4096 4352 4726 (interval_append targetCheck 4096 4224 4352 chunk_032 chunk_033) (interval_append targetCheck 4352 4480 4726 chunk_034 (interval_append targetCheck 4480 4608 4726 chunk_035 chunk_036))))))

theorem targets_checked (j : Nat) (hj : j < targetCount) : targetCheck j = true :=
  all_targets j (Nat.zero_le _) hj

end Nonrational.TerminalVerification.PaperPolygon
