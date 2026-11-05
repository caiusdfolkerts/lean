import cubical_indecomposability.rigidity.scale_compatibility

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CubicalIndecomposability.Rigidity

/-! Uniform scaling and translation are the complete solution space. -/

theorem homothetic_000 (h : Assignment) (H : Constraints h) :
    h 0 0 = h 1 0 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_000 h H

theorem homothetic_001 (h : Assignment) (H : Constraints h) :
    h 0 1 = h 1 1 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_001 h H

theorem homothetic_002 (h : Assignment) (H : Constraints h) :
    h 0 2 = h 1 2 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_002 h H

theorem homothetic_003 (h : Assignment) (H : Constraints h) :
    h 0 3 = h 1 3 + ((29636437161 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_003 h H

theorem homothetic_004 (h : Assignment) (H : Constraints h) :
    h 1 0 = h 1 0 + (0 : ℝ) * (h 3 0 - h 1 0) := by
  ring

theorem homothetic_005 (h : Assignment) (H : Constraints h) :
    h 1 1 = h 1 1 + (0 : ℝ) * (h 3 0 - h 1 0) := by
  ring

theorem homothetic_006 (h : Assignment) (H : Constraints h) :
    h 1 2 = h 1 2 + (0 : ℝ) * (h 3 0 - h 1 0) := by
  ring

theorem homothetic_007 (h : Assignment) (H : Constraints h) :
    h 1 3 = h 1 3 + (0 : ℝ) * (h 3 0 - h 1 0) := by
  ring

theorem homothetic_008 (h : Assignment) (H : Constraints h) :
    h 2 0 = h 1 0 + ((129880447682 : ℝ) / 249882082977) * (h 3 0 - h 1 0) := by
  linear_combination value_008 h H

theorem homothetic_009 (h : Assignment) (H : Constraints h) :
    h 2 1 = h 1 1 + ((117193993383 : ℝ) / 333176110636) * (h 3 0 - h 1 0) := by
  linear_combination value_009 h H

theorem homothetic_010 (h : Assignment) (H : Constraints h) :
    h 2 2 = h 1 2 + ((117193993383 : ℝ) / 333176110636) * (h 3 0 - h 1 0) := by
  linear_combination value_010 h H

theorem homothetic_011 (h : Assignment) (H : Constraints h) :
    h 2 3 = h 1 3 + ((19757624774 : ℝ) / 83294027659) * (h 3 0 - h 1 0) := by
  linear_combination value_011 h H

theorem homothetic_012 (h : Assignment) (H : Constraints h) :
    h 3 0 = h 1 0 + (1 : ℝ) * (h 3 0 - h 1 0) := by
  ring

theorem homothetic_013 (h : Assignment) (H : Constraints h) :
    h 3 1 = h 1 1 + (0 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination value_013 h H

theorem homothetic_014 (h : Assignment) (H : Constraints h) :
    h 3 2 = h 1 2 + (0 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination value_014 h H

theorem homothetic_015 (h : Assignment) (H : Constraints h) :
    h 3 3 = h 1 3 + (0 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination value_015 h H

theorem homothetic_016 (h : Assignment) (H : Constraints h) :
    h 4 0 = h 1 0 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_016 h H

theorem homothetic_017 (h : Assignment) (H : Constraints h) :
    h 4 1 = h 1 1 + ((32135819613 : ℝ) / 48000654118) * (h 3 0 - h 1 0) := by
  linear_combination value_017 h H + (1 : ℝ) * (scales0 h H)

theorem homothetic_018 (h : Assignment) (H : Constraints h) :
    h 4 2 = h 1 2 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_018 h H

theorem homothetic_019 (h : Assignment) (H : Constraints h) :
    h 4 3 = h 1 3 + ((29636437161 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_019 h H

theorem homothetic_020 (h : Assignment) (H : Constraints h) :
    h 5 0 = h 1 0 + (0 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination value_020 h H

theorem homothetic_021 (h : Assignment) (H : Constraints h) :
    h 5 1 = h 1 1 + (1 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination (1 : ℝ) * (scales0 h H)

theorem homothetic_022 (h : Assignment) (H : Constraints h) :
    h 5 2 = h 1 2 + (0 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination value_022 h H

theorem homothetic_023 (h : Assignment) (H : Constraints h) :
    h 5 3 = h 1 3 + (0 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination value_023 h H

theorem homothetic_024 (h : Assignment) (H : Constraints h) :
    h 6 0 = h 1 0 + ((129880447682 : ℝ) / 249882082977) * (h 3 0 - h 1 0) := by
  linear_combination value_024 h H

theorem homothetic_025 (h : Assignment) (H : Constraints h) :
    h 6 1 = h 1 1 + ((458114032001 : ℝ) / 666352221272) * (h 3 0 - h 1 0) := by
  linear_combination value_025 h H + (1 : ℝ) * (scales0 h H)

theorem homothetic_026 (h : Assignment) (H : Constraints h) :
    h 6 2 = h 1 2 + ((117193993383 : ℝ) / 333176110636) * (h 3 0 - h 1 0) := by
  linear_combination value_026 h H

theorem homothetic_027 (h : Assignment) (H : Constraints h) :
    h 6 3 = h 1 3 + ((19757624774 : ℝ) / 83294027659) * (h 3 0 - h 1 0) := by
  linear_combination value_027 h H

theorem homothetic_028 (h : Assignment) (H : Constraints h) :
    h 7 0 = h 1 0 + (1 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination value_028 h H

theorem homothetic_029 (h : Assignment) (H : Constraints h) :
    h 7 1 = h 1 1 + (1 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination value_029 h H + (1 : ℝ) * (scales0 h H)

theorem homothetic_030 (h : Assignment) (H : Constraints h) :
    h 7 2 = h 1 2 + (0 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination value_030 h H

theorem homothetic_031 (h : Assignment) (H : Constraints h) :
    h 7 3 = h 1 3 + (0 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination value_031 h H

theorem homothetic_032 (h : Assignment) (H : Constraints h) :
    h 8 0 = h 1 0 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_032 h H

theorem homothetic_033 (h : Assignment) (H : Constraints h) :
    h 8 1 = h 1 1 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_033 h H

theorem homothetic_034 (h : Assignment) (H : Constraints h) :
    h 8 2 = h 1 2 + ((74819036228 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_034 h H + (1 : ℝ) * (scales1 h H)

theorem homothetic_035 (h : Assignment) (H : Constraints h) :
    h 8 3 = h 1 3 + ((29636437161 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_035 h H

theorem homothetic_036 (h : Assignment) (H : Constraints h) :
    h 9 0 = h 1 0 + (0 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination value_036 h H

theorem homothetic_037 (h : Assignment) (H : Constraints h) :
    h 9 1 = h 1 1 + (0 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination value_037 h H

theorem homothetic_038 (h : Assignment) (H : Constraints h) :
    h 9 2 = h 1 2 + (1 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination (1 : ℝ) * (scales1 h H)

theorem homothetic_039 (h : Assignment) (H : Constraints h) :
    h 9 3 = h 1 3 + (0 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination value_039 h H

theorem homothetic_040 (h : Assignment) (H : Constraints h) :
    h 10 0 = h 1 0 + ((129880447682 : ℝ) / 249882082977) * (h 3 0 - h 1 0) := by
  linear_combination value_040 h H

theorem homothetic_041 (h : Assignment) (H : Constraints h) :
    h 10 1 = h 1 1 + ((117193993383 : ℝ) / 333176110636) * (h 3 0 - h 1 0) := by
  linear_combination value_041 h H

theorem homothetic_042 (h : Assignment) (H : Constraints h) :
    h 10 2 = h 1 2 + ((328912582073 : ℝ) / 499764165954) * (h 3 0 - h 1 0) := by
  linear_combination value_042 h H + (1 : ℝ) * (scales1 h H)

theorem homothetic_043 (h : Assignment) (H : Constraints h) :
    h 10 3 = h 1 3 + ((19757624774 : ℝ) / 83294027659) * (h 3 0 - h 1 0) := by
  linear_combination value_043 h H

theorem homothetic_044 (h : Assignment) (H : Constraints h) :
    h 11 0 = h 1 0 + (1 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination value_044 h H

theorem homothetic_045 (h : Assignment) (H : Constraints h) :
    h 11 1 = h 1 1 + (0 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination value_045 h H

theorem homothetic_046 (h : Assignment) (H : Constraints h) :
    h 11 2 = h 1 2 + (1 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination value_046 h H + (1 : ℝ) * (scales1 h H)

theorem homothetic_047 (h : Assignment) (H : Constraints h) :
    h 11 3 = h 1 3 + (0 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination value_047 h H

theorem homothetic_048 (h : Assignment) (H : Constraints h) :
    h 12 0 = h 1 0 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_048 h H

theorem homothetic_049 (h : Assignment) (H : Constraints h) :
    h 12 1 = h 1 1 + ((32135819613 : ℝ) / 48000654118) * (h 3 0 - h 1 0) := by
  linear_combination value_049 h H + (1 : ℝ) * (scales0 h H)

theorem homothetic_050 (h : Assignment) (H : Constraints h) :
    h 12 2 = h 1 2 + ((74819036228 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_050 h H + (1 : ℝ) * (scales1 h H)

theorem homothetic_051 (h : Assignment) (H : Constraints h) :
    h 12 3 = h 1 3 + ((29636437161 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_051 h H

theorem homothetic_052 (h : Assignment) (H : Constraints h) :
    h 13 0 = h 1 0 + (0 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination value_052 h H

theorem homothetic_053 (h : Assignment) (H : Constraints h) :
    h 13 1 = h 1 1 + (1 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination value_053 h H + (1 : ℝ) * (scales0 h H)

theorem homothetic_054 (h : Assignment) (H : Constraints h) :
    h 13 2 = h 1 2 + (1 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination value_054 h H + (1 : ℝ) * (scales1 h H)

theorem homothetic_055 (h : Assignment) (H : Constraints h) :
    h 13 3 = h 1 3 + (0 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination value_055 h H

theorem homothetic_056 (h : Assignment) (H : Constraints h) :
    h 14 0 = h 1 0 + ((129880447682 : ℝ) / 249882082977) * (h 3 0 - h 1 0) := by
  linear_combination value_056 h H

theorem homothetic_057 (h : Assignment) (H : Constraints h) :
    h 14 1 = h 1 1 + ((458114032001 : ℝ) / 666352221272) * (h 3 0 - h 1 0) := by
  linear_combination value_057 h H + (1 : ℝ) * (scales0 h H)

theorem homothetic_058 (h : Assignment) (H : Constraints h) :
    h 14 2 = h 1 2 + ((328912582073 : ℝ) / 499764165954) * (h 3 0 - h 1 0) := by
  linear_combination value_058 h H + (1 : ℝ) * (scales1 h H)

theorem homothetic_059 (h : Assignment) (H : Constraints h) :
    h 14 3 = h 1 3 + ((19757624774 : ℝ) / 83294027659) * (h 3 0 - h 1 0) := by
  linear_combination value_059 h H

theorem homothetic_060 (h : Assignment) (H : Constraints h) :
    h 15 0 = h 1 0 + (1 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination value_060 h H

theorem homothetic_061 (h : Assignment) (H : Constraints h) :
    h 15 1 = h 1 1 + (1 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination value_061 h H + (1 : ℝ) * (scales0 h H)

theorem homothetic_062 (h : Assignment) (H : Constraints h) :
    h 15 2 = h 1 2 + (1 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination value_062 h H + (1 : ℝ) * (scales1 h H)

theorem homothetic_063 (h : Assignment) (H : Constraints h) :
    h 15 3 = h 1 3 + (0 : ℝ) * (h 3 0 - h 1 0) := by
  linear_combination value_063 h H

theorem homothetic_064 (h : Assignment) (H : Constraints h) :
    h 16 0 = h 1 0 + ((282243102288077 : ℝ) / 617857941263449) * (h 3 0 - h 1 0) := by
  linear_combination value_064 h H + ((546216952893660 : ℝ) / 617857941263449) * (scales0 h H) + ((-447088691072218 : ℝ) / 617857941263449) * (scales1 h H)

theorem homothetic_065 (h : Assignment) (H : Constraints h) :
    h 16 1 = h 1 1 + ((158648699407709 : ℝ) / 617857941263449) * (h 3 0 - h 1 0) := by
  linear_combination value_065 h H + ((-814601591351640 : ℝ) / 617857941263449) * (scales0 h H) + ((666766487735972 : ℝ) / 617857941263449) * (scales1 h H)

theorem homothetic_066 (h : Assignment) (H : Constraints h) :
    h 16 2 = h 1 2 + ((158648699407709 : ℝ) / 617857941263449) * (h 3 0 - h 1 0) := by
  linear_combination value_066 h H + ((-814601591351640 : ℝ) / 617857941263449) * (scales0 h H) + ((666766487735972 : ℝ) / 617857941263449) * (scales1 h H)

theorem homothetic_067 (h : Assignment) (H : Constraints h) :
    h 16 3 = h 1 3 + ((144596176908519 : ℝ) / 617857941263449) * (h 3 0 - h 1 0) := by
  linear_combination value_067 h H + ((-88020218368170 : ℝ) / 617857941263449) * (scales0 h H) + ((72046178738391 : ℝ) / 617857941263449) * (scales1 h H)

theorem homothetic_068 (h : Assignment) (H : Constraints h) :
    h 17 0 = h 1 0 + ((1176016025891 : ℝ) / 2704182658048) * (h 3 0 - h 1 0) := by
  linear_combination value_068 h H + ((3240044152965 : ℝ) / 1352091329024) * (scales0 h H) + ((-5304072280039 : ℝ) / 2704182658048) * (scales1 h H)

theorem homothetic_069 (h : Assignment) (H : Constraints h) :
    h 17 1 = h 1 1 + ((2975709287677 : ℝ) / 13520913290240) * (h 3 0 - h 1 0) := by
  linear_combination value_069 h H + ((1639676546271 : ℝ) / 1352091329024) * (scales0 h H) + ((-13421056175033 : ℝ) / 13520913290240) * (scales1 h H)

theorem homothetic_070 (h : Assignment) (H : Constraints h) :
    h 17 2 = h 1 2 + ((2975709287677 : ℝ) / 13520913290240) * (h 3 0 - h 1 0) := by
  linear_combination value_070 h H + ((1639676546271 : ℝ) / 1352091329024) * (scales0 h H) + ((-13421056175033 : ℝ) / 13520913290240) * (scales1 h H)

theorem homothetic_071 (h : Assignment) (H : Constraints h) :
    h 17 3 = h 1 3 + ((1452185420889 : ℝ) / 6760456645120) * (h 3 0 - h 1 0) := by
  linear_combination value_071 h H + ((800183803347 : ℝ) / 676045664512) * (scales0 h H) + ((-6549652612581 : ℝ) / 6760456645120) * (scales1 h H)

theorem homothetic_072 (h : Assignment) (H : Constraints h) :
    h 18 0 = h 1 0 + ((39963337415001 : ℝ) / 83792536655077) * (h 3 0 - h 1 0) := by
  linear_combination value_072 h H + ((-1225096040646180 : ℝ) / 2429983562997233) * (scales0 h H) + ((1002763796232614 : ℝ) / 2429983562997233) * (scales1 h H)

theorem homothetic_073 (h : Assignment) (H : Constraints h) :
    h 18 1 = h 1 1 + ((42614921436437 : ℝ) / 167585073310154) * (h 3 0 - h 1 0) := by
  linear_combination value_073 h H + ((-2787378521826375 : ℝ) / 2429983562997233) * (scales0 h H) + ((4563041876471325 : ℝ) / 4859967125994466) * (scales1 h H)

theorem homothetic_074 (h : Assignment) (H : Constraints h) :
    h 18 2 = h 1 2 + ((42614921436437 : ℝ) / 167585073310154) * (h 3 0 - h 1 0) := by
  linear_combination value_074 h H + ((-2787378521826375 : ℝ) / 2429983562997233) * (scales0 h H) + ((4563041876471325 : ℝ) / 4859967125994466) * (scales1 h H)

theorem homothetic_075 (h : Assignment) (H : Constraints h) :
    h 18 3 = h 1 3 + ((19500775651938 : ℝ) / 83792536655077) * (h 3 0 - h 1 0) := by
  linear_combination value_075 h H + ((-4414807190880 : ℝ) / 83792536655077) * (scales0 h H) + ((3613601441424 : ℝ) / 83792536655077) * (scales1 h H)

theorem homothetic_076 (h : Assignment) (H : Constraints h) :
    h 19 0 = h 1 0 + ((3440082303493 : ℝ) / 6760456645120) * (h 3 0 - h 1 0) := by
  linear_combination value_076 h H + ((-12807158174847 : ℝ) / 4732319651584) * (scales0 h H) + ((104828961357081 : ℝ) / 47323196515840) * (scales1 h H)

theorem homothetic_077 (h : Assignment) (H : Constraints h) :
    h 19 1 = h 1 1 + ((2975709287677 : ℝ) / 13520913290240) * (h 3 0 - h 1 0) := by
  linear_combination value_077 h H + ((1639676546271 : ℝ) / 1352091329024) * (scales0 h H) + ((-13421056175033 : ℝ) / 13520913290240) * (scales1 h H)

theorem homothetic_078 (h : Assignment) (H : Constraints h) :
    h 19 2 = h 1 2 + ((2975709287677 : ℝ) / 13520913290240) * (h 3 0 - h 1 0) := by
  linear_combination value_078 h H + ((1639676546271 : ℝ) / 1352091329024) * (scales0 h H) + ((-13421056175033 : ℝ) / 13520913290240) * (scales1 h H)

theorem homothetic_079 (h : Assignment) (H : Constraints h) :
    h 19 3 = h 1 3 + ((1452185420889 : ℝ) / 6760456645120) * (h 3 0 - h 1 0) := by
  linear_combination value_079 h H + ((800183803347 : ℝ) / 676045664512) * (scales0 h H) + ((-6549652612581 : ℝ) / 6760456645120) * (scales1 h H)

theorem homothetic_080 (h : Assignment) (H : Constraints h) :
    h 20 0 = h 1 0 + ((1100037740749235 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0) := by
  linear_combination value_080 h H + ((1857137639838444 : ℝ) / 2542109602773571) * (scales0 h H) + ((-1624489678420774 : ℝ) / 2542109602773571) * (scales1 h H)

theorem homothetic_081 (h : Assignment) (H : Constraints h) :
    h 20 1 = h 1 1 + ((3643447258418433 : ℝ) / 5084219205547142) * (h 3 0 - h 1 0) := by
  linear_combination value_081 h H + ((4099313112460801 : ℝ) / 2542109602773571) * (scales0 h H) + ((-1362128995946455 : ℝ) / 2542109602773571) * (scales1 h H)

theorem homothetic_082 (h : Assignment) (H : Constraints h) :
    h 20 2 = h 1 2 + ((744044857571303 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0) := by
  linear_combination value_082 h H + ((-2769645410595576 : ℝ) / 2542109602773571) * (scales0 h H) + ((2422685473538396 : ℝ) / 2542109602773571) * (scales1 h H)

theorem homothetic_083 (h : Assignment) (H : Constraints h) :
    h 20 3 = h 1 3 + ((604790773144527 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0) := by
  linear_combination value_083 h H + ((-299268742451778 : ℝ) / 2542109602773571) * (scales0 h H) + ((261778649443113 : ℝ) / 2542109602773571) * (scales1 h H)

theorem homothetic_084 (h : Assignment) (H : Constraints h) :
    h 21 0 = h 1 0 + ((120001635295 : ℝ) / 358549019234) * (h 3 0 - h 1 0) := by
  linear_combination value_084 h H + ((11016150120081 : ℝ) / 4123313721191) * (scales0 h H) + ((-19272262628377 : ℝ) / 8246627442382) * (scales1 h H)

theorem homothetic_085 (h : Assignment) (H : Constraints h) :
    h 21 1 = h 1 1 + ((588086130579 : ℝ) / 717098038468) * (h 3 0 - h 1 0) := by
  linear_combination value_085 h H + ((-17983328509141 : ℝ) / 41233137211910) * (scales0 h H) + ((103596562034867 : ℝ) / 82466274423820) * (scales1 h H)

theorem homothetic_086 (h : Assignment) (H : Constraints h) :
    h 21 2 = h 1 2 + ((60728760973 : ℝ) / 358549019234) * (h 3 0 - h 1 0) := by
  linear_combination value_086 h H + ((27874501286607 : ℝ) / 20616568605955) * (scales0 h H) + ((-48765195061319 : ℝ) / 41233137211910) * (scales1 h H)

theorem homothetic_087 (h : Assignment) (H : Constraints h) :
    h 21 3 = h 1 3 + ((29636437161 : ℝ) / 179274509617) * (h 3 0 - h 1 0) := by
  linear_combination value_087 h H + ((27206249313798 : ℝ) / 20616568605955) * (scales0 h H) + ((-23798059040283 : ℝ) / 20616568605955) * (scales1 h H)

theorem homothetic_088 (h : Assignment) (H : Constraints h) :
    h 22 0 = h 1 0 + ((2411684364523635 : ℝ) / 4911369189790666) * (h 3 0 - h 1 0) := by
  linear_combination value_088 h H + ((-1041331634549253 : ℝ) / 2455684594895333) * (scales0 h H) + ((1821763186368301 : ℝ) / 4911369189790666) * (scales1 h H)

theorem homothetic_089 (h : Assignment) (H : Constraints h) :
    h 22 1 = h 1 1 + ((28364274250472077 : ℝ) / 39290953518325328) * (h 3 0 - h 1 0) := by
  linear_combination value_089 h H + ((29624035164323443 : ℝ) / 19645476759162664) * (scales0 h H) + ((-17457042264366243 : ℝ) / 39290953518325328) * (scales1 h H)

theorem homothetic_090 (h : Assignment) (H : Constraints h) :
    h 22 2 = h 1 2 + ((5626268271645667 : ℝ) / 19645476759162664) * (h 3 0 - h 1 0) := by
  linear_combination value_090 h H + ((-9477086974209675 : ℝ) / 9822738379581332) * (scales0 h H) + ((16579740392789475 : ℝ) / 19645476759162664) * (scales1 h H)

theorem homothetic_091 (h : Assignment) (H : Constraints h) :
    h 22 3 = h 1 3 + ((575124699546366 : ℝ) / 2455684594895333) * (h 3 0 - h 1 0) := by
  linear_combination value_091 h H + ((-108824997255192 : ℝ) / 2455684594895333) * (scales0 h H) + ((95192236161132 : ℝ) / 2455684594895333) * (scales1 h H)

theorem homothetic_092 (h : Assignment) (H : Constraints h) :
    h 23 0 = h 1 0 + ((780582375658 : ℝ) / 1254921567319) * (h 3 0 - h 1 0) := by
  linear_combination value_092 h H + ((-435443377944798 : ℝ) / 144315980241685) * (scales0 h H) + ((380894370903783 : ℝ) / 144315980241685) * (scales1 h H)

theorem homothetic_093 (h : Assignment) (H : Constraints h) :
    h 23 1 = h 1 1 + ((588086130579 : ℝ) / 717098038468) * (h 3 0 - h 1 0) := by
  linear_combination value_093 h H + ((-17983328509141 : ℝ) / 41233137211910) * (scales0 h H) + ((103596562034867 : ℝ) / 82466274423820) * (scales1 h H)

theorem homothetic_094 (h : Assignment) (H : Constraints h) :
    h 23 2 = h 1 2 + ((60728760973 : ℝ) / 358549019234) * (h 3 0 - h 1 0) := by
  linear_combination value_094 h H + ((27874501286607 : ℝ) / 20616568605955) * (scales0 h H) + ((-48765195061319 : ℝ) / 41233137211910) * (scales1 h H)

theorem homothetic_095 (h : Assignment) (H : Constraints h) :
    h 23 3 = h 1 3 + ((29636437161 : ℝ) / 179274509617) * (h 3 0 - h 1 0) := by
  linear_combination value_095 h H + ((27206249313798 : ℝ) / 20616568605955) * (scales0 h H) + ((-23798059040283 : ℝ) / 20616568605955) * (scales1 h H)

theorem homothetic_096 (h : Assignment) (H : Constraints h) :
    h 24 0 = h 1 0 + ((1100037740749235 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0) := by
  linear_combination value_096 h H + ((1857137639838444 : ℝ) / 2542109602773571) * (scales0 h H) + ((-1624489678420774 : ℝ) / 2542109602773571) * (scales1 h H)

theorem homothetic_097 (h : Assignment) (H : Constraints h) :
    h 24 1 = h 1 1 + ((744044857571303 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0) := by
  linear_combination value_097 h H + ((-2769645410595576 : ℝ) / 2542109602773571) * (scales0 h H) + ((2422685473538396 : ℝ) / 2542109602773571) * (scales1 h H)

theorem homothetic_098 (h : Assignment) (H : Constraints h) :
    h 24 2 = h 1 2 + ((1976061186791234 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0) := by
  linear_combination value_098 h H + ((5083036935812586 : ℝ) / 2542109602773571) * (scales0 h H) + ((-1904163446744410 : ℝ) / 2542109602773571) * (scales1 h H)

theorem homothetic_099 (h : Assignment) (H : Constraints h) :
    h 24 3 = h 1 3 + ((604790773144527 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0) := by
  linear_combination value_099 h H + ((-299268742451778 : ℝ) / 2542109602773571) * (scales0 h H) + ((261778649443113 : ℝ) / 2542109602773571) * (scales1 h H)

theorem homothetic_100 (h : Assignment) (H : Constraints h) :
    h 25 0 = h 1 0 + ((120001635295 : ℝ) / 358549019234) * (h 3 0 - h 1 0) := by
  linear_combination value_100 h H + ((11016150120081 : ℝ) / 4123313721191) * (scales0 h H) + ((-19272262628377 : ℝ) / 8246627442382) * (scales1 h H)

theorem homothetic_101 (h : Assignment) (H : Constraints h) :
    h 25 1 = h 1 1 + ((60728760973 : ℝ) / 358549019234) * (h 3 0 - h 1 0) := by
  linear_combination value_101 h H + ((27874501286607 : ℝ) / 20616568605955) * (scales0 h H) + ((-48765195061319 : ℝ) / 41233137211910) * (scales1 h H)

theorem homothetic_102 (h : Assignment) (H : Constraints h) :
    h 25 2 = h 1 2 + ((163728347711 : ℝ) / 179274509617) * (h 3 0 - h 1 0) := by
  linear_combination value_102 h H + ((-14271376629708 : ℝ) / 20616568605955) * (scales0 h H) + ((33100136616473 : ℝ) / 20616568605955) * (scales1 h H)

theorem homothetic_103 (h : Assignment) (H : Constraints h) :
    h 25 3 = h 1 3 + ((29636437161 : ℝ) / 179274509617) * (h 3 0 - h 1 0) := by
  linear_combination value_103 h H + ((27206249313798 : ℝ) / 20616568605955) * (scales0 h H) + ((-23798059040283 : ℝ) / 20616568605955) * (scales1 h H)

theorem homothetic_104 (h : Assignment) (H : Constraints h) :
    h 26 0 = h 1 0 + ((2411684364523635 : ℝ) / 4911369189790666) * (h 3 0 - h 1 0) := by
  linear_combination value_104 h H + ((-1041331634549253 : ℝ) / 2455684594895333) * (scales0 h H) + ((1821763186368301 : ℝ) / 4911369189790666) * (scales1 h H)

theorem homothetic_105 (h : Assignment) (H : Constraints h) :
    h 26 1 = h 1 1 + ((5626268271645667 : ℝ) / 19645476759162664) * (h 3 0 - h 1 0) := by
  linear_combination value_105 h H + ((-9477086974209675 : ℝ) / 9822738379581332) * (scales0 h H) + ((16579740392789475 : ℝ) / 19645476759162664) * (scales1 h H)

theorem homothetic_106 (h : Assignment) (H : Constraints h) :
    h 26 2 = h 1 2 + ((7703724177912473 : ℝ) / 9822738379581332) * (h 3 0 - h 1 0) := by
  linear_combination value_106 h H + ((9145265966661627 : ℝ) / 4911369189790666) * (scales0 h H) + ((-6176495980395327 : ℝ) / 9822738379581332) * (scales1 h H)

theorem homothetic_107 (h : Assignment) (H : Constraints h) :
    h 26 3 = h 1 3 + ((575124699546366 : ℝ) / 2455684594895333) * (h 3 0 - h 1 0) := by
  linear_combination value_107 h H + ((-108824997255192 : ℝ) / 2455684594895333) * (scales0 h H) + ((95192236161132 : ℝ) / 2455684594895333) * (scales1 h H)

theorem homothetic_108 (h : Assignment) (H : Constraints h) :
    h 27 0 = h 1 0 + ((780582375658 : ℝ) / 1254921567319) * (h 3 0 - h 1 0) := by
  linear_combination value_108 h H + ((-435443377944798 : ℝ) / 144315980241685) * (scales0 h H) + ((380894370903783 : ℝ) / 144315980241685) * (scales1 h H)

theorem homothetic_109 (h : Assignment) (H : Constraints h) :
    h 27 1 = h 1 1 + ((60728760973 : ℝ) / 358549019234) * (h 3 0 - h 1 0) := by
  linear_combination value_109 h H + ((27874501286607 : ℝ) / 20616568605955) * (scales0 h H) + ((-48765195061319 : ℝ) / 41233137211910) * (scales1 h H)

theorem homothetic_110 (h : Assignment) (H : Constraints h) :
    h 27 2 = h 1 2 + ((163728347711 : ℝ) / 179274509617) * (h 3 0 - h 1 0) := by
  linear_combination value_110 h H + ((-14271376629708 : ℝ) / 20616568605955) * (scales0 h H) + ((33100136616473 : ℝ) / 20616568605955) * (scales1 h H)

theorem homothetic_111 (h : Assignment) (H : Constraints h) :
    h 27 3 = h 1 3 + ((29636437161 : ℝ) / 179274509617) * (h 3 0 - h 1 0) := by
  linear_combination value_111 h H + ((27206249313798 : ℝ) / 20616568605955) * (scales0 h H) + ((-23798059040283 : ℝ) / 20616568605955) * (scales1 h H)

theorem homothetic_112 (h : Assignment) (H : Constraints h) :
    h 28 0 = h 1 0 + ((1100037740749235 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0) := by
  linear_combination value_112 h H + ((1857137639838444 : ℝ) / 2542109602773571) * (scales0 h H) + ((-1624489678420774 : ℝ) / 2542109602773571) * (scales1 h H)

theorem homothetic_113 (h : Assignment) (H : Constraints h) :
    h 28 1 = h 1 1 + ((3643447258418433 : ℝ) / 5084219205547142) * (h 3 0 - h 1 0) := by
  linear_combination value_113 h H + ((4099313112460801 : ℝ) / 2542109602773571) * (scales0 h H) + ((-1362128995946455 : ℝ) / 2542109602773571) * (scales1 h H)

theorem homothetic_114 (h : Assignment) (H : Constraints h) :
    h 28 2 = h 1 2 + ((1976061186791234 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0) := by
  linear_combination value_114 h H + ((5083036935812586 : ℝ) / 2542109602773571) * (scales0 h H) + ((-1904163446744410 : ℝ) / 2542109602773571) * (scales1 h H)

theorem homothetic_115 (h : Assignment) (H : Constraints h) :
    h 28 3 = h 1 3 + ((604790773144527 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0) := by
  linear_combination value_115 h H + ((-299268742451778 : ℝ) / 2542109602773571) * (scales0 h H) + ((261778649443113 : ℝ) / 2542109602773571) * (scales1 h H)

theorem homothetic_116 (h : Assignment) (H : Constraints h) :
    h 29 0 = h 1 0 + ((120001635295 : ℝ) / 358549019234) * (h 3 0 - h 1 0) := by
  linear_combination value_116 h H + ((11016150120081 : ℝ) / 4123313721191) * (scales0 h H) + ((-19272262628377 : ℝ) / 8246627442382) * (scales1 h H)

theorem homothetic_117 (h : Assignment) (H : Constraints h) :
    h 29 1 = h 1 1 + ((588086130579 : ℝ) / 717098038468) * (h 3 0 - h 1 0) := by
  linear_combination value_117 h H + ((-17983328509141 : ℝ) / 41233137211910) * (scales0 h H) + ((103596562034867 : ℝ) / 82466274423820) * (scales1 h H)

theorem homothetic_118 (h : Assignment) (H : Constraints h) :
    h 29 2 = h 1 2 + ((163728347711 : ℝ) / 179274509617) * (h 3 0 - h 1 0) := by
  linear_combination value_118 h H + ((-14271376629708 : ℝ) / 20616568605955) * (scales0 h H) + ((33100136616473 : ℝ) / 20616568605955) * (scales1 h H)

theorem homothetic_119 (h : Assignment) (H : Constraints h) :
    h 29 3 = h 1 3 + ((29636437161 : ℝ) / 179274509617) * (h 3 0 - h 1 0) := by
  linear_combination value_119 h H + ((27206249313798 : ℝ) / 20616568605955) * (scales0 h H) + ((-23798059040283 : ℝ) / 20616568605955) * (scales1 h H)

theorem homothetic_120 (h : Assignment) (H : Constraints h) :
    h 30 0 = h 1 0 + ((2411684364523635 : ℝ) / 4911369189790666) * (h 3 0 - h 1 0) := by
  linear_combination value_120 h H + ((-1041331634549253 : ℝ) / 2455684594895333) * (scales0 h H) + ((1821763186368301 : ℝ) / 4911369189790666) * (scales1 h H)

theorem homothetic_121 (h : Assignment) (H : Constraints h) :
    h 30 1 = h 1 1 + ((28364274250472077 : ℝ) / 39290953518325328) * (h 3 0 - h 1 0) := by
  linear_combination value_121 h H + ((29624035164323443 : ℝ) / 19645476759162664) * (scales0 h H) + ((-17457042264366243 : ℝ) / 39290953518325328) * (scales1 h H)

theorem homothetic_122 (h : Assignment) (H : Constraints h) :
    h 30 2 = h 1 2 + ((7703724177912473 : ℝ) / 9822738379581332) * (h 3 0 - h 1 0) := by
  linear_combination value_122 h H + ((9145265966661627 : ℝ) / 4911369189790666) * (scales0 h H) + ((-6176495980395327 : ℝ) / 9822738379581332) * (scales1 h H)

theorem homothetic_123 (h : Assignment) (H : Constraints h) :
    h 30 3 = h 1 3 + ((575124699546366 : ℝ) / 2455684594895333) * (h 3 0 - h 1 0) := by
  linear_combination value_123 h H + ((-108824997255192 : ℝ) / 2455684594895333) * (scales0 h H) + ((95192236161132 : ℝ) / 2455684594895333) * (scales1 h H)

theorem homothetic_124 (h : Assignment) (H : Constraints h) :
    h 31 0 = h 1 0 + ((780582375658 : ℝ) / 1254921567319) * (h 3 0 - h 1 0) := by
  linear_combination value_124 h H + ((-435443377944798 : ℝ) / 144315980241685) * (scales0 h H) + ((380894370903783 : ℝ) / 144315980241685) * (scales1 h H)

theorem homothetic_125 (h : Assignment) (H : Constraints h) :
    h 31 1 = h 1 1 + ((588086130579 : ℝ) / 717098038468) * (h 3 0 - h 1 0) := by
  linear_combination value_125 h H + ((-17983328509141 : ℝ) / 41233137211910) * (scales0 h H) + ((103596562034867 : ℝ) / 82466274423820) * (scales1 h H)

theorem homothetic_126 (h : Assignment) (H : Constraints h) :
    h 31 2 = h 1 2 + ((163728347711 : ℝ) / 179274509617) * (h 3 0 - h 1 0) := by
  linear_combination value_126 h H + ((-14271376629708 : ℝ) / 20616568605955) * (scales0 h H) + ((33100136616473 : ℝ) / 20616568605955) * (scales1 h H)

theorem homothetic_127 (h : Assignment) (H : Constraints h) :
    h 31 3 = h 1 3 + ((29636437161 : ℝ) / 179274509617) * (h 3 0 - h 1 0) := by
  linear_combination value_127 h H + ((27206249313798 : ℝ) / 20616568605955) * (scales0 h H) + ((-23798059040283 : ℝ) / 20616568605955) * (scales1 h H)

theorem homothetic_128 (h : Assignment) (H : Constraints h) :
    h 32 0 = h 1 0 + ((37924673351107660395524 : ℝ) / 80135970582803502418019) * (h 3 0 - h 1 0) := by
  linear_combination value_128 h H + ((1984243624967293010630333118 : ℝ) / 672741473042635402799269505) * (scales0 h H) + ((-366881573866853714432956137 : ℝ) / 156665822489380847227227145) * (scales1 h H)

theorem homothetic_129 (h : Assignment) (H : Constraints h) :
    h 32 1 = h 1 1 + ((22977346258318728988718983 : ℝ) / 43593967997045105315402336) * (h 3 0 - h 1 0) := by
  linear_combination value_129 h H + ((-128334351448113932233494742221 : ℝ) / 182985680667596829561401305360) * (scales0 h H) + ((86072801708468017563560514833 : ℝ) / 85226207434223180891611566880) * (scales1 h H)

theorem homothetic_130 (h : Assignment) (H : Constraints h) :
    h 32 2 = h 1 2 + ((252036929976259488883767 : ℝ) / 320543882331214009672076) * (h 3 0 - h 1 0) := by
  linear_combination value_130 h H + ((2092699072455672553385462919 : ℝ) / 1345482946085270805598539010) * (scales0 h H) + ((-239109547304040989142325067 : ℝ) / 626663289957523388908908580) * (scales1 h H)

theorem homothetic_131 (h : Assignment) (H : Constraints h) :
    h 32 3 = h 1 3 + ((19011358777051563159879 : ℝ) / 80135970582803502418019) * (h 3 0 - h 1 0) := by
  linear_combination value_131 h H + ((-141879948728109196051564326 : ℝ) / 672741473042635402799269505) * (scales0 h H) + ((1622753227103486375895987 : ℝ) / 9215636617022402778072185) * (scales1 h H)

theorem homothetic_132 (h : Assignment) (H : Constraints h) :
    h 33 0 = h 1 0 + ((2047002871184314068251267 : ℝ) / 4353150459615128109773067) * (h 3 0 - h 1 0) := by
  linear_combination value_132 h H + ((1964305101213638443870359895770 : ℝ) / 348392788634071137924061355833) * (scales0 h H) + ((-16975711837127100659582949221 : ℝ) / 3904775962274769914466441099) * (scales1 h H)

theorem homothetic_133 (h : Assignment) (H : Constraints h) :
    h 33 1 = h 1 1 + ((12242802616029478209018187 : ℝ) / 23216802451280683252123024) * (h 3 0 - h 1 0) := by
  linear_combination value_133 h H + ((-25723007555725338834837341160387 : ℝ) / 27871423090725691033924908466640) * (scales0 h H) + ((4160667383113056795758699869223 : ℝ) / 3540330205795791389116239929760) * (scales1 h H)

theorem homothetic_134 (h : Assignment) (H : Constraints h) :
    h 33 2 = h 1 2 + ((6771655532286104264962343 : ℝ) / 8706300919230256219546134) * (h 3 0 - h 1 0) := by
  linear_combination value_134 h H + ((31762477745279768535251075617161 : ℝ) / 3483927886340711379240613558330) * (scales0 h H) + ((-470291010651928374929096394551 : ℝ) / 78095519245495398289328821980) * (scales1 h H)

theorem homothetic_135 (h : Assignment) (H : Constraints h) :
    h 33 3 = h 1 3 + ((344918463589651164188249 : ℝ) / 1451050153205042703257689) * (h 3 0 - h 1 0) := by
  linear_combination value_135 h H + ((-1086975051893597234230446355038 : ℝ) / 1741963943170355689620306779165) * (scales0 h H) + ((3151362603300167409011141063 : ℝ) / 6507959937124616524110735165) * (scales1 h H)

theorem homothetic_136 (h : Assignment) (H : Constraints h) :
    h 34 0 = h 1 0 + ((17999741293728835263788678 : ℝ) / 37789298968306411348967583) * (h 3 0 - h 1 0) := by
  linear_combination value_136 h H + ((101071459026990958765575291254 : ℝ) / 458237238100680022507730796745) * (scales0 h H) + ((-51895347364531141739643630871 : ℝ) / 169485005872854254900119609755) * (scales1 h H)

theorem homothetic_137 (h : Assignment) (H : Constraints h) :
    h 34 1 = h 1 1 + ((26549542442343632698252807 : ℝ) / 50385731957741881798623444) * (h 3 0 - h 1 0) := by
  linear_combination value_137 h H + ((-45755861090415787045857375231177 : ℝ) / 80649753905719683961360620227120) * (scales0 h H) + ((27966703486858654046268158158399 : ℝ) / 30733281064944238221888355902240) * (scales1 h H)

theorem homothetic_138 (h : Assignment) (H : Constraints h) :
    h 34 2 = h 1 2 + ((59446036744140026258008847 : ℝ) / 75578597936612822697935166) * (h 3 0 - h 1 0) := by
  linear_combination value_138 h H + ((13283879343489716995631629035751 : ℝ) / 10081219238214960495170077528390) * (scales0 h H) + ((-138486319455277622586403713803 : ℝ) / 677940023491417019600478439020) * (scales1 h H)

theorem homothetic_139 (h : Assignment) (H : Constraints h) :
    h 34 3 = h 1 3 + ((2986002101697047462905541 : ℝ) / 12596432989435470449655861) * (h 3 0 - h 1 0) := by
  linear_combination value_139 h H + ((-44404666411918119634893459450 : ℝ) / 1008121923821496049517007752839) * (scales0 h H) + ((583319456784811150219555663 : ℝ) / 11299000391523616993341307317) * (scales1 h H)

theorem homothetic_140 (h : Assignment) (H : Constraints h) :
    h 35 0 = h 1 0 + ((98325468546266864931701 : ℝ) / 205888361993277578641021) * (h 3 0 - h 1 0) := by
  linear_combination value_140 h H + ((-220271233488555718042254873846 : ℝ) / 247165890247499833994866095185) * (scales0 h H) + ((483042981283910047794284161 : ℝ) / 923409303539849940204979185) * (scales1 h H)

theorem homothetic_141 (h : Assignment) (H : Constraints h) :
    h 35 1 = h 1 1 + ((12156889629218154062180811 : ℝ) / 23059496543247088807794352) * (h 3 0 - h 1 0) := by
  linear_combination value_141 h H + ((-22382570556429732277216213515633 : ℝ) / 27682579707719981407425002660720) * (scales0 h H) + ((3832477161397923488018079703357 : ℝ) / 3516342627879748572300560736480) * (scales1 h H)

theorem homothetic_142 (h : Assignment) (H : Constraints h) :
    h 35 2 = h 1 2 + ((2249625401621580903991093 : ℝ) / 2882437067905886100974294) * (h 3 0 - h 1 0) := by
  linear_combination value_142 h H + ((23314774412723819810537136333987 : ℝ) / 3460322463464997675928125332590) * (scales0 h H) + ((-109816415891037746398177695199 : ℝ) / 25855460499115798325739417180) * (scales1 h H)

theorem homothetic_143 (h : Assignment) (H : Constraints h) :
    h 35 3 = h 1 3 + ((341832949651977221202207 : ℝ) / 1441218533952943050487147) * (h 3 0 - h 1 0) := by
  linear_combination value_143 h H + ((-55881888235985827100922492258 : ℝ) / 346032246346499767592812533259) * (scales0 h H) + ((59999240782588592547411283 : ℝ) / 430924341651929972095656953) * (scales1 h H)

theorem homothetic_144 (h : Assignment) (H : Constraints h) :
    h 36 0 = h 1 0 + ((37924673351107660395524 : ℝ) / 80135970582803502418019) * (h 3 0 - h 1 0) := by
  linear_combination value_144 h H + ((1984243624967293010630333118 : ℝ) / 672741473042635402799269505) * (scales0 h H) + ((-366881573866853714432956137 : ℝ) / 156665822489380847227227145) * (scales1 h H)

theorem homothetic_145 (h : Assignment) (H : Constraints h) :
    h 36 1 = h 1 1 + ((23261555189186827128125343 : ℝ) / 43593967997045105315402336) * (h 3 0 - h 1 0) := by
  linear_combination value_145 h H + ((142897503207460818934830522091 : ℝ) / 182985680667596829561401305360) * (scales0 h H) + ((-13602766033558799983759603543 : ℝ) / 85226207434223180891611566880) * (scales1 h H)

theorem homothetic_146 (h : Assignment) (H : Constraints h) :
    h 36 2 = h 1 2 + ((252036929976259488883767 : ℝ) / 320543882331214009672076) * (h 3 0 - h 1 0) := by
  linear_combination value_146 h H + ((2092699072455672553385462919 : ℝ) / 1345482946085270805598539010) * (scales0 h H) + ((-239109547304040989142325067 : ℝ) / 626663289957523388908908580) * (scales1 h H)

theorem homothetic_147 (h : Assignment) (H : Constraints h) :
    h 36 3 = h 1 3 + ((19011358777051563159879 : ℝ) / 80135970582803502418019) * (h 3 0 - h 1 0) := by
  linear_combination value_147 h H + ((-141879948728109196051564326 : ℝ) / 672741473042635402799269505) * (scales0 h H) + ((1622753227103486375895987 : ℝ) / 9215636617022402778072185) * (scales1 h H)

theorem homothetic_148 (h : Assignment) (H : Constraints h) :
    h 37 0 = h 1 0 + ((2047002871184314068251267 : ℝ) / 4353150459615128109773067) * (h 3 0 - h 1 0) := by
  linear_combination value_148 h H + ((1964305101213638443870359895770 : ℝ) / 348392788634071137924061355833) * (scales0 h H) + ((-16975711837127100659582949221 : ℝ) / 3904775962274769914466441099) * (scales1 h H)

theorem homothetic_149 (h : Assignment) (H : Constraints h) :
    h 37 1 = h 1 1 + ((12402523337509070551825067 : ℝ) / 23216802451280683252123024) * (h 3 0 - h 1 0) := by
  linear_combination value_149 h H + ((6652508824964705013858403487333 : ℝ) / 27871423090725691033924908466640) * (scales0 h H) + ((866914767777074946709400332943 : ℝ) / 3540330205795791389116239929760) * (scales1 h H)

theorem homothetic_150 (h : Assignment) (H : Constraints h) :
    h 37 2 = h 1 2 + ((6771655532286104264962343 : ℝ) / 8706300919230256219546134) * (h 3 0 - h 1 0) := by
  linear_combination value_150 h H + ((31762477745279768535251075617161 : ℝ) / 3483927886340711379240613558330) * (scales0 h H) + ((-470291010651928374929096394551 : ℝ) / 78095519245495398289328821980) * (scales1 h H)

theorem homothetic_151 (h : Assignment) (H : Constraints h) :
    h 37 3 = h 1 3 + ((344918463589651164188249 : ℝ) / 1451050153205042703257689) * (h 3 0 - h 1 0) := by
  linear_combination value_151 h H + ((-1086975051893597234230446355038 : ℝ) / 1741963943170355689620306779165) * (scales0 h H) + ((3151362603300167409011141063 : ℝ) / 6507959937124616524110735165) * (scales1 h H)

theorem homothetic_152 (h : Assignment) (H : Constraints h) :
    h 38 0 = h 1 0 + ((17999741293728835263788678 : ℝ) / 37789298968306411348967583) * (h 3 0 - h 1 0) := by
  linear_combination value_152 h H + ((101071459026990958765575291254 : ℝ) / 458237238100680022507730796745) * (scales0 h H) + ((-51895347364531141739643630871 : ℝ) / 169485005872854254900119609755) * (scales1 h H)

theorem homothetic_153 (h : Assignment) (H : Constraints h) :
    h 38 1 = h 1 1 + ((6722163842805085176374758 : ℝ) / 12596432989435470449655861) * (h 3 0 - h 1 0) := by
  linear_combination value_153 h H + ((58642307420003998916173317639071 : ℝ) / 80649753905719683961360620227120) * (scales0 h H) + ((-3671927105646530133536206652777 : ℝ) / 30733281064944238221888355902240) * (scales1 h H)

theorem homothetic_154 (h : Assignment) (H : Constraints h) :
    h 38 2 = h 1 2 + ((59446036744140026258008847 : ℝ) / 75578597936612822697935166) * (h 3 0 - h 1 0) := by
  linear_combination value_154 h H + ((13283879343489716995631629035751 : ℝ) / 10081219238214960495170077528390) * (scales0 h H) + ((-138486319455277622586403713803 : ℝ) / 677940023491417019600478439020) * (scales1 h H)

theorem homothetic_155 (h : Assignment) (H : Constraints h) :
    h 38 3 = h 1 3 + ((2986002101697047462905541 : ℝ) / 12596432989435470449655861) * (h 3 0 - h 1 0) := by
  linear_combination value_155 h H + ((-44404666411918119634893459450 : ℝ) / 1008121923821496049517007752839) * (scales0 h H) + ((583319456784811150219555663 : ℝ) / 11299000391523616993341307317) * (scales1 h H)

theorem homothetic_156 (h : Assignment) (H : Constraints h) :
    h 39 0 = h 1 0 + ((98325468546266864931701 : ℝ) / 205888361993277578641021) * (h 3 0 - h 1 0) := by
  linear_combination value_156 h H + ((-220271233488555718042254873846 : ℝ) / 247165890247499833994866095185) * (scales0 h H) + ((483042981283910047794284161 : ℝ) / 923409303539849940204979185) * (scales1 h H)

theorem homothetic_157 (h : Assignment) (H : Constraints h) :
    h 39 1 = h 1 1 + ((12316610350697746404987691 : ℝ) / 23059496543247088807794352) * (h 3 0 - h 1 0) := by
  linear_combination value_157 h H + ((8616662827913348872128545373959 : ℝ) / 27682579707719981407425002660720) * (scales0 h H) + ((670662280877636424841122383989 : ℝ) / 3516342627879748572300560736480) * (scales1 h H)

theorem homothetic_158 (h : Assignment) (H : Constraints h) :
    h 39 2 = h 1 2 + ((2249625401621580903991093 : ℝ) / 2882437067905886100974294) * (h 3 0 - h 1 0) := by
  linear_combination value_158 h H + ((23314774412723819810537136333987 : ℝ) / 3460322463464997675928125332590) * (scales0 h H) + ((-109816415891037746398177695199 : ℝ) / 25855460499115798325739417180) * (scales1 h H)

theorem homothetic_159 (h : Assignment) (H : Constraints h) :
    h 39 3 = h 1 3 + ((341832949651977221202207 : ℝ) / 1441218533952943050487147) * (h 3 0 - h 1 0) := by
  linear_combination value_159 h H + ((-55881888235985827100922492258 : ℝ) / 346032246346499767592812533259) * (scales0 h H) + ((59999240782588592547411283 : ℝ) / 430924341651929972095656953) * (scales1 h H)

theorem homothetic_160 (h : Assignment) (H : Constraints h) :
    h 40 0 = h 1 0 + ((330874999755796998347 : ℝ) / 704418962202810426877) * (h 3 0 - h 1 0) := by
  linear_combination value_160 h H + ((-143533237735706606712 : ℝ) / 81008180653323199090855) * (scales0 h H) + ((125552494446375169052 : ℝ) / 81008180653323199090855) * (scales1 h H)

theorem homothetic_161 (h : Assignment) (H : Constraints h) :
    h 40 1 = h 1 1 + ((11748196884205232413579 : ℝ) / 22541406790489933660064) * (h 3 0 - h 1 0) := by
  linear_combination value_161 h H + ((-7275925541890134021504321 : ℝ) / 1296130890453171185453680) * (scales0 h H) + ((216391415190288059972887769 : ℝ) / 44068450275407820305425120) * (scales1 h H)

theorem homothetic_162 (h : Assignment) (H : Constraints h) :
    h 40 2 = h 1 2 + ((2216361114449715196637 : ℝ) / 2817675848811241707508) * (h 3 0 - h 1 0) := by
  linear_combination value_162 h H + ((58850120629217951428689 : ℝ) / 32403272261329279636342) * (scales0 h H) + ((-38149113135864349218029 : ℝ) / 64806544522658559272684) * (scales1 h H)

theorem homothetic_163 (h : Assignment) (H : Constraints h) :
    h 40 3 = h 1 3 + ((167203354786906476873 : ℝ) / 704418962202810426877) * (h 3 0 - h 1 0) := by
  linear_combination value_163 h H + ((-8661715161776066384874 : ℝ) / 81008180653323199090855) * (scales0 h H) + ((7576641911662506870429 : ℝ) / 81008180653323199090855) * (scales1 h H)

theorem homothetic_164 (h : Assignment) (H : Constraints h) :
    h 41 0 = h 1 0 + ((86609735132826034823 : ℝ) / 191962945012440494507) * (h 3 0 - h 1 0) := by
  linear_combination value_164 h H + ((-25611094310695704965245392 : ℝ) / 7042160637781379540989295) * (scales0 h H) + ((6109836224447014583212136 : ℝ) / 1920589264849467147542535) * (scales1 h H)

theorem homothetic_165 (h : Assignment) (H : Constraints h) :
    h 41 1 = h 1 1 + ((1582787225885989341909 : ℝ) / 3071407120199047912112) * (h 3 0 - h 1 0) := by
  linear_combination value_165 h H + ((-761857510174688672583148287 : ℝ) / 112674570204502072655828720) * (scales0 h H) + ((6179510915861363677618869439 : ℝ) / 1044800560078110128263139040) * (scales1 h H)

theorem homothetic_166 (h : Assignment) (H : Constraints h) :
    h 41 2 = h 1 2 + ((286686793470506661255 : ℝ) / 383925890024880989014) * (h 3 0 - h 1 0) := by
  linear_combination value_166 h H + ((-1099135286985820856325509673 : ℝ) / 183096176582315868065721670) * (scales0 h H) + ((624294667588936491095494213 : ℝ) / 99870641772172291672211820) * (scales1 h H)

theorem homothetic_167 (h : Assignment) (H : Constraints h) :
    h 41 3 = h 1 3 + ((46015588008359398443 : ℝ) / 191962945012440494507) * (h 3 0 - h 1 0) := by
  linear_combination value_167 h H + ((1115771857151937365366838 : ℝ) / 3156830630729583932167615) * (scales0 h H) + ((-88726955960883908139193 : ℝ) / 286984602793598539287965) * (scales1 h H)

theorem homothetic_168 (h : Assignment) (H : Constraints h) :
    h 42 0 = h 1 0 + ((830968579220254654811 : ℝ) / 1735988930597398397265) * (h 3 0 - h 1 0) := by
  linear_combination value_168 h H + ((22006194672091771648456 : ℝ) / 12537697832092321758025) * (scales0 h H) + ((-519734538873226253932652 : ℝ) / 338517841466492687466675) * (scales1 h H)

theorem homothetic_169 (h : Assignment) (H : Constraints h) :
    h 42 1 = h 1 1 + ((14397052723137184347689 : ℝ) / 27775822889558374356240) * (h 3 0 - h 1 0) := by
  linear_combination value_169 h H + ((-13621661665825553968696411 : ℝ) / 2206634818448248629412400) * (scales0 h H) + ((994381301605265439714838003 : ℝ) / 184153705757772021981871200) * (scales1 h H)

theorem homothetic_170 (h : Assignment) (H : Constraints h) :
    h 42 2 = h 1 2 + ((2734596386369016255457 : ℝ) / 3471977861194796794530) * (h 3 0 - h 1 0) := by
  linear_combination value_170 h H + ((12800136748644181407158081 : ℝ) / 6344075103038714809560650) * (scales0 h H) + ((-23821651682201804677921189 : ℝ) / 31143641414917327246934100) * (scales1 h H)

theorem homothetic_171 (h : Assignment) (H : Constraints h) :
    h 42 3 = h 1 3 + ((411046245289316342401 : ℝ) / 1735988930597398397265) * (h 3 0 - h 1 0) := by
  linear_combination value_171 h H + ((-702618985889944829564302 : ℝ) / 3172037551519357404780325) * (scales0 h H) + ((1508564293234293310535119 : ℝ) / 7785910353729331811733525) * (scales1 h H)

theorem homothetic_172 (h : Assignment) (H : Constraints h) :
    h 43 0 = h 1 0 + ((432259550897862671942509 : ℝ) / 889047834128228807904369) * (h 3 0 - h 1 0) := by
  linear_combination value_172 h H + ((110172271200970053940784112 : ℝ) / 34080166974915437636334145) * (scales0 h H) + ((-867336605631166208965192568 : ℝ) / 306721502774238938727007305) * (scales1 h H)

theorem homothetic_173 (h : Assignment) (H : Constraints h) :
    h 43 1 = h 1 1 + ((2438632638476828853507479 : ℝ) / 4741588448683886975489968) * (h 3 0 - h 1 0) := by
  linear_combination value_173 h H + ((-759265773647343449002289253 : ℝ) / 109056534319729400436269264) * (scales0 h H) + ((22581126527363584798105121117 : ℝ) / 3707922166870799614833154976) * (scales1 h H)

theorem homothetic_174 (h : Assignment) (H : Constraints h) :
    h 43 2 = h 1 2 + ((1349016979335012821116111 : ℝ) / 1778095668256457615808738) * (h 3 0 - h 1 0) := by
  linear_combination value_174 h H + ((-3240347762322562893878199039 : ℝ) / 886084341347801378544687770) * (scales0 h H) + ((66969111343182346456631709827 : ℝ) / 15949518144260424813804379860) * (scales1 h H)

theorem homothetic_175 (h : Assignment) (H : Constraints h) :
    h 43 3 = h 1 3 + ((70309348935659297530543 : ℝ) / 296349278042742935968123) * (h 3 0 - h 1 0) := by
  linear_combination value_175 h H + ((-57093268423683249565655886 : ℝ) / 443042170673900689272343885) * (scales0 h H) + ((149823184785024998043208093 : ℝ) / 1329126512021702067817031655) * (scales1 h H)

theorem homothetic_176 (h : Assignment) (H : Constraints h) :
    h 44 0 = h 1 0 + ((330874999755796998347 : ℝ) / 704418962202810426877) * (h 3 0 - h 1 0) := by
  linear_combination value_176 h H + ((-143533237735706606712 : ℝ) / 81008180653323199090855) * (scales0 h H) + ((125552494446375169052 : ℝ) / 81008180653323199090855) * (scales1 h H)

theorem homothetic_177 (h : Assignment) (H : Constraints h) :
    h 44 1 = h 1 1 + ((12145691892412362678483 : ℝ) / 22541406790489933660064) * (h 3 0 - h 1 0) := by
  linear_combination value_177 h H + ((6652957375333667859130279 : ℝ) / 1296130890453171185453680) * (scales0 h H) + ((-159315987679964401072678111 : ℝ) / 44068450275407820305425120) * (scales1 h H)

theorem homothetic_178 (h : Assignment) (H : Constraints h) :
    h 44 2 = h 1 2 + ((2216361114449715196637 : ℝ) / 2817675848811241707508) * (h 3 0 - h 1 0) := by
  linear_combination value_178 h H + ((58850120629217951428689 : ℝ) / 32403272261329279636342) * (scales0 h H) + ((-38149113135864349218029 : ℝ) / 64806544522658559272684) * (scales1 h H)

theorem homothetic_179 (h : Assignment) (H : Constraints h) :
    h 44 3 = h 1 3 + ((167203354786906476873 : ℝ) / 704418962202810426877) * (h 3 0 - h 1 0) := by
  linear_combination value_179 h H + ((-8661715161776066384874 : ℝ) / 81008180653323199090855) * (scales0 h H) + ((7576641911662506870429 : ℝ) / 81008180653323199090855) * (scales1 h H)

theorem homothetic_180 (h : Assignment) (H : Constraints h) :
    h 45 0 = h 1 0 + ((86609735132826034823 : ℝ) / 191962945012440494507) * (h 3 0 - h 1 0) := by
  linear_combination value_180 h H + ((-25611094310695704965245392 : ℝ) / 7042160637781379540989295) * (scales0 h H) + ((6109836224447014583212136 : ℝ) / 1920589264849467147542535) * (scales1 h H)

theorem homothetic_181 (h : Assignment) (H : Constraints h) :
    h 45 1 = h 1 1 + ((1682925609258774509813 : ℝ) / 3071407120199047912112) * (h 3 0 - h 1 0) := by
  linear_combination value_181 h H + ((2027499983276597232863586913 : ℝ) / 292953882531705388905154672) * (scales0 h H) + ((-14069096150486344956551728177 : ℝ) / 2716481456203086333484161504) * (scales1 h H)

theorem homothetic_182 (h : Assignment) (H : Constraints h) :
    h 45 2 = h 1 2 + ((286686793470506661255 : ℝ) / 383925890024880989014) * (h 3 0 - h 1 0) := by
  linear_combination value_182 h H + ((-1099135286985820856325509673 : ℝ) / 183096176582315868065721670) * (scales0 h H) + ((624294667588936491095494213 : ℝ) / 99870641772172291672211820) * (scales1 h H)

theorem homothetic_183 (h : Assignment) (H : Constraints h) :
    h 45 3 = h 1 3 + ((46015588008359398443 : ℝ) / 191962945012440494507) * (h 3 0 - h 1 0) := by
  linear_combination value_183 h H + ((1115771857151937365366838 : ℝ) / 3156830630729583932167615) * (scales0 h H) + ((-88726955960883908139193 : ℝ) / 286984602793598539287965) * (scales1 h H)

theorem homothetic_184 (h : Assignment) (H : Constraints h) :
    h 46 0 = h 1 0 + ((830968579220254654811 : ℝ) / 1735988930597398397265) * (h 3 0 - h 1 0) := by
  linear_combination value_184 h H + ((22006194672091771648456 : ℝ) / 12537697832092321758025) * (scales0 h H) + ((-519734538873226253932652 : ℝ) / 338517841466492687466675) * (scales1 h H)

theorem homothetic_185 (h : Assignment) (H : Constraints h) :
    h 46 1 = h 1 1 + ((1669936793920543509701 : ℝ) / 3086202543284263817360) * (h 3 0 - h 1 0) := by
  linear_combination value_185 h H + ((283211757137194707396627787 : ℝ) / 50752600824309718476485200) * (scales0 h H) + ((-1885502045648956021241156539 : ℝ) / 470615025825417389509226400) * (scales1 h H)

theorem homothetic_186 (h : Assignment) (H : Constraints h) :
    h 46 2 = h 1 2 + ((2734596386369016255457 : ℝ) / 3471977861194796794530) * (h 3 0 - h 1 0) := by
  linear_combination value_186 h H + ((12800136748644181407158081 : ℝ) / 6344075103038714809560650) * (scales0 h H) + ((-23821651682201804677921189 : ℝ) / 31143641414917327246934100) * (scales1 h H)

theorem homothetic_187 (h : Assignment) (H : Constraints h) :
    h 46 3 = h 1 3 + ((411046245289316342401 : ℝ) / 1735988930597398397265) * (h 3 0 - h 1 0) := by
  linear_combination value_187 h H + ((-702618985889944829564302 : ℝ) / 3172037551519357404780325) * (scales0 h H) + ((1508564293234293310535119 : ℝ) / 7785910353729331811733525) * (scales1 h H)

theorem homothetic_188 (h : Assignment) (H : Constraints h) :
    h 47 0 = h 1 0 + ((432259550897862671942509 : ℝ) / 889047834128228807904369) * (h 3 0 - h 1 0) := by
  linear_combination value_188 h H + ((110172271200970053940784112 : ℝ) / 34080166974915437636334145) * (scales0 h H) + ((-867336605631166208965192568 : ℝ) / 306721502774238938727007305) * (scales1 h H)

theorem homothetic_189 (h : Assignment) (H : Constraints h) :
    h 47 1 = h 1 1 + ((2598353359956421196314359 : ℝ) / 4741588448683886975489968) * (h 3 0 - h 1 0) := by
  linear_combination value_189 h H + ((2136610258052710525485324533 : ℝ) / 308203249164452653406847920) * (scales0 h H) + ((-54378178819898928565889508157 : ℝ) / 10478910471591390215832829280) * (scales1 h H)

theorem homothetic_190 (h : Assignment) (H : Constraints h) :
    h 47 2 = h 1 2 + ((1349016979335012821116111 : ℝ) / 1778095668256457615808738) * (h 3 0 - h 1 0) := by
  linear_combination value_190 h H + ((-3240347762322562893878199039 : ℝ) / 886084341347801378544687770) * (scales0 h H) + ((66969111343182346456631709827 : ℝ) / 15949518144260424813804379860) * (scales1 h H)

theorem homothetic_191 (h : Assignment) (H : Constraints h) :
    h 47 3 = h 1 3 + ((70309348935659297530543 : ℝ) / 296349278042742935968123) * (h 3 0 - h 1 0) := by
  linear_combination value_191 h H + ((-57093268423683249565655886 : ℝ) / 443042170673900689272343885) * (scales0 h H) + ((149823184785024998043208093 : ℝ) / 1329126512021702067817031655) * (scales1 h H)

theorem homothetic_192 (h : Assignment) (H : Constraints h) :
    h 48 0 = h 1 0 + ((15520612305655146664685015750 : ℝ) / 32675527555713337775918693611) * (h 3 0 - h 1 0) := by
  linear_combination value_192 h H + ((32673708890913507468542806734 : ℝ) / 32675527555713337775918693611) * (scales0 h H) + ((-25730972583399966856700360524 : ℝ) / 32675527555713337775918693611) * (scales1 h H)

theorem homothetic_193 (h : Assignment) (H : Constraints h) :
    h 48 1 = h 1 1 + ((550094978867967299599421436073 : ℝ) / 1045616881782826808829398195552) * (h 3 0 - h 1 0) := by
  linear_combination value_193 h H + ((208182836301821096045651822331 : ℝ) / 522808440891413404414699097776) * (scales0 h H) + ((69685528373866284575206709495 : ℝ) / 522808440891413404414699097776) * (scales1 h H)

theorem homothetic_194 (h : Assignment) (H : Constraints h) :
    h 48 2 = h 1 2 + ((102710259697434411157310306897 : ℝ) / 130702110222853351103674774444) * (h 3 0 - h 1 0) := by
  linear_combination value_194 h H + ((134213750884978747507484829423 : ℝ) / 65351055111426675551837387222) * (scales0 h H) + ((-50902781445077666501544776093 : ℝ) / 65351055111426675551837387222) * (scales1 h H)

theorem homothetic_195 (h : Assignment) (H : Constraints h) :
    h 48 3 = h 1 3 + ((7749326945362260727376169663 : ℝ) / 32675527555713337775918693611) * (h 3 0 - h 1 0) := by
  linear_combination value_195 h H + ((-4002714589940938903161736386 : ℝ) / 32675527555713337775918693611) * (scales0 h H) + ((3450783330695605018723130577 : ℝ) / 32675527555713337775918693611) * (scales1 h H)

theorem homothetic_196 (h : Assignment) (H : Constraints h) :
    h 49 0 = h 1 0 + ((386933626973084057587048918 : ℝ) / 815579242680225781335639533) * (h 3 0 - h 1 0) := by
  linear_combination value_196 h H + ((2998253794527737665871750838 : ℝ) / 8971371669482483594692034863) * (scales0 h H)

theorem homothetic_197 (h : Assignment) (H : Constraints h) :
    h 49 1 = h 1 1 + ((13732829524213089535259041889 : ℝ) / 26098535765767225002740465056) * (h 3 0 - h 1 0) := by
  linear_combination value_197 h H + ((73333801017703631498498142543 : ℝ) / 143541946711719737515072557808) * (scales0 h H)

theorem homothetic_198 (h : Assignment) (H : Constraints h) :
    h 49 2 = h 1 2 + ((2559485950430847862138819501 : ℝ) / 3262316970720903125342558132) * (h 3 0 - h 1 0) := by
  linear_combination value_198 h H + ((896822506056033586189872729 : ℝ) / 1631158485360451562671279066) * (scales0 h H) + (1 : ℝ) * (scales1 h H)

theorem homothetic_199 (h : Assignment) (H : Constraints h) :
    h 49 3 = h 1 3 + ((193484426833554591124006800 : ℝ) / 815579242680225781335639533) * (h 3 0 - h 1 0) := by
  linear_combination value_199 h H + ((-297994247945526024314667306 : ℝ) / 8971371669482483594692034863) * (scales0 h H)

theorem homothetic_200 (h : Assignment) (H : Constraints h) :
    h 50 0 = h 1 0 + ((246573827856610733773743225345 : ℝ) / 518754931685204875296418551023) * (h 3 0 - h 1 0) := by
  linear_combination value_200 h H + ((-266286651705594267031295217288 : ℝ) / 518754931685204875296418551023) * (scales0 h H) + ((216546615514887264628724421488 : ℝ) / 518754931685204875296418551023) * (scales1 h H)

theorem homothetic_201 (h : Assignment) (H : Constraints h) :
    h 50 1 = h 1 1 + ((4366642872826104676091635747493 : ℝ) / 8300078906963278004742696816368) * (h 3 0 - h 1 0) := by
  linear_combination value_201 h H + ((1644188391755857818182070777339 : ℝ) / 4150039453481639002371348408184) * (scales0 h H) + ((1119638926192710425104328795061 : ℝ) / 8300078906963278004742696816368) * (scales1 h H)

theorem homothetic_202 (h : Assignment) (H : Constraints h) :
    h 50 2 = h 1 2 + ((815352184629613741817890564765 : ℝ) / 1037509863370409750592837102046) * (h 3 0 - h 1 0) := by
  linear_combination value_202 h H + ((970664285983757617368809643177 : ℝ) / 518754931685204875296418551023) * (scales0 h H) + ((-657290740000537986652883523327 : ℝ) / 1037509863370409750592837102046) * (scales1 h H)

theorem homothetic_203 (h : Assignment) (H : Constraints h) :
    h 50 3 = h 1 3 + ((123017280524935410449489547363 : ℝ) / 518754931685204875296418551023) * (h 3 0 - h 1 0) := by
  linear_combination value_203 h H + ((-14335061367662622798576402618 : ℝ) / 518754931685204875296418551023) * (scales0 h H) + ((15600554891686645608115909725 : ℝ) / 518754931685204875296418551023) * (scales1 h H)

theorem homothetic_204 (h : Assignment) (H : Constraints h) :
    h 51 0 = h 1 0 + ((1660479031129104979232793601 : ℝ) / 3491713850758211169491718831) * (h 3 0 - h 1 0) := by
  linear_combination value_204 h H + ((-1073017843950021148530627336 : ℝ) / 8147332318435826062147343939) * (scales0 h H)

theorem homothetic_205 (h : Assignment) (H : Constraints h) :
    h 51 1 = h 1 1 + ((68590219495914303247941647397 : ℝ) / 130357317094973216994357503024) * (h 3 0 - h 1 0) := by
  linear_combination value_205 h H + ((651819120524886273743674901565 : ℝ) / 1254689177039117213570690966606) * (scales0 h H)

theorem homothetic_206 (h : Assignment) (H : Constraints h) :
    h 51 2 = h 1 2 + ((38372687645216636315735202943 : ℝ) / 48883993910614956372884063634) * (h 3 0 - h 1 0) := by
  linear_combination value_206 h H + ((236998667223818854439752680264 : ℝ) / 627344588519558606785345483303) * (scales0 h H) + (1 : ℝ) * (scales1 h H)

theorem homothetic_207 (h : Assignment) (H : Constraints h) :
    h 51 3 = h 1 3 + ((1932189183592177483300578859 : ℝ) / 8147332318435826062147343939) * (h 3 0 - h 1 0) := by
  linear_combination value_207 h H + ((-88425925523875795828590648 : ℝ) / 627344588519558606785345483303) * (scales0 h H)

theorem homothetic_208 (h : Assignment) (H : Constraints h) :
    h 52 0 = h 1 0 + ((34489688017312440758442635101 : ℝ) / 72674441298858640087278575651) * (h 3 0 - h 1 0) := by
  linear_combination value_208 h H + ((72478632673303706561023043496 : ℝ) / 72674441298858640087278575651) * (scales0 h H) + ((-57123224158121650301803519610 : ℝ) / 72674441298858640087278575651) * (scales1 h H)

theorem homothetic_209 (h : Assignment) (H : Constraints h) :
    h 52 1 = h 1 1 + ((310361656748375544205985042169 : ℝ) / 581395530390869120698228605208) * (h 3 0 - h 1 0) := by
  linear_combination value_209 h H + ((130070925129166839427359717251 : ℝ) / 290697765195434560349114302604) * (scales0 h H) + ((30859835989602710605426082479 : ℝ) / 290697765195434560349114302604) * (scales1 h H)

theorem homothetic_210 (h : Assignment) (H : Constraints h) :
    h 52 2 = h 1 2 + ((57117792398369718875735622862 : ℝ) / 72674441298858640087278575651) * (h 3 0 - h 1 0) := by
  linear_combination value_210 h H + ((149303068254927490314397680882 : ℝ) / 72674441298858640087278575651) * (scales0 h H) + ((-56634073205085405255350804018 : ℝ) / 72674441298858640087278575651) * (scales1 h H)

theorem homothetic_211 (h : Assignment) (H : Constraints h) :
    h 52 3 = h 1 3 + ((17236832104620269945525241231 : ℝ) / 72674441298858640087278575651) * (h 3 0 - h 1 0) := by
  linear_combination value_211 h H + ((-8893840324418822981414494530 : ℝ) / 72674441298858640087278575651) * (scales0 h H) + ((7670180634305715487985049609 : ℝ) / 72674441298858640087278575651) * (scales1 h H)

theorem homothetic_212 (h : Assignment) (H : Constraints h) :
    h 53 0 = h 1 0 + ((7498087158674464836866999 : ℝ) / 15858103373848045076594149) * (h 3 0 - h 1 0) := by
  linear_combination value_212 h H + ((57342753996512257668551364 : ℝ) / 174439137112328495842535639) * (scales0 h H)

theorem homothetic_213 (h : Assignment) (H : Constraints h) :
    h 53 1 = h 1 1 + ((9679039782173769529790013 : ℝ) / 18123546712969194373250456) * (h 3 0 - h 1 0) := by
  linear_combination value_213 h H + ((53601752032832795999267723 : ℝ) / 99679506921330569052877508) * (scales0 h H)

theorem homothetic_214 (h : Assignment) (H : Constraints h) :
    h 53 2 = h 1 2 + ((1771507616629943951493344 : ℝ) / 2265443339121149296656307) * (h 3 0 - h 1 0) := by
  linear_combination value_214 h H + ((13480713225851098567607208 : ℝ) / 24919876730332642263219377) * (scales0 h H) + (1 : ℝ) * (scales1 h H)

theorem homothetic_215 (h : Assignment) (H : Constraints h) :
    h 53 3 = h 1 3 + ((3764940308545379251029699 : ℝ) / 15858103373848045076594149) * (h 3 0 - h 1 0) := by
  linear_combination value_215 h H + ((-5687796970335434662811808 : ℝ) / 174439137112328495842535639) * (scales0 h H)

theorem homothetic_216 (h : Assignment) (H : Constraints h) :
    h 54 0 = h 1 0 + ((137140387230205721936245456467 : ℝ) / 288351569402810574529240132192) * (h 3 0 - h 1 0) := by
  linear_combination value_216 h H + ((-73776641543489070940041714339 : ℝ) / 144175784701405287264620066096) * (scales0 h H) + ((120126910384208960708621950915 : ℝ) / 288351569402810574529240132192) * (scales1 h H)

theorem homothetic_217 (h : Assignment) (H : Constraints h) :
    h 54 1 = h 1 1 + ((2462877092205180514685636204021 : ℝ) / 4613625110444969192467842115072) * (h 3 0 - h 1 0) := by
  linear_combination value_217 h H + ((1015175603829028825047716757755 : ℝ) / 2306812555222484596233921057536) * (scales0 h H) + ((516858231467655607560504108645 : ℝ) / 4613625110444969192467842115072) * (scales1 h H)

theorem homothetic_218 (h : Assignment) (H : Constraints h) :
    h 54 2 = h 1 2 + ((226662826025668122197608848679 : ℝ) / 288351569402810574529240132192) * (h 3 0 - h 1 0) := by
  linear_combination value_218 h H + ((269928922810662604454177689353 : ℝ) / 144175784701405287264620066096) * (scales0 h H) + ((-182840609873591744038605265353 : ℝ) / 288351569402810574529240132192) * (scales1 h H)

theorem homothetic_219 (h : Assignment) (H : Constraints h) :
    h 54 3 = h 1 3 + ((17093090215749250446173900913 : ℝ) / 72087892350702643632310033048) * (h 3 0 - h 1 0) := by
  linear_combination value_219 h H + ((-1001121979882274265817398609 : ℝ) / 36043946175351321816155016524) * (scales0 h H) + ((2173216697008202992100235825 : ℝ) / 72087892350702643632310033048) * (scales1 h H)

theorem homothetic_220 (h : Assignment) (H : Constraints h) :
    h 55 0 = h 1 0 + ((15811069717464985005318455 : ℝ) / 33194360854270403463010278) * (h 3 0 - h 1 0) := by
  linear_combination value_220 h H + ((-3579729374400456323214828 : ℝ) / 27661967378558669552508565) * (scales0 h H)

theorem homothetic_221 (h : Assignment) (H : Constraints h) :
    h 55 1 = h 1 1 + ((94541007463441608255985705 : ℝ) / 177036591222775485136054816) * (h 3 0 - h 1 0) := by
  linear_combination value_221 h H + ((660757783908340905703731119 : ℝ) / 1217126564656581460310376860) * (scales0 h H)

theorem homothetic_222 (h : Assignment) (H : Constraints h) :
    h 55 2 = h 1 2 + ((25999589691916191252747115 : ℝ) / 33194360854270403463010278) * (h 3 0 - h 1 0) := by
  linear_combination value_222 h H + ((113391772322661382481049024 : ℝ) / 304281641164145365077594215) * (scales0 h H) + (1 : ℝ) * (scales1 h H)

theorem homothetic_223 (h : Assignment) (H : Constraints h) :
    h 55 3 = h 1 3 + ((1312098045054627791910868 : ℝ) / 5532393475711733910501713) * (h 3 0 - h 1 0) := by
  linear_combination value_223 h H + ((-6696008247861808220880 : ℝ) / 60856328232829073015518843) * (scales0 h H)

theorem homothetic_224 (h : Assignment) (H : Constraints h) :
    h 56 0 = h 1 0 + ((113794235583827978925919 : ℝ) / 240376066713909992395400) * (h 3 0 - h 1 0) := by
  linear_combination value_224 h H + ((3161039314271773420806596667 : ℝ) / 1008978540031637193079691500) * (scales0 h H) + ((-68764358380088094269000213 : ℝ) / 27643247672099649125471000) * (scales1 h H)

theorem homothetic_225 (h : Assignment) (H : Constraints h) :
    h 56 1 = h 1 1 + ((934816436068939411244123 : ℝ) / 1923008533711279939163200) * (h 3 0 - h 1 0) := by
  linear_combination value_225 h H + ((19414839583517363453450513439 : ℝ) / 8071828320253097544637532000) * (scales0 h H) + ((-5738876243940075067449936857 : ℝ) / 3759481683405552281064056000) * (scales1 h H)

theorem homothetic_226 (h : Assignment) (H : Constraints h) :
    h 56 2 = h 1 2 + ((100340131284208498460027 : ℝ) / 120188033356954996197700) * (h 3 0 - h 1 0) := by
  linear_combination value_226 h H + ((-480774751631741289653908389 : ℝ) / 504489270015818596539845750) * (scales0 h H) + ((23367414129755617727949071 : ℝ) / 13821623836049824562735500) * (scales1 h H)

theorem homothetic_227 (h : Assignment) (H : Constraints h) :
    h 56 3 = h 1 3 + ((12759751460028199206351 : ℝ) / 60094016678477498098850) * (h 3 0 - h 1 0) := by
  linear_combination value_227 h H + ((372304208406275240464072143 : ℝ) / 252244635007909298269922875) * (scales0 h H) + ((-8329980296380684811405877 : ℝ) / 6910811918024912281367750) * (scales1 h H)

theorem homothetic_228 (h : Assignment) (H : Constraints h) :
    h 57 0 = h 1 0 + ((22643664462472705843084 : ℝ) / 47944807999223844799935) * (h 3 0 - h 1 0) := by
  linear_combination value_228 h H + ((13393165800162739382713734 : ℝ) / 3990565207333689277185701) * (scales0 h H) + ((-85289296303667014747598497 : ℝ) / 31979186935482304481556645) * (scales1 h H)

theorem homothetic_229 (h : Assignment) (H : Constraints h) :
    h 57 1 = h 1 1 + ((22443927884827818480627 : ℝ) / 42617607110421195377720) * (h 3 0 - h 1 0) := by
  linear_combination value_229 h H + ((-455697671901342475194376641 : ℝ) / 79811304146673785543714020) * (scales0 h H) + ((1206980366386691997475730201 : ℝ) / 241620523512532967193983540) * (scales1 h H)

theorem homothetic_230 (h : Assignment) (H : Constraints h) :
    h 57 2 = h 1 2 + ((37945283165796075729259 : ℝ) / 47944807999223844799935) * (h 3 0 - h 1 0) := by
  linear_combination value_230 h H + ((154529642813639551120678656 : ℝ) / 19952826036668446385928505) * (scales0 h H) + ((-169477047792844912248520321 : ℝ) / 31979186935482304481556645) * (scales1 h H)

theorem homothetic_231 (h : Assignment) (H : Constraints h) :
    h 57 3 = h 1 3 + ((11268276397206178816139 : ℝ) / 47944807999223844799935) * (h 3 0 - h 1 0) := by
  linear_combination value_231 h H + ((-2112356982453003366864414 : ℝ) / 688028484023049875376845) * (scales0 h H) + ((2699812471334852541906743 : ℝ) / 1102730583982148430398505) * (scales1 h H)

theorem homothetic_232 (h : Assignment) (H : Constraints h) :
    h 58 0 = h 1 0 + ((621772335938949344656519 : ℝ) / 1231189400320748122982390) * (h 3 0 - h 1 0) := by
  linear_combination value_232 h H + ((-16537522489458809905008878751 : ℝ) / 5167917507846340246218582025) * (scales0 h H) + ((368427272927502107194965529 : ℝ) / 141586781036886034142974850) * (scales1 h H)

theorem homothetic_233 (h : Assignment) (H : Constraints h) :
    h 58 1 = h 1 1 + ((9630627783411212560211751 : ℝ) / 19699030405131969967718240) * (h 3 0 - h 1 0) := by
  linear_combination value_233 h H + ((153061583650156223807045403051 : ℝ) / 82686680125541443939497312400) * (scales0 h H) + ((-41636451361200205751305460393 : ℝ) / 38511604442033001286889159200) * (scales1 h H)

theorem homothetic_234 (h : Assignment) (H : Constraints h) :
    h 58 2 = h 1 2 + ((1027026933978880855912949 : ℝ) / 1231189400320748122982390) * (h 3 0 - h 1 0) := by
  linear_combination value_234 h H + ((-4215936139788936757521194181 : ℝ) / 5167917507846340246218582025) * (scales0 h H) + ((223760042669872934461308849 : ℝ) / 141586781036886034142974850) * (scales1 h H)

theorem homothetic_235 (h : Assignment) (H : Constraints h) :
    h 58 3 = h 1 3 + ((130961908332148683270212 : ℝ) / 615594700160374061491195) * (h 3 0 - h 1 0) := by
  linear_combination value_235 h H + ((7202570310470526750271528524 : ℝ) / 5167917507846340246218582025) * (scales0 h H) + ((-80651127640777593610839848 : ℝ) / 70793390518443017071487425) * (scales1 h H)

theorem homothetic_236 (h : Assignment) (H : Constraints h) :
    h 59 0 = h 1 0 + ((529787797170143595009788 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0) := by
  linear_combination value_236 h H + ((14822215821356797205531829486 : ℝ) / 9245771035243392164319874225) * (scales0 h H) + ((-159344708955709399123588597 : ℝ) / 126654397743060166634518825) * (scales1 h H)

theorem homothetic_237 (h : Assignment) (H : Constraints h) :
    h 59 1 = h 1 1 + ((578749084305489324838032 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0) := by
  linear_combination value_237 h H + ((-50677467186335059297991218311 : ℝ) / 9245771035243392164319874225) * (scales0 h H) + ((82881235079194589895477500167 : ℝ) / 17224998093056182662294560200) * (scales1 h H)

theorem homothetic_238 (h : Assignment) (H : Constraints h) :
    h 59 2 = h 1 2 + ((874063471235004430739378 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0) := by
  linear_combination value_238 h H + ((67536049194508108851727272846 : ℝ) / 9245771035243392164319874225) * (scales0 h H) + ((-626408573601213946019058142 : ℝ) / 126654397743060166634518825) * (scales1 h H)

theorem homothetic_239 (h : Assignment) (H : Constraints h) :
    h 59 3 = h 1 3 + ((257588362112298345612543 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0) := by
  linear_combination value_239 h H + ((-26274335083844763094555047894 : ℝ) / 9245771035243392164319874225) * (scales0 h H) + ((286839626563733418382593063 : ℝ) / 126654397743060166634518825) * (scales1 h H)

theorem homothetic_240 (h : Assignment) (H : Constraints h) :
    h 60 0 = h 1 0 + ((113794235583827978925919 : ℝ) / 240376066713909992395400) * (h 3 0 - h 1 0) := by
  linear_combination value_240 h H + ((3161039314271773420806596667 : ℝ) / 1008978540031637193079691500) * (scales0 h H) + ((-68764358380088094269000213 : ℝ) / 27643247672099649125471000) * (scales1 h H)

theorem homothetic_241 (h : Assignment) (H : Constraints h) :
    h 60 1 = h 1 1 + ((1076920901502988480947303 : ℝ) / 1923008533711279939163200) * (h 3 0 - h 1 0) := by
  linear_combination value_241 h H + ((-10500665848274917354430148421 : ℝ) / 8071828320253097544637532000) * (scales0 h H) + ((5784129614890699131802604323 : ℝ) / 3759481683405552281064056000) * (scales1 h H)

theorem homothetic_242 (h : Assignment) (H : Constraints h) :
    h 60 2 = h 1 2 + ((100340131284208498460027 : ℝ) / 120188033356954996197700) * (h 3 0 - h 1 0) := by
  linear_combination value_242 h H + ((-480774751631741289653908389 : ℝ) / 504489270015818596539845750) * (scales0 h H) + ((23367414129755617727949071 : ℝ) / 13821623836049824562735500) * (scales1 h H)

theorem homothetic_243 (h : Assignment) (H : Constraints h) :
    h 60 3 = h 1 3 + ((12759751460028199206351 : ℝ) / 60094016678477498098850) * (h 3 0 - h 1 0) := by
  linear_combination value_243 h H + ((372304208406275240464072143 : ℝ) / 252244635007909298269922875) * (scales0 h H) + ((-8329980296380684811405877 : ℝ) / 6910811918024912281367750) * (scales1 h H)

theorem homothetic_244 (h : Assignment) (H : Constraints h) :
    h 61 0 = h 1 0 + ((22643664462472705843084 : ℝ) / 47944807999223844799935) * (h 3 0 - h 1 0) := by
  linear_combination value_244 h H + ((13393165800162739382713734 : ℝ) / 3990565207333689277185701) * (scales0 h H) + ((-85289296303667014747598497 : ℝ) / 31979186935482304481556645) * (scales1 h H)

theorem homothetic_245 (h : Assignment) (H : Constraints h) :
    h 61 1 = h 1 1 + ((204749156506201958443003 : ℝ) / 383558463993790758399480) * (h 3 0 - h 1 0) := by
  linear_combination value_245 h H + ((315083883405342297140896639 : ℝ) / 79811304146673785543714020) * (scales0 h H) + ((-5827470807254752012871525461 : ℝ) / 2174584711612796704745851860) * (scales1 h H)

theorem homothetic_246 (h : Assignment) (H : Constraints h) :
    h 61 2 = h 1 2 + ((37945283165796075729259 : ℝ) / 47944807999223844799935) * (h 3 0 - h 1 0) := by
  linear_combination value_246 h H + ((154529642813639551120678656 : ℝ) / 19952826036668446385928505) * (scales0 h H) + ((-169477047792844912248520321 : ℝ) / 31979186935482304481556645) * (scales1 h H)

theorem homothetic_247 (h : Assignment) (H : Constraints h) :
    h 61 3 = h 1 3 + ((11268276397206178816139 : ℝ) / 47944807999223844799935) * (h 3 0 - h 1 0) := by
  linear_combination value_247 h H + ((-2112356982453003366864414 : ℝ) / 688028484023049875376845) * (scales0 h H) + ((2699812471334852541906743 : ℝ) / 1102730583982148430398505) * (scales1 h H)

theorem homothetic_248 (h : Assignment) (H : Constraints h) :
    h 62 0 = h 1 0 + ((621772335938949344656519 : ℝ) / 1231189400320748122982390) * (h 3 0 - h 1 0) := by
  linear_combination value_248 h H + ((-16537522489458809905008878751 : ℝ) / 5167917507846340246218582025) * (scales0 h H) + ((368427272927502107194965529 : ℝ) / 141586781036886034142974850) * (scales1 h H)

theorem homothetic_249 (h : Assignment) (H : Constraints h) :
    h 62 1 = h 1 1 + ((10987079498918044589196651 : ℝ) / 19699030405131969967718240) * (h 3 0 - h 1 0) := by
  linear_combination value_249 h H + ((-69944775396722900818180883489 : ℝ) / 82686680125541443939497312400) * (scales0 h H) + ((45168965696159126417226512027 : ℝ) / 38511604442033001286889159200) * (scales1 h H)

theorem homothetic_250 (h : Assignment) (H : Constraints h) :
    h 62 2 = h 1 2 + ((1027026933978880855912949 : ℝ) / 1231189400320748122982390) * (h 3 0 - h 1 0) := by
  linear_combination value_250 h H + ((-4215936139788936757521194181 : ℝ) / 5167917507846340246218582025) * (scales0 h H) + ((223760042669872934461308849 : ℝ) / 141586781036886034142974850) * (scales1 h H)

theorem homothetic_251 (h : Assignment) (H : Constraints h) :
    h 62 3 = h 1 3 + ((130961908332148683270212 : ℝ) / 615594700160374061491195) * (h 3 0 - h 1 0) := by
  linear_combination value_251 h H + ((7202570310470526750271528524 : ℝ) / 5167917507846340246218582025) * (scales0 h H) + ((-80651127640777593610839848 : ℝ) / 70793390518443017071487425) * (scales1 h H)

theorem homothetic_252 (h : Assignment) (H : Constraints h) :
    h 63 0 = h 1 0 + ((529787797170143595009788 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0) := by
  linear_combination value_252 h H + ((14822215821356797205531829486 : ℝ) / 9245771035243392164319874225) * (scales0 h H) + ((-159344708955709399123588597 : ℝ) / 126654397743060166634518825) * (scales1 h H)

theorem homothetic_253 (h : Assignment) (H : Constraints h) :
    h 63 1 = h 1 1 + ((588731629397963846263462 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0) := by
  linear_combination value_253 h H + ((35124268474128805285885696009 : ℝ) / 9245771035243392164319874225) * (scales0 h H) + ((-44098331053156324319269247573 : ℝ) / 17224998093056182662294560200) * (scales1 h H)

theorem homothetic_254 (h : Assignment) (H : Constraints h) :
    h 63 2 = h 1 2 + ((874063471235004430739378 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0) := by
  linear_combination value_254 h H + ((67536049194508108851727272846 : ℝ) / 9245771035243392164319874225) * (scales0 h H) + ((-626408573601213946019058142 : ℝ) / 126654397743060166634518825) * (scales1 h H)

theorem homothetic_255 (h : Assignment) (H : Constraints h) :
    h 63 3 = h 1 3 + ((257588362112298345612543 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0) := by
  linear_combination value_255 h H + ((-26274335083844763094555047894 : ℝ) / 9245771035243392164319874225) * (scales0 h H) + ((286839626563733418382593063 : ℝ) / 126654397743060166634518825) * (scales1 h H)

theorem homothetic_256 (h : Assignment) (H : Constraints h) :
    h 64 0 = h 1 0 + ((1751923035161058628064 : ℝ) / 3726409371667389204473) * (h 3 0 - h 1 0) := by
  linear_combination value_256 h H + ((-291719362271465515182138 : ℝ) / 28711984208697233820464465) * (scales0 h H) + ((255174997716761229511173 : ℝ) / 28711984208697233820464465) * (scales1 h H)

theorem homothetic_257 (h : Assignment) (H : Constraints h) :
    h 64 1 = h 1 1 + ((15699441442694853759603 : ℝ) / 29811274973339113635784) * (h 3 0 - h 1 0) := by
  linear_combination value_257 h H + ((-657088095247999863383620611 : ℝ) / 114847936834788935281857860) * (scales0 h H) + ((19542286684597921862853605579 : ℝ) / 3904829852382823799583167240) * (scales1 h H)

theorem homothetic_258 (h : Assignment) (H : Constraints h) :
    h 64 2 = h 1 2 + ((2935064701642600779897 : ℝ) / 3726409371667389204473) * (h 3 0 - h 1 0) := by
  linear_combination value_258 h H + ((10310189948343925385992056 : ℝ) / 5742396841739446764092893) * (scales0 h H) + ((-3276211577127843088795583 : ℝ) / 5742396841739446764092893) * (scales1 h H)

theorem homothetic_259 (h : Assignment) (H : Constraints h) :
    h 64 3 = h 1 3 + ((882872984694381404469 : ℝ) / 3726409371667389204473) * (h 3 0 - h 1 0) := by
  linear_combination value_259 h H + ((-42085322381761110668898 : ℝ) / 428537077741749758514395) * (scales0 h H) + ((36813195939601494408633 : ℝ) / 428537077741749758514395) * (scales1 h H)

theorem homothetic_260 (h : Assignment) (H : Constraints h) :
    h 65 0 = h 1 0 + ((20000684545103902867904 : ℝ) / 41708273765268360426865) * (h 3 0 - h 1 0) := by
  linear_combination value_260 h H + ((-941473835656930474758414 : ℝ) / 4796451483005861449089475) * (scales0 h H) + ((823533213543044848835519 : ℝ) / 4796451483005861449089475) * (scales1 h H)

theorem homothetic_261 (h : Assignment) (H : Constraints h) :
    h 65 1 = h 1 1 + ((87640008256665869233209 : ℝ) / 166833095061073441707460) * (h 3 0 - h 1 0) := by
  linear_combination value_261 h H + ((-54635370603528972226547007 : ℝ) / 9592902966011722898178950) * (scales0 h H) + ((1624896392393843136959898023 : ℝ) / 326158700844398578538084300) * (scales1 h H)

theorem homothetic_262 (h : Assignment) (H : Constraints h) :
    h 65 2 = h 1 2 + ((756896934477189495856362 : ℝ) / 959290296601172289817895) * (h 3 0 - h 1 0) := by
  linear_combination value_262 h H + ((195059622242413808686096038 : ℝ) / 110318384109134813329057925) * (scales0 h H) + ((-60305664540819749170871398 : ℝ) / 110318384109134813329057925) * (scales1 h H)

theorem homothetic_263 (h : Assignment) (H : Constraints h) :
    h 65 3 = h 1 3 + ((226570796465936930441627 : ℝ) / 959290296601172289817895) * (h 3 0 - h 1 0) := by
  linear_combination value_263 h H + ((-9223400505893096429721342 : ℝ) / 110318384109134813329057925) * (scales0 h H) + ((8067963623346575635148407 : ℝ) / 110318384109134813329057925) * (scales1 h H)

theorem homothetic_264 (h : Assignment) (H : Constraints h) :
    h 66 0 = h 1 0 + ((1751923035161058628064 : ℝ) / 3726409371667389204473) * (h 3 0 - h 1 0) := by
  linear_combination value_264 h H + ((-291719362271465515182138 : ℝ) / 28711984208697233820464465) * (scales0 h H) + ((255174997716761229511173 : ℝ) / 28711984208697233820464465) * (scales1 h H)

theorem homothetic_265 (h : Assignment) (H : Constraints h) :
    h 66 1 = h 1 1 + ((15937830579231558748867 : ℝ) / 29811274973339113635784) * (h 3 0 - h 1 0) := by
  linear_combination value_265 h H + ((8940910464732447581878847 : ℝ) / 1714148310966999034057580) * (scales0 h H) + ((-214929259610135377181499163 : ℝ) / 58281042572877967157957720) * (scales1 h H)

theorem homothetic_266 (h : Assignment) (H : Constraints h) :
    h 66 2 = h 1 2 + ((2935064701642600779897 : ℝ) / 3726409371667389204473) * (h 3 0 - h 1 0) := by
  linear_combination value_266 h H + ((10310189948343925385992056 : ℝ) / 5742396841739446764092893) * (scales0 h H) + ((-3276211577127843088795583 : ℝ) / 5742396841739446764092893) * (scales1 h H)

theorem homothetic_267 (h : Assignment) (H : Constraints h) :
    h 66 3 = h 1 3 + ((882872984694381404469 : ℝ) / 3726409371667389204473) * (h 3 0 - h 1 0) := by
  linear_combination value_267 h H + ((-42085322381761110668898 : ℝ) / 428537077741749758514395) * (scales0 h H) + ((36813195939601494408633 : ℝ) / 428537077741749758514395) * (scales1 h H)

theorem homothetic_268 (h : Assignment) (H : Constraints h) :
    h 67 0 = h 1 0 + ((20000684545103902867904 : ℝ) / 41708273765268360426865) * (h 3 0 - h 1 0) := by
  linear_combination value_268 h H + ((-941473835656930474758414 : ℝ) / 4796451483005861449089475) * (scales0 h H) + ((823533213543044848835519 : ℝ) / 4796451483005861449089475) * (scales1 h H)

theorem homothetic_269 (h : Assignment) (H : Constraints h) :
    h 67 1 = h 1 1 + ((2055650370273213078065527 : ℝ) / 3837161186404689159271580) * (h 3 0 - h 1 0) := by
  linear_combination value_269 h H + ((1146036153981825572140388119 : ℝ) / 220636768218269626658115850) * (scales0 h H) + ((-27522063213634645341565356741 : ℝ) / 7501650119421167306375938900) * (scales1 h H)

theorem homothetic_270 (h : Assignment) (H : Constraints h) :
    h 67 2 = h 1 2 + ((756896934477189495856362 : ℝ) / 959290296601172289817895) * (h 3 0 - h 1 0) := by
  linear_combination value_270 h H + ((195059622242413808686096038 : ℝ) / 110318384109134813329057925) * (scales0 h H) + ((-60305664540819749170871398 : ℝ) / 110318384109134813329057925) * (scales1 h H)

theorem homothetic_271 (h : Assignment) (H : Constraints h) :
    h 67 3 = h 1 3 + ((226570796465936930441627 : ℝ) / 959290296601172289817895) * (h 3 0 - h 1 0) := by
  linear_combination value_271 h H + ((-9223400505893096429721342 : ℝ) / 110318384109134813329057925) * (scales0 h H) + ((8067963623346575635148407 : ℝ) / 110318384109134813329057925) * (scales1 h H)

theorem homothetic_272 (h : Assignment) (H : Constraints h) :
    h 68 0 = h 1 0 + ((4938288334848929488318654189 : ℝ) / 10169278224994740028343429276) * (h 3 0 - h 1 0) := by
  linear_combination value_272 h H + ((5428426250568344182008510411 : ℝ) / 5084639112497370014171714638) * (scales0 h H) + ((-4193580421215274133070474349 : ℝ) / 5084639112497370014171714638) * (scales1 h H)

theorem homothetic_273 (h : Assignment) (H : Constraints h) :
    h 68 1 = h 1 1 + ((40596238269230557822406629745 : ℝ) / 81354225799957920226747434208) * (h 3 0 - h 1 0) := by
  linear_combination value_273 h H + ((9173994634686174881142454227 : ℝ) / 40677112899978960113373717104) * (scales0 h H) + ((9291944721704916188588246191 : ℝ) / 40677112899978960113373717104) * (scales1 h H)

theorem homothetic_274 (h : Assignment) (H : Constraints h) :
    h 68 2 = h 1 2 + ((4148824248022565979793367417 : ℝ) / 5084639112497370014171714638) * (h 3 0 - h 1 0) := by
  linear_combination value_274 h H + ((5709290239179495222494681169 : ℝ) / 2542319556248685007085857319) * (scales0 h H) + ((-2249156636753811471869694935 : ℝ) / 2542319556248685007085857319) * (scales1 h H)

theorem homothetic_275 (h : Assignment) (H : Constraints h) :
    h 68 3 = h 1 3 + ((565250632961968976317651050 : ℝ) / 2542319556248685007085857319) * (h 3 0 - h 1 0) := by
  linear_combination value_275 h H + ((-551634595776523028599468848 : ℝ) / 2542319556248685007085857319) * (scales0 h H) + ((400840909230863343986102535 : ℝ) / 2542319556248685007085857319) * (scales1 h H)

theorem homothetic_276 (h : Assignment) (H : Constraints h) :
    h 69 0 = h 1 0 + ((222615224668037268577921484 : ℝ) / 464647896163676837925749215) * (h 3 0 - h 1 0) := by
  linear_combination value_276 h H + ((2658624247514620828316061234 : ℝ) / 464647896163676837925749215) * (scales0 h H) + ((-421820523190100863556743991 : ℝ) / 92929579232735367585149843) * (scales1 h H)

theorem homothetic_277 (h : Assignment) (H : Constraints h) :
    h 69 1 = h 1 1 + ((3818379522142608901893272387 : ℝ) / 7434366338618829406811987440) * (h 3 0 - h 1 0) := by
  linear_combination value_277 h H + ((-38017423363876502189231092239 : ℝ) / 3717183169309414703405993720) * (scales0 h H) + ((796472063505222428400640036 : ℝ) / 92929579232735367585149843) * (scales1 h H)

theorem homothetic_278 (h : Assignment) (H : Constraints h) :
    h 69 2 = h 1 2 + ((149202793612884591943313675 : ℝ) / 185859158465470735170299686) * (h 3 0 - h 1 0) := by
  linear_combination value_278 h H + ((1085185267384402951048261791 : ℝ) / 92929579232735367585149843) * (scales0 h H) + ((-781719599377401145066669565 : ℝ) / 92929579232735367585149843) * (scales1 h H)

theorem homothetic_279 (h : Assignment) (H : Constraints h) :
    h 69 3 = h 1 3 + ((106480836916872452880983463 : ℝ) / 464647896163676837925749215) * (h 3 0 - h 1 0) := by
  linear_combination value_279 h H + ((-2371339062383857627979294082 : ℝ) / 464647896163676837925749215) * (scales0 h H) + ((377060251595859534768709821 : ℝ) / 92929579232735367585149843) * (scales1 h H)

theorem homothetic_280 (h : Assignment) (H : Constraints h) :
    h 70 0 = h 1 0 + ((39338327489839858386171227646 : ℝ) / 80657737443519335659690486109) * (h 3 0 - h 1 0) := by
  linear_combination value_280 h H + ((-35724170004512650198172474382 : ℝ) / 80657737443519335659690486109) * (scales0 h H) + ((30710762120847743456314792043 : ℝ) / 80657737443519335659690486109) * (scales1 h H)

theorem homothetic_281 (h : Assignment) (H : Constraints h) :
    h 70 1 = h 1 1 + ((321974428085998725597296933773 : ℝ) / 645261899548154685277523888872) * (h 3 0 - h 1 0) := by
  linear_combination value_281 h H + ((78153896159066249752805747307 : ℝ) / 322630949774077342638761944436) * (scales0 h H) + ((138794665687244804416753760493 : ℝ) / 645261899548154685277523888872) * (scales1 h H)

theorem homothetic_282 (h : Assignment) (H : Constraints h) :
    h 70 2 = h 1 2 + ((65835672595422239671695232802 : ℝ) / 80657737443519335659690486109) * (h 3 0 - h 1 0) := by
  linear_combination value_282 h H + ((164826048525223839798807150750 : ℝ) / 80657737443519335659690486109) * (scales0 h H) + ((-58342545896312511145748377200 : ℝ) / 80657737443519335659690486109) * (scales1 h H)

theorem homothetic_283 (h : Assignment) (H : Constraints h) :
    h 70 3 = h 1 3 + ((17921391158976226871865665829 : ℝ) / 80657737443519335659690486109) * (h 3 0 - h 1 0) := by
  linear_combination value_283 h H + ((-9074791502589585430862011494 : ℝ) / 80657737443519335659690486109) * (scales0 h H) + ((5992215956008704915417834675 : ℝ) / 80657737443519335659690486109) * (scales1 h H)

theorem homothetic_284 (h : Assignment) (H : Constraints h) :
    h 71 0 = h 1 0 + ((1003897197976319768434290316 : ℝ) / 2074506067496563827516624195) * (h 3 0 - h 1 0) := by
  linear_combination value_284 h H + ((13379951895815089576602050242 : ℝ) / 2996508764161703306412901615) * (scales0 h H) + ((-59937059233222266171502165333 : ℝ) / 16181147326473197854629668721) * (scales1 h H)

theorem homothetic_285 (h : Assignment) (H : Constraints h) :
    h 71 1 = h 1 1 + ((2122341129024522150111233753 : ℝ) / 4149012134993127655033248390) * (h 3 0 - h 1 0) := by
  linear_combination value_285 h H + ((-464292682002857386405736794337 : ℝ) / 47944140226587252902606425840) * (scales0 h H) + ((4250899001679056885007915587155 : ℝ) / 517796714447142331348149399072) * (scales1 h H)

theorem homothetic_286 (h : Assignment) (H : Constraints h) :
    h 71 2 = h 1 2 + ((1670260968397920540156861991 : ℝ) / 2074506067496563827516624195) * (h 3 0 - h 1 0) := by
  linear_combination value_286 h H + ((66287825663355286117291959149 : ℝ) / 5993017528323406612825803230) * (scales0 h H) + ((-3625571150397552950745705822997 : ℝ) / 453072125141249539929630724188) * (scales1 h H)

theorem homothetic_287 (h : Assignment) (H : Constraints h) :
    h 71 3 = h 1 3 + ((472864766827913401537169891 : ℝ) / 2074506067496563827516624195) * (h 3 0 - h 1 0) := by
  linear_combination value_287 h H + ((-14335953079860154106054582218 : ℝ) / 2996508764161703306412901615) * (scales0 h H) + ((435550986958983084455269195813 : ℝ) / 113268031285312384982407681047) * (scales1 h H)

theorem homothetic_288 (h : Assignment) (H : Constraints h) :
    h 72 0 = h 1 0 + ((4906535356657251125339724649 : ℝ) / 10142285318032214414898904385) * (h 3 0 - h 1 0) := by
  linear_combination value_288 h H + ((10709194217554460098522315188 : ℝ) / 10142285318032214414898904385) * (scales0 h H) + ((-8299416986506909385423492114 : ℝ) / 10142285318032214414898904385) * (scales1 h H)

theorem homothetic_289 (h : Assignment) (H : Constraints h) :
    h 72 1 = h 1 1 + ((44687036887344659550100205613 : ℝ) / 81138282544257715319191235080) * (h 3 0 - h 1 0) := by
  linear_combination value_289 h H + ((22530116888518686859564770383 : ℝ) / 40569141272128857659595617540) * (scales0 h H) + ((1894604078825100633048058891 : ℝ) / 40569141272128857659595617540) * (scales1 h H)

theorem homothetic_290 (h : Assignment) (H : Constraints h) :
    h 72 2 = h 1 2 + ((8304500581584305539562577334 : ℝ) / 10142285318032214414898904385) * (h 3 0 - h 1 0) := by
  linear_combination value_290 h H + ((22960600609335036967202013198 : ℝ) / 10142285318032214414898904385) * (scales0 h H) + ((-9074162538116691992675948894 : ℝ) / 10142285318032214414898904385) * (scales1 h H)

theorem homothetic_291 (h : Assignment) (H : Constraints h) :
    h 72 3 = h 1 3 + ((2239717528780526923198348569 : ℝ) / 10142285318032214414898904385) * (h 3 0 - h 1 0) := by
  linear_combination value_291 h H + ((-2298096067182135113927703582 : ℝ) / 10142285318032214414898904385) * (scales0 h H) + ((1652783455024682952663638331 : ℝ) / 10142285318032214414898904385) * (scales1 h H)

theorem homothetic_292 (h : Assignment) (H : Constraints h) :
    h 73 0 = h 1 0 + ((1020481614556172551615244 : ℝ) / 2150660474908759628252035) * (h 3 0 - h 1 0) := by
  linear_combination value_292 h H + ((144110868863848355564920998 : ℝ) / 49465190922901471449796805) * (scales0 h H) + ((-114320518036606348086814481 : ℝ) / 49465190922901471449796805) * (scales1 h H)

theorem homothetic_293 (h : Assignment) (H : Constraints h) :
    h 73 1 = h 1 1 + ((73792219984703345486771169 : ℝ) / 137642270394160616208130240) * (h 3 0 - h 1 0) := by
  linear_combination value_293 h H + ((5519385069167698573864438273 : ℝ) / 1582886109532847086393497760) * (scales0 h H) + ((-124284974950167962944205166943 : ℝ) / 53818127724116800937378923840) * (scales1 h H)

theorem homothetic_294 (h : Assignment) (H : Constraints h) :
    h 73 2 = h 1 2 + ((13680129980524901849883997 : ℝ) / 17205283799270077026016280) * (h 3 0 - h 1 0) := by
  linear_combination value_294 h H + ((277343704725602265677456865 : ℝ) / 39572152738321177159837444) * (scales0 h H) + ((-1863032374543099366316653579 : ℝ) / 395721527383211771598374440) * (scales1 h H)

theorem homothetic_295 (h : Assignment) (H : Constraints h) :
    h 73 3 = h 1 3 + ((501374243288405392583034 : ℝ) / 2150660474908759628252035) * (h 3 0 - h 1 0) := by
  linear_combination value_295 h H + ((-133037823446536300935042744 : ℝ) / 49465190922901471449796805) * (scales0 h H) + ((105973566221906182221802206 : ℝ) / 49465190922901471449796805) * (scales1 h H)

theorem homothetic_296 (h : Assignment) (H : Constraints h) :
    h 74 0 = h 1 0 + ((19707632172954535636665804033 : ℝ) / 40125038554912127264482075795) * (h 3 0 - h 1 0) := by
  linear_combination value_296 h H + ((-16988954485877604534684310704 : ℝ) / 40125038554912127264482075795) * (scales0 h H) + ((14869921899585899311348736212 : ℝ) / 40125038554912127264482075795) * (scales1 h H)

theorem homothetic_297 (h : Assignment) (H : Constraints h) :
    h 74 1 = h 1 1 + ((353642629134415506844988262617 : ℝ) / 642000616878594036231713212720) * (h 3 0 - h 1 0) := by
  linear_combination value_297 h H + ((172280964673096863417781854407 : ℝ) / 321000308439297018115856606360) * (scales0 h H) + ((39605003468736493200344541993 : ℝ) / 642000616878594036231713212720) * (scales1 h H)

theorem homothetic_298 (h : Assignment) (H : Constraints h) :
    h 74 2 = h 1 2 + ((32894453627601669236924528203 : ℝ) / 40125038554912127264482075795) * (h 3 0 - h 1 0) := by
  linear_combination value_298 h H + ((82808359645249467612955649736 : ℝ) / 40125038554912127264482075795) * (scales0 h H) + ((-29446801888989653781165002643 : ℝ) / 40125038554912127264482075795) * (scales1 h H)

theorem homothetic_299 (h : Assignment) (H : Constraints h) :
    h 74 3 = h 1 3 + ((8840082381656969702886826773 : ℝ) / 40125038554912127264482075795) * (h 3 0 - h 1 0) := by
  linear_combination value_299 h H + ((-4942135071977515637471305614 : ℝ) / 40125038554912127264482075795) * (scales0 h H) + ((3203773603528562030662615047 : ℝ) / 40125038554912127264482075795) * (scales1 h H)

theorem homothetic_300 (h : Assignment) (H : Constraints h) :
    h 75 0 = h 1 0 + ((1816572152561131527176 : ℝ) / 3768430844561840415153) * (h 3 0 - h 1 0) := by
  linear_combination value_300 h H + ((7217593650578870064146152214 : ℝ) / 2062598283453637770117117425) * (scales0 h H) + ((-163233951289965804929195203843 : ℝ) / 55690153653248219793162170475) * (scales1 h H)

theorem homothetic_301 (h : Assignment) (H : Constraints h) :
    h 75 1 = h 1 1 + ((899744661814417380293 : ℝ) / 1674858153138595740068) * (h 3 0 - h 1 0) := by
  linear_combination value_301 h H + ((117865192495578550643752549481 : ℝ) / 33001572535258204321873878800) * (scales0 h H) + ((-8074956830011493968555468420447 : ℝ) / 3366160398596336840831135637600) * (scales1 h H)

theorem homothetic_302 (h : Assignment) (H : Constraints h) :
    h 75 2 = h 1 2 + ((12023881457031766930853 : ℝ) / 15073723378247361660612) * (h 3 0 - h 1 0) := by
  linear_combination value_302 h H + ((14865341638549968439249778579 : ℝ) / 2062598283453637770117117425) * (scales0 h H) + ((-273885615923138555919198178573 : ℝ) / 55690153653248219793162170475) * (scales1 h H)

theorem homothetic_303 (h : Assignment) (H : Constraints h) :
    h 75 3 = h 1 3 + ((873519230859749645698 : ℝ) / 3768430844561840415153) * (h 3 0 - h 1 0) := by
  linear_combination value_303 h H + ((-5759642033963314397148106256 : ℝ) / 2062598283453637770117117425) * (scales0 h H) + ((125373544643667335704090026622 : ℝ) / 55690153653248219793162170475) * (scales1 h H)

theorem homothetic_304 (h : Assignment) (H : Constraints h) :
    h 76 0 = h 1 0 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_304 h H + ((45182599067 : ℝ) / 120001635295) * (scales0 h H)

theorem homothetic_305 (h : Assignment) (H : Constraints h) :
    h 76 1 = h 1 1 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_305 h H + ((45182599067 : ℝ) / 120001635295) * (scales0 h H)

theorem homothetic_306 (h : Assignment) (H : Constraints h) :
    h 76 2 = h 1 2 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_306 h H + ((45182599067 : ℝ) / 120001635295) * (scales0 h H)

theorem homothetic_307 (h : Assignment) (H : Constraints h) :
    h 76 3 = h 1 3 + ((-29636437161 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_307 h H + ((-29636437161 : ℝ) / 120001635295) * (scales0 h H)

theorem homothetic_308 (h : Assignment) (H : Constraints h) :
    h 77 0 = h 1 0 + ((117193993383 : ℝ) / 333176110636) * (h 3 0 - h 1 0) := by
  linear_combination value_308 h H + ((117193993383 : ℝ) / 333176110636) * (scales0 h H)

theorem homothetic_309 (h : Assignment) (H : Constraints h) :
    h 77 1 = h 1 1 + ((129880447682 : ℝ) / 249882082977) * (h 3 0 - h 1 0) := by
  linear_combination value_309 h H + ((129880447682 : ℝ) / 249882082977) * (scales0 h H)

theorem homothetic_310 (h : Assignment) (H : Constraints h) :
    h 77 2 = h 1 2 + ((117193993383 : ℝ) / 333176110636) * (h 3 0 - h 1 0) := by
  linear_combination value_310 h H + ((117193993383 : ℝ) / 333176110636) * (scales0 h H)

theorem homothetic_311 (h : Assignment) (H : Constraints h) :
    h 77 3 = h 1 3 + ((-19757624774 : ℝ) / 83294027659) * (h 3 0 - h 1 0) := by
  linear_combination value_311 h H + ((-19757624774 : ℝ) / 83294027659) * (scales0 h H)

theorem homothetic_312 (h : Assignment) (H : Constraints h) :
    h 78 0 = h 1 0 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_312 h H + ((45182599067 : ℝ) / 120001635295) * (scales0 h H)

theorem homothetic_313 (h : Assignment) (H : Constraints h) :
    h 78 1 = h 1 1 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_313 h H + ((45182599067 : ℝ) / 120001635295) * (scales0 h H)

theorem homothetic_314 (h : Assignment) (H : Constraints h) :
    h 78 2 = h 1 2 + ((32135819613 : ℝ) / 48000654118) * (h 3 0 - h 1 0) := by
  linear_combination value_314 h H + ((-15864834505 : ℝ) / 48000654118) * (scales0 h H) + (1 : ℝ) * (scales1 h H)

theorem homothetic_315 (h : Assignment) (H : Constraints h) :
    h 78 3 = h 1 3 + ((-29636437161 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_315 h H + ((-29636437161 : ℝ) / 120001635295) * (scales0 h H)

theorem homothetic_316 (h : Assignment) (H : Constraints h) :
    h 79 0 = h 1 0 + ((117193993383 : ℝ) / 333176110636) * (h 3 0 - h 1 0) := by
  linear_combination value_316 h H + ((117193993383 : ℝ) / 333176110636) * (scales0 h H)

theorem homothetic_317 (h : Assignment) (H : Constraints h) :
    h 79 1 = h 1 1 + ((129880447682 : ℝ) / 249882082977) * (h 3 0 - h 1 0) := by
  linear_combination value_317 h H + ((129880447682 : ℝ) / 249882082977) * (scales0 h H)

theorem homothetic_318 (h : Assignment) (H : Constraints h) :
    h 79 2 = h 1 2 + ((458114032001 : ℝ) / 666352221272) * (h 3 0 - h 1 0) := by
  linear_combination value_318 h H + ((-208238189271 : ℝ) / 666352221272) * (scales0 h H) + (1 : ℝ) * (scales1 h H)

theorem homothetic_319 (h : Assignment) (H : Constraints h) :
    h 79 3 = h 1 3 + ((-19757624774 : ℝ) / 83294027659) * (h 3 0 - h 1 0) := by
  linear_combination value_319 h H + ((-19757624774 : ℝ) / 83294027659) * (scales0 h H)

theorem homothetic_320 (h : Assignment) (H : Constraints h) :
    h 80 0 = h 1 0 + ((74819036228 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_320 h H + ((-45182599067 : ℝ) / 120001635295) * (scales0 h H)

theorem homothetic_321 (h : Assignment) (H : Constraints h) :
    h 80 1 = h 1 1 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_321 h H + ((45182599067 : ℝ) / 120001635295) * (scales0 h H)

theorem homothetic_322 (h : Assignment) (H : Constraints h) :
    h 80 2 = h 1 2 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_322 h H + ((45182599067 : ℝ) / 120001635295) * (scales0 h H)

theorem homothetic_323 (h : Assignment) (H : Constraints h) :
    h 80 3 = h 1 3 + ((-29636437161 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_323 h H + ((-29636437161 : ℝ) / 120001635295) * (scales0 h H)

theorem homothetic_324 (h : Assignment) (H : Constraints h) :
    h 81 0 = h 1 0 + ((328912582073 : ℝ) / 499764165954) * (h 3 0 - h 1 0) := by
  linear_combination value_324 h H + ((-170851583881 : ℝ) / 499764165954) * (scales0 h H)

theorem homothetic_325 (h : Assignment) (H : Constraints h) :
    h 81 1 = h 1 1 + ((129880447682 : ℝ) / 249882082977) * (h 3 0 - h 1 0) := by
  linear_combination value_325 h H + ((129880447682 : ℝ) / 249882082977) * (scales0 h H)

theorem homothetic_326 (h : Assignment) (H : Constraints h) :
    h 81 2 = h 1 2 + ((117193993383 : ℝ) / 333176110636) * (h 3 0 - h 1 0) := by
  linear_combination value_326 h H + ((117193993383 : ℝ) / 333176110636) * (scales0 h H)

theorem homothetic_327 (h : Assignment) (H : Constraints h) :
    h 81 3 = h 1 3 + ((-19757624774 : ℝ) / 83294027659) * (h 3 0 - h 1 0) := by
  linear_combination value_327 h H + ((-19757624774 : ℝ) / 83294027659) * (scales0 h H)

theorem homothetic_328 (h : Assignment) (H : Constraints h) :
    h 82 0 = h 1 0 + ((74819036228 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_328 h H + ((-45182599067 : ℝ) / 120001635295) * (scales0 h H)

theorem homothetic_329 (h : Assignment) (H : Constraints h) :
    h 82 1 = h 1 1 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_329 h H + ((45182599067 : ℝ) / 120001635295) * (scales0 h H)

theorem homothetic_330 (h : Assignment) (H : Constraints h) :
    h 82 2 = h 1 2 + ((32135819613 : ℝ) / 48000654118) * (h 3 0 - h 1 0) := by
  linear_combination value_330 h H + ((-15864834505 : ℝ) / 48000654118) * (scales0 h H) + (1 : ℝ) * (scales1 h H)

theorem homothetic_331 (h : Assignment) (H : Constraints h) :
    h 82 3 = h 1 3 + ((-29636437161 : ℝ) / 120001635295) * (h 3 0 - h 1 0) := by
  linear_combination value_331 h H + ((-29636437161 : ℝ) / 120001635295) * (scales0 h H)

theorem homothetic_332 (h : Assignment) (H : Constraints h) :
    h 83 0 = h 1 0 + ((328912582073 : ℝ) / 499764165954) * (h 3 0 - h 1 0) := by
  linear_combination value_332 h H + ((-170851583881 : ℝ) / 499764165954) * (scales0 h H)

theorem homothetic_333 (h : Assignment) (H : Constraints h) :
    h 83 1 = h 1 1 + ((129880447682 : ℝ) / 249882082977) * (h 3 0 - h 1 0) := by
  linear_combination value_333 h H + ((129880447682 : ℝ) / 249882082977) * (scales0 h H)

theorem homothetic_334 (h : Assignment) (H : Constraints h) :
    h 83 2 = h 1 2 + ((458114032001 : ℝ) / 666352221272) * (h 3 0 - h 1 0) := by
  linear_combination value_334 h H + ((-208238189271 : ℝ) / 666352221272) * (scales0 h H) + (1 : ℝ) * (scales1 h H)

theorem homothetic_335 (h : Assignment) (H : Constraints h) :
    h 83 3 = h 1 3 + ((-19757624774 : ℝ) / 83294027659) * (h 3 0 - h 1 0) := by
  linear_combination value_335 h H + ((-19757624774 : ℝ) / 83294027659) * (scales0 h H)

theorem homothetic_336 (h : Assignment) (H : Constraints h) :
    h 84 0 = h 1 0 + ((158648699407709 : ℝ) / 617857941263449) * (h 3 0 - h 1 0) := by
  linear_combination value_336 h H + ((306483803023377 : ℝ) / 617857941263449) * (scales0 h H) + ((-814601591351640 : ℝ) / 617857941263449) * (scales1 h H)

theorem homothetic_337 (h : Assignment) (H : Constraints h) :
    h 84 1 = h 1 1 + ((282243102288077 : ℝ) / 617857941263449) * (h 3 0 - h 1 0) := by
  linear_combination value_337 h H + ((183114840466635 : ℝ) / 617857941263449) * (scales0 h H) + ((546216952893660 : ℝ) / 617857941263449) * (scales1 h H)

theorem homothetic_338 (h : Assignment) (H : Constraints h) :
    h 84 2 = h 1 2 + ((158648699407709 : ℝ) / 617857941263449) * (h 3 0 - h 1 0) := by
  linear_combination value_338 h H + ((306483803023377 : ℝ) / 617857941263449) * (scales0 h H) + ((-814601591351640 : ℝ) / 617857941263449) * (scales1 h H)

theorem homothetic_339 (h : Assignment) (H : Constraints h) :
    h 84 3 = h 1 3 + ((-144596176908519 : ℝ) / 617857941263449) * (h 3 0 - h 1 0) := by
  linear_combination value_339 h H + ((-160570216538298 : ℝ) / 617857941263449) * (scales0 h H) + ((88020218368170 : ℝ) / 617857941263449) * (scales1 h H)

theorem homothetic_340 (h : Assignment) (H : Constraints h) :
    h 85 0 = h 1 0 + ((2975709287677 : ℝ) / 13520913290240) * (h 3 0 - h 1 0) := by
  linear_combination value_340 h H + ((1639676546271 : ℝ) / 1352091329024) * (scales1 h H)

theorem homothetic_341 (h : Assignment) (H : Constraints h) :
    h 85 1 = h 1 1 + ((1176016025891 : ℝ) / 2704182658048) * (h 3 0 - h 1 0) := by
  linear_combination value_341 h H + ((3240044152965 : ℝ) / 1352091329024) * (scales1 h H)

theorem homothetic_342 (h : Assignment) (H : Constraints h) :
    h 85 2 = h 1 2 + ((2975709287677 : ℝ) / 13520913290240) * (h 3 0 - h 1 0) := by
  linear_combination value_342 h H + ((1639676546271 : ℝ) / 1352091329024) * (scales1 h H)

theorem homothetic_343 (h : Assignment) (H : Constraints h) :
    h 85 3 = h 1 3 + ((-1452185420889 : ℝ) / 6760456645120) * (h 3 0 - h 1 0) := by
  linear_combination value_343 h H + ((-800183803347 : ℝ) / 676045664512) * (scales1 h H)

theorem homothetic_344 (h : Assignment) (H : Constraints h) :
    h 86 0 = h 1 0 + ((42614921436437 : ℝ) / 167585073310154) * (h 3 0 - h 1 0) := by
  linear_combination value_344 h H + ((1123773944419049 : ℝ) / 2429983562997233) * (scales0 h H) + ((-2787378521826375 : ℝ) / 2429983562997233) * (scales1 h H)

theorem homothetic_345 (h : Assignment) (H : Constraints h) :
    h 86 1 = h 1 1 + ((39963337415001 : ℝ) / 83792536655077) * (h 3 0 - h 1 0) := by
  linear_combination value_345 h H + ((1381269029448595 : ℝ) / 2429983562997233) * (scales0 h H) + ((-1225096040646180 : ℝ) / 2429983562997233) * (scales1 h H)

theorem homothetic_346 (h : Assignment) (H : Constraints h) :
    h 86 2 = h 1 2 + ((42614921436437 : ℝ) / 167585073310154) * (h 3 0 - h 1 0) := by
  linear_combination value_346 h H + ((1123773944419049 : ℝ) / 2429983562997233) * (scales0 h H) + ((-2787378521826375 : ℝ) / 2429983562997233) * (scales1 h H)

theorem homothetic_347 (h : Assignment) (H : Constraints h) :
    h 86 3 = h 1 3 + ((-19500775651938 : ℝ) / 83792536655077) * (h 3 0 - h 1 0) := by
  linear_combination value_347 h H + ((-20301981401394 : ℝ) / 83792536655077) * (scales0 h H) + ((4414807190880 : ℝ) / 83792536655077) * (scales1 h H)

theorem homothetic_348 (h : Assignment) (H : Constraints h) :
    h 87 0 = h 1 0 + ((2975709287677 : ℝ) / 13520913290240) * (h 3 0 - h 1 0) := by
  linear_combination value_348 h H + ((1639676546271 : ℝ) / 1352091329024) * (scales1 h H)

theorem homothetic_349 (h : Assignment) (H : Constraints h) :
    h 87 1 = h 1 1 + ((3440082303493 : ℝ) / 6760456645120) * (h 3 0 - h 1 0) := by
  linear_combination value_349 h H + (1 : ℝ) * (scales0 h H) + ((-12807158174847 : ℝ) / 4732319651584) * (scales1 h H)

theorem homothetic_350 (h : Assignment) (H : Constraints h) :
    h 87 2 = h 1 2 + ((2975709287677 : ℝ) / 13520913290240) * (h 3 0 - h 1 0) := by
  linear_combination value_350 h H + ((1639676546271 : ℝ) / 1352091329024) * (scales1 h H)

theorem homothetic_351 (h : Assignment) (H : Constraints h) :
    h 87 3 = h 1 3 + ((-1452185420889 : ℝ) / 6760456645120) * (h 3 0 - h 1 0) := by
  linear_combination value_351 h H + ((-800183803347 : ℝ) / 676045664512) * (scales1 h H)

theorem homothetic_352 (h : Assignment) (H : Constraints h) :
    h 88 0 = h 1 0 + ((744044857571303 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0) := by
  linear_combination value_352 h H + ((1091004794628483 : ℝ) / 2542109602773571) * (scales0 h H) + ((-2769645410595576 : ℝ) / 2542109602773571) * (scales1 h H)

theorem homothetic_353 (h : Assignment) (H : Constraints h) :
    h 88 1 = h 1 1 + ((1100037740749235 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0) := by
  linear_combination value_353 h H + ((867389779331565 : ℝ) / 2542109602773571) * (scales0 h H) + ((1857137639838444 : ℝ) / 2542109602773571) * (scales1 h H)

theorem homothetic_354 (h : Assignment) (H : Constraints h) :
    h 88 2 = h 1 2 + ((3643447258418433 : ℝ) / 5084219205547142) * (h 3 0 - h 1 0) := by
  linear_combination value_354 h H + ((-1830920974610259 : ℝ) / 5084219205547142) * (scales0 h H) + ((4099313112460801 : ℝ) / 2542109602773571) * (scales1 h H)

theorem homothetic_355 (h : Assignment) (H : Constraints h) :
    h 88 3 = h 1 3 + ((-604790773144527 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0) := by
  linear_combination value_355 h H + ((-642280866153192 : ℝ) / 2542109602773571) * (scales0 h H) + ((299268742451778 : ℝ) / 2542109602773571) * (scales1 h H)

theorem homothetic_356 (h : Assignment) (H : Constraints h) :
    h 89 0 = h 1 0 + ((60728760973 : ℝ) / 358549019234) * (h 3 0 - h 1 0) := by
  linear_combination value_356 h H + ((27874501286607 : ℝ) / 20616568605955) * (scales1 h H)

theorem homothetic_357 (h : Assignment) (H : Constraints h) :
    h 89 1 = h 1 1 + ((120001635295 : ℝ) / 358549019234) * (h 3 0 - h 1 0) := by
  linear_combination value_357 h H + ((11016150120081 : ℝ) / 4123313721191) * (scales1 h H)

theorem homothetic_358 (h : Assignment) (H : Constraints h) :
    h 89 2 = h 1 2 + ((588086130579 : ℝ) / 717098038468) * (h 3 0 - h 1 0) := by
  linear_combination value_358 h H + ((-17983328509141 : ℝ) / 41233137211910) * (scales1 h H)

theorem homothetic_359 (h : Assignment) (H : Constraints h) :
    h 89 3 = h 1 3 + ((-29636437161 : ℝ) / 179274509617) * (h 3 0 - h 1 0) := by
  linear_combination value_359 h H + ((-27206249313798 : ℝ) / 20616568605955) * (scales1 h H)

theorem homothetic_360 (h : Assignment) (H : Constraints h) :
    h 90 0 = h 1 0 + ((5626268271645667 : ℝ) / 19645476759162664) * (h 3 0 - h 1 0) := by
  linear_combination value_360 h H + ((4000350913637771 : ℝ) / 9822738379581332) * (scales0 h H) + ((-9477086974209675 : ℝ) / 9822738379581332) * (scales1 h H)

theorem homothetic_361 (h : Assignment) (H : Constraints h) :
    h 90 1 = h 1 1 + ((2411684364523635 : ℝ) / 4911369189790666) * (h 3 0 - h 1 0) := by
  linear_combination value_361 h H + ((1336292223626920 : ℝ) / 2455684594895333) * (scales0 h H) + ((-1041331634549253 : ℝ) / 2455684594895333) * (scales1 h H)

theorem homothetic_362 (h : Assignment) (H : Constraints h) :
    h 90 2 = h 1 2 + ((28364274250472077 : ℝ) / 39290953518325328) * (h 3 0 - h 1 0) := by
  linear_combination value_362 h H + ((-6713376906904283 : ℝ) / 19645476759162664) * (scales0 h H) + ((29624035164323443 : ℝ) / 19645476759162664) * (scales1 h H)

theorem homothetic_363 (h : Assignment) (H : Constraints h) :
    h 90 3 = h 1 3 + ((-575124699546366 : ℝ) / 2455684594895333) * (h 3 0 - h 1 0) := by
  linear_combination value_363 h H + ((-588757460640426 : ℝ) / 2455684594895333) * (scales0 h H) + ((108824997255192 : ℝ) / 2455684594895333) * (scales1 h H)

theorem homothetic_364 (h : Assignment) (H : Constraints h) :
    h 91 0 = h 1 0 + ((60728760973 : ℝ) / 358549019234) * (h 3 0 - h 1 0) := by
  linear_combination value_364 h H + ((27874501286607 : ℝ) / 20616568605955) * (scales1 h H)

theorem homothetic_365 (h : Assignment) (H : Constraints h) :
    h 91 1 = h 1 1 + ((780582375658 : ℝ) / 1254921567319) * (h 3 0 - h 1 0) := by
  linear_combination value_365 h H + (1 : ℝ) * (scales0 h H) + ((-435443377944798 : ℝ) / 144315980241685) * (scales1 h H)

theorem homothetic_366 (h : Assignment) (H : Constraints h) :
    h 91 2 = h 1 2 + ((588086130579 : ℝ) / 717098038468) * (h 3 0 - h 1 0) := by
  linear_combination value_366 h H + ((-17983328509141 : ℝ) / 41233137211910) * (scales1 h H)

theorem homothetic_367 (h : Assignment) (H : Constraints h) :
    h 91 3 = h 1 3 + ((-29636437161 : ℝ) / 179274509617) * (h 3 0 - h 1 0) := by
  linear_combination value_367 h H + ((-27206249313798 : ℝ) / 20616568605955) * (scales1 h H)

theorem homothetic_368 (h : Assignment) (H : Constraints h) :
    h 92 0 = h 1 0 + ((1976061186791234 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0) := by
  linear_combination value_368 h H + ((-1202812302276942 : ℝ) / 2542109602773571) * (scales0 h H) + ((5083036935812586 : ℝ) / 2542109602773571) * (scales1 h H)

theorem homothetic_369 (h : Assignment) (H : Constraints h) :
    h 92 1 = h 1 1 + ((1100037740749235 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0) := by
  linear_combination value_369 h H + ((867389779331565 : ℝ) / 2542109602773571) * (scales0 h H) + ((1857137639838444 : ℝ) / 2542109602773571) * (scales1 h H)

theorem homothetic_370 (h : Assignment) (H : Constraints h) :
    h 92 2 = h 1 2 + ((744044857571303 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0) := by
  linear_combination value_370 h H + ((1091004794628483 : ℝ) / 2542109602773571) * (scales0 h H) + ((-2769645410595576 : ℝ) / 2542109602773571) * (scales1 h H)

theorem homothetic_371 (h : Assignment) (H : Constraints h) :
    h 92 3 = h 1 3 + ((-604790773144527 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0) := by
  linear_combination value_371 h H + ((-642280866153192 : ℝ) / 2542109602773571) * (scales0 h H) + ((299268742451778 : ℝ) / 2542109602773571) * (scales1 h H)

theorem homothetic_372 (h : Assignment) (H : Constraints h) :
    h 93 0 = h 1 0 + ((163728347711 : ℝ) / 179274509617) * (h 3 0 - h 1 0) := by
  linear_combination value_372 h H + ((-14271376629708 : ℝ) / 20616568605955) * (scales1 h H)

theorem homothetic_373 (h : Assignment) (H : Constraints h) :
    h 93 1 = h 1 1 + ((120001635295 : ℝ) / 358549019234) * (h 3 0 - h 1 0) := by
  linear_combination value_373 h H + ((11016150120081 : ℝ) / 4123313721191) * (scales1 h H)

theorem homothetic_374 (h : Assignment) (H : Constraints h) :
    h 93 2 = h 1 2 + ((60728760973 : ℝ) / 358549019234) * (h 3 0 - h 1 0) := by
  linear_combination value_374 h H + ((27874501286607 : ℝ) / 20616568605955) * (scales1 h H)

theorem homothetic_375 (h : Assignment) (H : Constraints h) :
    h 93 3 = h 1 3 + ((-29636437161 : ℝ) / 179274509617) * (h 3 0 - h 1 0) := by
  linear_combination value_375 h H + ((-27206249313798 : ℝ) / 20616568605955) * (scales1 h H)

theorem homothetic_376 (h : Assignment) (H : Constraints h) :
    h 94 0 = h 1 0 + ((7703724177912473 : ℝ) / 9822738379581332) * (h 3 0 - h 1 0) := by
  linear_combination value_376 h H + ((-2205155887507727 : ℝ) / 4911369189790666) * (scales0 h H) + ((9145265966661627 : ℝ) / 4911369189790666) * (scales1 h H)

theorem homothetic_377 (h : Assignment) (H : Constraints h) :
    h 94 1 = h 1 1 + ((2411684364523635 : ℝ) / 4911369189790666) * (h 3 0 - h 1 0) := by
  linear_combination value_377 h H + ((1336292223626920 : ℝ) / 2455684594895333) * (scales0 h H) + ((-1041331634549253 : ℝ) / 2455684594895333) * (scales1 h H)

theorem homothetic_378 (h : Assignment) (H : Constraints h) :
    h 94 2 = h 1 2 + ((5626268271645667 : ℝ) / 19645476759162664) * (h 3 0 - h 1 0) := by
  linear_combination value_378 h H + ((4000350913637771 : ℝ) / 9822738379581332) * (scales0 h H) + ((-9477086974209675 : ℝ) / 9822738379581332) * (scales1 h H)

theorem homothetic_379 (h : Assignment) (H : Constraints h) :
    h 94 3 = h 1 3 + ((-575124699546366 : ℝ) / 2455684594895333) * (h 3 0 - h 1 0) := by
  linear_combination value_379 h H + ((-588757460640426 : ℝ) / 2455684594895333) * (scales0 h H) + ((108824997255192 : ℝ) / 2455684594895333) * (scales1 h H)

theorem homothetic_380 (h : Assignment) (H : Constraints h) :
    h 95 0 = h 1 0 + ((163728347711 : ℝ) / 179274509617) * (h 3 0 - h 1 0) := by
  linear_combination value_380 h H + ((-14271376629708 : ℝ) / 20616568605955) * (scales1 h H)

theorem homothetic_381 (h : Assignment) (H : Constraints h) :
    h 95 1 = h 1 1 + ((780582375658 : ℝ) / 1254921567319) * (h 3 0 - h 1 0) := by
  linear_combination value_381 h H + (1 : ℝ) * (scales0 h H) + ((-435443377944798 : ℝ) / 144315980241685) * (scales1 h H)

theorem homothetic_382 (h : Assignment) (H : Constraints h) :
    h 95 2 = h 1 2 + ((60728760973 : ℝ) / 358549019234) * (h 3 0 - h 1 0) := by
  linear_combination value_382 h H + ((27874501286607 : ℝ) / 20616568605955) * (scales1 h H)

theorem homothetic_383 (h : Assignment) (H : Constraints h) :
    h 95 3 = h 1 3 + ((-29636437161 : ℝ) / 179274509617) * (h 3 0 - h 1 0) := by
  linear_combination value_383 h H + ((-27206249313798 : ℝ) / 20616568605955) * (scales1 h H)

theorem homothetic_384 (h : Assignment) (H : Constraints h) :
    h 96 0 = h 1 0 + ((1976061186791234 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0) := by
  linear_combination value_384 h H + ((-1202812302276942 : ℝ) / 2542109602773571) * (scales0 h H) + ((5083036935812586 : ℝ) / 2542109602773571) * (scales1 h H)

theorem homothetic_385 (h : Assignment) (H : Constraints h) :
    h 96 1 = h 1 1 + ((1100037740749235 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0) := by
  linear_combination value_385 h H + ((867389779331565 : ℝ) / 2542109602773571) * (scales0 h H) + ((1857137639838444 : ℝ) / 2542109602773571) * (scales1 h H)

theorem homothetic_386 (h : Assignment) (H : Constraints h) :
    h 96 2 = h 1 2 + ((3643447258418433 : ℝ) / 5084219205547142) * (h 3 0 - h 1 0) := by
  linear_combination value_386 h H + ((-1830920974610259 : ℝ) / 5084219205547142) * (scales0 h H) + ((4099313112460801 : ℝ) / 2542109602773571) * (scales1 h H)

theorem homothetic_387 (h : Assignment) (H : Constraints h) :
    h 96 3 = h 1 3 + ((-604790773144527 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0) := by
  linear_combination value_387 h H + ((-642280866153192 : ℝ) / 2542109602773571) * (scales0 h H) + ((299268742451778 : ℝ) / 2542109602773571) * (scales1 h H)

theorem homothetic_388 (h : Assignment) (H : Constraints h) :
    h 97 0 = h 1 0 + ((163728347711 : ℝ) / 179274509617) * (h 3 0 - h 1 0) := by
  linear_combination value_388 h H + ((-14271376629708 : ℝ) / 20616568605955) * (scales1 h H)

theorem homothetic_389 (h : Assignment) (H : Constraints h) :
    h 97 1 = h 1 1 + ((120001635295 : ℝ) / 358549019234) * (h 3 0 - h 1 0) := by
  linear_combination value_389 h H + ((11016150120081 : ℝ) / 4123313721191) * (scales1 h H)

theorem homothetic_390 (h : Assignment) (H : Constraints h) :
    h 97 2 = h 1 2 + ((588086130579 : ℝ) / 717098038468) * (h 3 0 - h 1 0) := by
  linear_combination value_390 h H + ((-17983328509141 : ℝ) / 41233137211910) * (scales1 h H)

theorem homothetic_391 (h : Assignment) (H : Constraints h) :
    h 97 3 = h 1 3 + ((-29636437161 : ℝ) / 179274509617) * (h 3 0 - h 1 0) := by
  linear_combination value_391 h H + ((-27206249313798 : ℝ) / 20616568605955) * (scales1 h H)

theorem homothetic_392 (h : Assignment) (H : Constraints h) :
    h 98 0 = h 1 0 + ((7703724177912473 : ℝ) / 9822738379581332) * (h 3 0 - h 1 0) := by
  linear_combination value_392 h H + ((-2205155887507727 : ℝ) / 4911369189790666) * (scales0 h H) + ((9145265966661627 : ℝ) / 4911369189790666) * (scales1 h H)

theorem homothetic_393 (h : Assignment) (H : Constraints h) :
    h 98 1 = h 1 1 + ((2411684364523635 : ℝ) / 4911369189790666) * (h 3 0 - h 1 0) := by
  linear_combination value_393 h H + ((1336292223626920 : ℝ) / 2455684594895333) * (scales0 h H) + ((-1041331634549253 : ℝ) / 2455684594895333) * (scales1 h H)

theorem homothetic_394 (h : Assignment) (H : Constraints h) :
    h 98 2 = h 1 2 + ((28364274250472077 : ℝ) / 39290953518325328) * (h 3 0 - h 1 0) := by
  linear_combination value_394 h H + ((-6713376906904283 : ℝ) / 19645476759162664) * (scales0 h H) + ((29624035164323443 : ℝ) / 19645476759162664) * (scales1 h H)

theorem homothetic_395 (h : Assignment) (H : Constraints h) :
    h 98 3 = h 1 3 + ((-575124699546366 : ℝ) / 2455684594895333) * (h 3 0 - h 1 0) := by
  linear_combination value_395 h H + ((-588757460640426 : ℝ) / 2455684594895333) * (scales0 h H) + ((108824997255192 : ℝ) / 2455684594895333) * (scales1 h H)

theorem homothetic_396 (h : Assignment) (H : Constraints h) :
    h 99 0 = h 1 0 + ((163728347711 : ℝ) / 179274509617) * (h 3 0 - h 1 0) := by
  linear_combination value_396 h H + ((-14271376629708 : ℝ) / 20616568605955) * (scales1 h H)

theorem homothetic_397 (h : Assignment) (H : Constraints h) :
    h 99 1 = h 1 1 + ((780582375658 : ℝ) / 1254921567319) * (h 3 0 - h 1 0) := by
  linear_combination value_397 h H + (1 : ℝ) * (scales0 h H) + ((-435443377944798 : ℝ) / 144315980241685) * (scales1 h H)

theorem homothetic_398 (h : Assignment) (H : Constraints h) :
    h 99 2 = h 1 2 + ((588086130579 : ℝ) / 717098038468) * (h 3 0 - h 1 0) := by
  linear_combination value_398 h H + ((-17983328509141 : ℝ) / 41233137211910) * (scales1 h H)

theorem homothetic_399 (h : Assignment) (H : Constraints h) :
    h 99 3 = h 1 3 + ((-29636437161 : ℝ) / 179274509617) * (h 3 0 - h 1 0) := by
  linear_combination value_399 h H + ((-27206249313798 : ℝ) / 20616568605955) * (scales1 h H)

theorem homothetic_400 (h : Assignment) (H : Constraints h) :
    h 100 0 = h 1 0 + ((252036929976259488883767 : ℝ) / 320543882331214009672076) * (h 3 0 - h 1 0) := by
  linear_combination value_400 h H + ((-77075308907547833268126965 : ℝ) / 198897478986518293001523158) * (scales0 h H) + ((2092699072455672553385462919 : ℝ) / 1345482946085270805598539010) * (scales1 h H)

theorem homothetic_401 (h : Assignment) (H : Constraints h) :
    h 100 1 = h 1 1 + ((37924673351107660395524 : ℝ) / 80135970582803502418019) * (h 3 0 - h 1 0) := by
  linear_combination value_401 h H + ((-13368408477046350206631803 : ℝ) / 99448739493259146500761579) * (scales0 h H) + ((1984243624967293010630333118 : ℝ) / 672741473042635402799269505) * (scales1 h H)

theorem homothetic_402 (h : Assignment) (H : Constraints h) :
    h 100 2 = h 1 2 + ((22977346258318728988718983 : ℝ) / 43593967997045105315402336) * (h 3 0 - h 1 0) := by
  linear_combination value_402 h H + ((5909849546842025310538840485 : ℝ) / 27050057142166487848207149488) * (scales0 h H) + ((-128334351448113932233494742221 : ℝ) / 182985680667596829561401305360) * (scales1 h H)

theorem homothetic_403 (h : Assignment) (H : Constraints h) :
    h 100 3 = h 1 3 + ((-19011358777051563159879 : ℝ) / 80135970582803502418019) * (h 3 0 - h 1 0) := by
  linear_combination value_403 h H + ((-1591472348546978811637752 : ℝ) / 5849925852544655676515387) * (scales0 h H) + ((141879948728109196051564326 : ℝ) / 672741473042635402799269505) * (scales1 h H)

theorem homothetic_404 (h : Assignment) (H : Constraints h) :
    h 101 0 = h 1 0 + ((6771655532286104264962343 : ℝ) / 8706300919230256219546134) * (h 3 0 - h 1 0) := by
  linear_combination value_404 h H + ((-1263524282708508219959261271881 : ℝ) / 545310451775067868055052556956) * (scales0 h H) + ((31762477745279768535251075617161 : ℝ) / 3483927886340711379240613558330) * (scales1 h H)

theorem homothetic_405 (h : Assignment) (H : Constraints h) :
    h 101 1 = h 1 1 + ((2047002871184314068251267 : ℝ) / 4353150459615128109773067) * (h 3 0 - h 1 0) := by
  linear_combination value_405 h H + ((-111861372200933191332754672990 : ℝ) / 136327612943766967013763139239) * (scales0 h H) + ((1964305101213638443870359895770 : ℝ) / 348392788634071137924061355833) * (scales1 h H)

theorem homothetic_406 (h : Assignment) (H : Constraints h) :
    h 101 2 = h 1 2 + ((12242802616029478209018187 : ℝ) / 23216802451280683252123024) * (h 3 0 - h 1 0) := by
  linear_combination value_406 h H + ((6798743945144548393304339320733 : ℝ) / 24720740480469743351829049248672) * (scales0 h H) + ((-25723007555725338834837341160387 : ℝ) / 27871423090725691033924908466640) * (scales1 h H)

theorem homothetic_407 (h : Assignment) (H : Constraints h) :
    h 101 3 = h 1 3 + ((-344918463589651164188249 : ℝ) / 1451050153205042703257689) * (h 3 0 - h 1 0) := by
  linear_combination value_407 h H + ((-17152950526243690493712896468 : ℝ) / 45442537647922322337921046413) * (scales0 h H) + ((1086975051893597234230446355038 : ℝ) / 1741963943170355689620306779165) * (scales1 h H)

theorem homothetic_408 (h : Assignment) (H : Constraints h) :
    h 102 0 = h 1 0 + ((59446036744140026258008847 : ℝ) / 75578597936612822697935166) * (h 3 0 - h 1 0) := by
  linear_combination value_408 h H + ((-1547308847835853480810011144365 : ℝ) / 4733789903161807536862471187244) * (scales0 h H) + ((13283879343489716995631629035751 : ℝ) / 10081219238214960495170077528390) * (scales1 h H)

theorem homothetic_409 (h : Assignment) (H : Constraints h) :
    h 102 1 = h 1 1 + ((17999741293728835263788678 : ℝ) / 37789298968306411348967583) * (h 3 0 - h 1 0) := by
  linear_combination value_409 h H + ((60457706627437450172732037481 : ℝ) / 107586134162768353110510708801) * (scales0 h H) + ((101071459026990958765575291254 : ℝ) / 458237238100680022507730796745) * (scales1 h H)

theorem homothetic_410 (h : Assignment) (H : Constraints h) :
    h 102 2 = h 1 2 + ((26549542442343632698252807 : ℝ) / 50385731957741881798623444) * (h 3 0 - h 1 0) := by
  linear_combination value_410 h H + ((39547306060431870991147220801695 : ℝ) / 214598475610001941671098693821728) * (scales0 h H) + ((-45755861090415787045857375231177 : ℝ) / 80649753905719683961360620227120) * (scales1 h H)

theorem homothetic_411 (h : Assignment) (H : Constraints h) :
    h 102 3 = h 1 3 + ((-2986002101697047462905541 : ℝ) / 12596432989435470449655861) * (h 3 0 - h 1 0) := by
  linear_combination value_411 h H + ((-90522909293153379877888390004 : ℝ) / 394482491930150628071872598937) * (scales0 h H) + ((44404666411918119634893459450 : ℝ) / 1008121923821496049517007752839) * (scales1 h H)

theorem homothetic_412 (h : Assignment) (H : Constraints h) :
    h 103 0 = h 1 0 + ((2249625401621580903991093 : ℝ) / 2882437067905886100974294) * (h 3 0 - h 1 0) := by
  linear_combination value_412 h H + ((-308714914906482671272344739813 : ℝ) / 180538563311217270048423930396) * (scales0 h H) + ((23314774412723819810537136333987 : ℝ) / 3460322463464997675928125332590) * (scales1 h H)

theorem homothetic_413 (h : Assignment) (H : Constraints h) :
    h 103 1 = h 1 1 + ((98325468546266864931701 : ℝ) / 205888361993277578641021) * (h 3 0 - h 1 0) := by
  linear_combination value_413 h H + ((5452564667982460154700466654 : ℝ) / 6447805832543473930300854657) * (scales0 h H) + ((-220271233488555718042254873846 : ℝ) / 247165890247499833994866095185) * (scales1 h H)

theorem homothetic_414 (h : Assignment) (H : Constraints h) :
    h 103 2 = h 1 2 + ((12156889629218154062180811 : ℝ) / 23059496543247088807794352) * (h 3 0 - h 1 0) := by
  linear_combination value_414 h H + ((6036067200865735745129766329731 : ℝ) / 24553244610325548726585654533856) * (scales0 h H) + ((-22382570556429732277216213515633 : ℝ) / 27682579707719981407425002660720) * (scales1 h H)

theorem homothetic_415 (h : Assignment) (H : Constraints h) :
    h 103 3 = h 1 3 + ((-341832949651977221202207 : ℝ) / 1441218533952943050487147) * (h 3 0 - h 1 0) := by
  linear_combination value_415 h H + ((-3903285373919911398449457656 : ℝ) / 15044880275934772504035327533) * (scales0 h H) + ((55881888235985827100922492258 : ℝ) / 346032246346499767592812533259) * (scales1 h H)

theorem homothetic_416 (h : Assignment) (H : Constraints h) :
    h 104 0 = h 1 0 + ((252036929976259488883767 : ℝ) / 320543882331214009672076) * (h 3 0 - h 1 0) := by
  linear_combination value_416 h H + ((-77075308907547833268126965 : ℝ) / 198897478986518293001523158) * (scales0 h H) + ((2092699072455672553385462919 : ℝ) / 1345482946085270805598539010) * (scales1 h H)

theorem homothetic_417 (h : Assignment) (H : Constraints h) :
    h 104 1 = h 1 1 + ((37924673351107660395524 : ℝ) / 80135970582803502418019) * (h 3 0 - h 1 0) := by
  linear_combination value_417 h H + ((-13368408477046350206631803 : ℝ) / 99448739493259146500761579) * (scales0 h H) + ((1984243624967293010630333118 : ℝ) / 672741473042635402799269505) * (scales1 h H)

theorem homothetic_418 (h : Assignment) (H : Constraints h) :
    h 104 2 = h 1 2 + ((23261555189186827128125343 : ℝ) / 43593967997045105315402336) * (h 3 0 - h 1 0) := by
  linear_combination value_418 h H + ((-2372784085995988745127732027 : ℝ) / 27050057142166487848207149488) * (scales0 h H) + ((142897503207460818934830522091 : ℝ) / 182985680667596829561401305360) * (scales1 h H)

theorem homothetic_419 (h : Assignment) (H : Constraints h) :
    h 104 3 = h 1 3 + ((-19011358777051563159879 : ℝ) / 80135970582803502418019) * (h 3 0 - h 1 0) := by
  linear_combination value_419 h H + ((-1591472348546978811637752 : ℝ) / 5849925852544655676515387) * (scales0 h H) + ((141879948728109196051564326 : ℝ) / 672741473042635402799269505) * (scales1 h H)

theorem homothetic_420 (h : Assignment) (H : Constraints h) :
    h 105 0 = h 1 0 + ((6771655532286104264962343 : ℝ) / 8706300919230256219546134) * (h 3 0 - h 1 0) := by
  linear_combination value_420 h H + ((-1263524282708508219959261271881 : ℝ) / 545310451775067868055052556956) * (scales0 h H) + ((31762477745279768535251075617161 : ℝ) / 3483927886340711379240613558330) * (scales1 h H)

theorem homothetic_421 (h : Assignment) (H : Constraints h) :
    h 105 1 = h 1 1 + ((2047002871184314068251267 : ℝ) / 4353150459615128109773067) * (h 3 0 - h 1 0) := by
  linear_combination value_421 h H + ((-111861372200933191332754672990 : ℝ) / 136327612943766967013763139239) * (scales0 h H) + ((1964305101213638443870359895770 : ℝ) / 348392788634071137924061355833) * (scales1 h H)

theorem homothetic_422 (h : Assignment) (H : Constraints h) :
    h 105 2 = h 1 2 + ((12402523337509070551825067 : ℝ) / 23216802451280683252123024) * (h 3 0 - h 1 0) := by
  linear_combination value_422 h H + ((1252121310167180136020707511333 : ℝ) / 24720740480469743351829049248672) * (scales0 h H) + ((6652508824964705013858403487333 : ℝ) / 27871423090725691033924908466640) * (scales1 h H)

theorem homothetic_423 (h : Assignment) (H : Constraints h) :
    h 105 3 = h 1 3 + ((-344918463589651164188249 : ℝ) / 1451050153205042703257689) * (h 3 0 - h 1 0) := by
  linear_combination value_423 h H + ((-17152950526243690493712896468 : ℝ) / 45442537647922322337921046413) * (scales0 h H) + ((1086975051893597234230446355038 : ℝ) / 1741963943170355689620306779165) * (scales1 h H)

theorem homothetic_424 (h : Assignment) (H : Constraints h) :
    h 106 0 = h 1 0 + ((59446036744140026258008847 : ℝ) / 75578597936612822697935166) * (h 3 0 - h 1 0) := by
  linear_combination value_424 h H + ((-1547308847835853480810011144365 : ℝ) / 4733789903161807536862471187244) * (scales0 h H) + ((13283879343489716995631629035751 : ℝ) / 10081219238214960495170077528390) * (scales1 h H)

theorem homothetic_425 (h : Assignment) (H : Constraints h) :
    h 106 1 = h 1 1 + ((17999741293728835263788678 : ℝ) / 37789298968306411348967583) * (h 3 0 - h 1 0) := by
  linear_combination value_425 h H + ((60457706627437450172732037481 : ℝ) / 107586134162768353110510708801) * (scales0 h H) + ((101071459026990958765575291254 : ℝ) / 458237238100680022507730796745) * (scales1 h H)

theorem homothetic_426 (h : Assignment) (H : Constraints h) :
    h 106 2 = h 1 2 + ((6722163842805085176374758 : ℝ) / 12596432989435470449655861) * (h 3 0 - h 1 0) := by
  linear_combination value_426 h H + ((-15878106154893252875550704693249 : ℝ) / 214598475610001941671098693821728) * (scales0 h H) + ((58642307420003998916173317639071 : ℝ) / 80649753905719683961360620227120) * (scales1 h H)

theorem homothetic_427 (h : Assignment) (H : Constraints h) :
    h 106 3 = h 1 3 + ((-2986002101697047462905541 : ℝ) / 12596432989435470449655861) * (h 3 0 - h 1 0) := by
  linear_combination value_427 h H + ((-90522909293153379877888390004 : ℝ) / 394482491930150628071872598937) * (scales0 h H) + ((44404666411918119634893459450 : ℝ) / 1008121923821496049517007752839) * (scales1 h H)

theorem homothetic_428 (h : Assignment) (H : Constraints h) :
    h 107 0 = h 1 0 + ((2249625401621580903991093 : ℝ) / 2882437067905886100974294) * (h 3 0 - h 1 0) := by
  linear_combination value_428 h H + ((-308714914906482671272344739813 : ℝ) / 180538563311217270048423930396) * (scales0 h H) + ((23314774412723819810537136333987 : ℝ) / 3460322463464997675928125332590) * (scales1 h H)

theorem homothetic_429 (h : Assignment) (H : Constraints h) :
    h 107 1 = h 1 1 + ((98325468546266864931701 : ℝ) / 205888361993277578641021) * (h 3 0 - h 1 0) := by
  linear_combination value_429 h H + ((5452564667982460154700466654 : ℝ) / 6447805832543473930300854657) * (scales0 h H) + ((-220271233488555718042254873846 : ℝ) / 247165890247499833994866095185) * (scales1 h H)

theorem homothetic_430 (h : Assignment) (H : Constraints h) :
    h 107 2 = h 1 2 + ((12316610350697746404987691 : ℝ) / 23059496543247088807794352) * (h 3 0 - h 1 0) := by
  linear_combination value_430 h H + ((788878170848256898961871452059 : ℝ) / 24553244610325548726585654533856) * (scales0 h H) + ((8616662827913348872128545373959 : ℝ) / 27682579707719981407425002660720) * (scales1 h H)

theorem homothetic_431 (h : Assignment) (H : Constraints h) :
    h 107 3 = h 1 3 + ((-341832949651977221202207 : ℝ) / 1441218533952943050487147) * (h 3 0 - h 1 0) := by
  linear_combination value_431 h H + ((-3903285373919911398449457656 : ℝ) / 15044880275934772504035327533) * (scales0 h H) + ((55881888235985827100922492258 : ℝ) / 346032246346499767592812533259) * (scales1 h H)

theorem homothetic_432 (h : Assignment) (H : Constraints h) :
    h 108 0 = h 1 0 + ((2216361114449715196637 : ℝ) / 2817675848811241707508) * (h 3 0 - h 1 0) := by
  linear_combination value_432 h H + ((-621191793265828350363 : ℝ) / 1408837924405620853754) * (scales0 h H) + ((58850120629217951428689 : ℝ) / 32403272261329279636342) * (scales1 h H)

theorem homothetic_433 (h : Assignment) (H : Constraints h) :
    h 108 1 = h 1 1 + ((330874999755796998347 : ℝ) / 704418962202810426877) * (h 3 0 - h 1 0) := by
  linear_combination value_433 h H + ((331031354045269445631 : ℝ) / 704418962202810426877) * (scales0 h H) + ((-143533237735706606712 : ℝ) / 81008180653323199090855) * (scales1 h H)

theorem homothetic_434 (h : Assignment) (H : Constraints h) :
    h 108 2 = h 1 2 + ((11748196884205232413579 : ℝ) / 22541406790489933660064) * (h 3 0 - h 1 0) := by
  linear_combination value_434 h H + ((234599035402598809246983 : ℝ) / 191601957719164436110544) * (scales0 h H) + ((-7275925541890134021504321 : ℝ) / 1296130890453171185453680) * (scales1 h H)

theorem homothetic_435 (h : Assignment) (H : Constraints h) :
    h 108 3 = h 1 3 + ((-167203354786906476873 : ℝ) / 704418962202810426877) * (h 3 0 - h 1 0) := by
  linear_combination value_435 h H + ((-176638774353111342216 : ℝ) / 704418962202810426877) * (scales0 h H) + ((8661715161776066384874 : ℝ) / 81008180653323199090855) * (scales1 h H)

theorem homothetic_436 (h : Assignment) (H : Constraints h) :
    h 109 0 = h 1 0 + ((286686793470506661255 : ℝ) / 383925890024880989014) * (h 3 0 - h 1 0) := by
  linear_combination value_436 h H + ((4764387564147266187978403 : ℝ) / 9552843995599088768646348) * (scales0 h H) + ((-1099135286985820856325509673 : ℝ) / 183096176582315868065721670) * (scales1 h H)

theorem homothetic_437 (h : Assignment) (H : Constraints h) :
    h 109 1 = h 1 1 + ((86609735132826034823 : ℝ) / 191962945012440494507) * (h 3 0 - h 1 0) := by
  linear_combination value_437 h H + ((166581903158374989068243 : ℝ) / 183708538376905553243199) * (scales0 h H) + ((-25611094310695704965245392 : ℝ) / 7042160637781379540989295) * (scales1 h H)

theorem homothetic_438 (h : Assignment) (H : Constraints h) :
    h 109 2 = h 1 2 + ((1582787225885989341909 : ℝ) / 3071407120199047912112) * (h 3 0 - h 1 0) := by
  linear_combination value_438 h H + ((136151565219732618160718185 : ℝ) / 99937444877036620964300256) * (scales0 h H) + ((-761857510174688672583148287 : ℝ) / 112674570204502072655828720) * (scales1 h H)

theorem homothetic_439 (h : Assignment) (H : Constraints h) :
    h 109 3 = h 1 3 + ((-46015588008359398443 : ℝ) / 191962945012440494507) * (h 3 0 - h 1 0) := by
  linear_combination value_439 h H + ((-5364791332306573317908 : ℝ) / 27450701136778990714501) * (scales0 h H) + ((-1115771857151937365366838 : ℝ) / 3156830630729583932167615) * (scales1 h H)

theorem homothetic_440 (h : Assignment) (H : Constraints h) :
    h 110 0 = h 1 0 + ((2734596386369016255457 : ℝ) / 3471977861194796794530) * (h 3 0 - h 1 0) := by
  linear_combination value_440 h H + ((-1385622525909000961769227 : ℝ) / 2978957004905135649706740) * (scales0 h H) + ((12800136748644181407158081 : ℝ) / 6344075103038714809560650) * (scales1 h H)

theorem homothetic_441 (h : Assignment) (H : Constraints h) :
    h 110 1 = h 1 1 + ((830968579220254654811 : ℝ) / 1735988930597398397265) * (h 3 0 - h 1 0) := by
  linear_combination value_441 h H + ((17521231134939615422497 : ℝ) / 67703568293298537493335) * (scales0 h H) + ((22006194672091771648456 : ℝ) / 12537697832092321758025) * (scales1 h H)

theorem homothetic_442 (h : Assignment) (H : Constraints h) :
    h 110 2 = h 1 2 + ((14397052723137184347689 : ℝ) / 27775822889558374356240) * (h 3 0 - h 1 0) := by
  linear_combination value_442 h H + ((523293629333666712175409207 : ℝ) / 405138152667098448360116640) * (scales0 h H) + ((-13621661665825553968696411 : ℝ) / 2206634818448248629412400) * (scales1 h H)

theorem homothetic_443 (h : Assignment) (H : Constraints h) :
    h 110 3 = h 1 3 + ((-411046245289316342401 : ℝ) / 1735988930597398397265) * (h 3 0 - h 1 0) := by
  linear_combination value_443 h H + ((-197004103519997441171332 : ℝ) / 744739251226283912426685) * (scales0 h H) + ((702618985889944829564302 : ℝ) / 3172037551519357404780325) * (scales1 h H)

theorem homothetic_444 (h : Assignment) (H : Constraints h) :
    h 111 0 = h 1 0 + ((1349016979335012821116111 : ℝ) / 1778095668256457615808738) * (h 3 0 - h 1 0) := by
  linear_combination value_444 h H + ((30068092897903049031194683 : ℝ) / 138691462124003694033081564) * (scales0 h H) + ((-3240347762322562893878199039 : ℝ) / 886084341347801378544687770) * (scales1 h H)

theorem homothetic_445 (h : Assignment) (H : Constraints h) :
    h 111 1 = h 1 1 + ((432259550897862671942509 : ℝ) / 889047834128228807904369) * (h 3 0 - h 1 0) := by
  linear_combination value_445 h H + ((216658346801724741898271 : ℝ) / 2667143502384686423713107) * (scales0 h H) + ((110172271200970053940784112 : ℝ) / 34080166974915437636334145) * (scales1 h H)

theorem homothetic_446 (h : Assignment) (H : Constraints h) :
    h 111 2 = h 1 2 + ((2438632638476828853507479 : ℝ) / 4741588448683886975489968) * (h 3 0 - h 1 0) := by
  linear_combination value_446 h H + ((223518282605868375278937481 : ℝ) / 161214007255252157166658912) * (scales0 h H) + ((-759265773647343449002289253 : ℝ) / 109056534319729400436269264) * (scales1 h H)

theorem homothetic_447 (h : Assignment) (H : Constraints h) :
    h 111 3 = h 1 3 + ((-70309348935659297530543 : ℝ) / 296349278042742935968123) * (h 3 0 - h 1 0) := by
  linear_combination value_447 h H + ((-2928643917064840870245608 : ℝ) / 11557621843666974502756797) * (scales0 h H) + ((57093268423683249565655886 : ℝ) / 443042170673900689272343885) * (scales1 h H)

theorem homothetic_448 (h : Assignment) (H : Constraints h) :
    h 112 0 = h 1 0 + ((2216361114449715196637 : ℝ) / 2817675848811241707508) * (h 3 0 - h 1 0) := by
  linear_combination value_448 h H + ((-621191793265828350363 : ℝ) / 1408837924405620853754) * (scales0 h H) + ((58850120629217951428689 : ℝ) / 32403272261329279636342) * (scales1 h H)

theorem homothetic_449 (h : Assignment) (H : Constraints h) :
    h 112 1 = h 1 1 + ((330874999755796998347 : ℝ) / 704418962202810426877) * (h 3 0 - h 1 0) := by
  linear_combination value_449 h H + ((331031354045269445631 : ℝ) / 704418962202810426877) * (scales0 h H) + ((-143533237735706606712 : ℝ) / 81008180653323199090855) * (scales1 h H)

theorem homothetic_450 (h : Assignment) (H : Constraints h) :
    h 112 2 = h 1 2 + ((12145691892412362678483 : ℝ) / 22541406790489933660064) * (h 3 0 - h 1 0) := by
  linear_combination value_450 h H + ((-187564067094409291744857 : ℝ) / 191601957719164436110544) * (scales0 h H) + ((6652957375333667859130279 : ℝ) / 1296130890453171185453680) * (scales1 h H)

theorem homothetic_451 (h : Assignment) (H : Constraints h) :
    h 112 3 = h 1 3 + ((-167203354786906476873 : ℝ) / 704418962202810426877) * (h 3 0 - h 1 0) := by
  linear_combination value_451 h H + ((-176638774353111342216 : ℝ) / 704418962202810426877) * (scales0 h H) + ((8661715161776066384874 : ℝ) / 81008180653323199090855) * (scales1 h H)

theorem homothetic_452 (h : Assignment) (H : Constraints h) :
    h 113 0 = h 1 0 + ((286686793470506661255 : ℝ) / 383925890024880989014) * (h 3 0 - h 1 0) := by
  linear_combination value_452 h H + ((4764387564147266187978403 : ℝ) / 9552843995599088768646348) * (scales0 h H) + ((-1099135286985820856325509673 : ℝ) / 183096176582315868065721670) * (scales1 h H)

theorem homothetic_453 (h : Assignment) (H : Constraints h) :
    h 113 1 = h 1 1 + ((86609735132826034823 : ℝ) / 191962945012440494507) * (h 3 0 - h 1 0) := by
  linear_combination value_453 h H + ((166581903158374989068243 : ℝ) / 183708538376905553243199) * (scales0 h H) + ((-25611094310695704965245392 : ℝ) / 7042160637781379540989295) * (scales1 h H)

theorem homothetic_454 (h : Assignment) (H : Constraints h) :
    h 113 2 = h 1 2 + ((1682925609258774509813 : ℝ) / 3071407120199047912112) * (h 3 0 - h 1 0) := by
  linear_combination value_454 h H + ((-1550956070874721031953414451 : ℝ) / 1299186783401476072535903328) * (scales0 h H) + ((2027499983276597232863586913 : ℝ) / 292953882531705388905154672) * (scales1 h H)

theorem homothetic_455 (h : Assignment) (H : Constraints h) :
    h 113 3 = h 1 3 + ((-46015588008359398443 : ℝ) / 191962945012440494507) * (h 3 0 - h 1 0) := by
  linear_combination value_455 h H + ((-5364791332306573317908 : ℝ) / 27450701136778990714501) * (scales0 h H) + ((-1115771857151937365366838 : ℝ) / 3156830630729583932167615) * (scales1 h H)

theorem homothetic_456 (h : Assignment) (H : Constraints h) :
    h 114 0 = h 1 0 + ((2734596386369016255457 : ℝ) / 3471977861194796794530) * (h 3 0 - h 1 0) := by
  linear_combination value_456 h H + ((-1385622525909000961769227 : ℝ) / 2978957004905135649706740) * (scales0 h H) + ((12800136748644181407158081 : ℝ) / 6344075103038714809560650) * (scales1 h H)

theorem homothetic_457 (h : Assignment) (H : Constraints h) :
    h 114 1 = h 1 1 + ((830968579220254654811 : ℝ) / 1735988930597398397265) * (h 3 0 - h 1 0) := by
  linear_combination value_457 h H + ((17521231134939615422497 : ℝ) / 67703568293298537493335) * (scales0 h H) + ((22006194672091771648456 : ℝ) / 12537697832092321758025) * (scales1 h H)

theorem homothetic_458 (h : Assignment) (H : Constraints h) :
    h 114 2 = h 1 2 + ((1669936793920543509701 : ℝ) / 3086202543284263817360) * (h 3 0 - h 1 0) := by
  linear_combination value_458 h H + ((-46486447366095334287530017 : ℝ) / 45015350296344272040012960) * (scales0 h H) + ((283211757137194707396627787 : ℝ) / 50752600824309718476485200) * (scales1 h H)

theorem homothetic_459 (h : Assignment) (H : Constraints h) :
    h 114 3 = h 1 3 + ((-411046245289316342401 : ℝ) / 1735988930597398397265) * (h 3 0 - h 1 0) := by
  linear_combination value_459 h H + ((-197004103519997441171332 : ℝ) / 744739251226283912426685) * (scales0 h H) + ((702618985889944829564302 : ℝ) / 3172037551519357404780325) * (scales1 h H)

theorem homothetic_460 (h : Assignment) (H : Constraints h) :
    h 115 0 = h 1 0 + ((1349016979335012821116111 : ℝ) / 1778095668256457615808738) * (h 3 0 - h 1 0) := by
  linear_combination value_460 h H + ((30068092897903049031194683 : ℝ) / 138691462124003694033081564) * (scales0 h H) + ((-3240347762322562893878199039 : ℝ) / 886084341347801378544687770) * (scales1 h H)

theorem homothetic_461 (h : Assignment) (H : Constraints h) :
    h 115 1 = h 1 1 + ((432259550897862671942509 : ℝ) / 889047834128228807904369) * (h 3 0 - h 1 0) := by
  linear_combination value_461 h H + ((216658346801724741898271 : ℝ) / 2667143502384686423713107) * (scales0 h H) + ((110172271200970053940784112 : ℝ) / 34080166974915437636334145) * (scales1 h H)

theorem homothetic_462 (h : Assignment) (H : Constraints h) :
    h 115 2 = h 1 2 + ((2598353359956421196314359 : ℝ) / 4741588448683886975489968) * (h 3 0 - h 1 0) := by
  linear_combination value_462 h H + ((-2504841805677907691351358515 : ℝ) / 2095782094318278043166565856) * (scales0 h H) + ((2136610258052710525485324533 : ℝ) / 308203249164452653406847920) * (scales1 h H)

theorem homothetic_463 (h : Assignment) (H : Constraints h) :
    h 115 3 = h 1 3 + ((-70309348935659297530543 : ℝ) / 296349278042742935968123) * (h 3 0 - h 1 0) := by
  linear_combination value_463 h H + ((-2928643917064840870245608 : ℝ) / 11557621843666974502756797) * (scales0 h H) + ((57093268423683249565655886 : ℝ) / 443042170673900689272343885) * (scales1 h H)

theorem homothetic_464 (h : Assignment) (H : Constraints h) :
    h 116 0 = h 1 0 + ((102710259697434411157310306897 : ℝ) / 130702110222853351103674774444) * (h 3 0 - h 1 0) := by
  linear_combination value_464 h H + ((-2061667070398959704986122573 : ℝ) / 4216197103963011325924992724) * (scales0 h H) + ((134213750884978747507484829423 : ℝ) / 65351055111426675551837387222) * (scales1 h H)

theorem homothetic_465 (h : Assignment) (H : Constraints h) :
    h 116 1 = h 1 1 + ((15520612305655146664685015750 : ℝ) / 32675527555713337775918693611) * (h 3 0 - h 1 0) := by
  linear_combination value_465 h H + ((276705677359406646865889340 : ℝ) / 1054049275990752831481248181) * (scales0 h H) + ((32673708890913507468542806734 : ℝ) / 32675527555713337775918693611) * (scales1 h H)

theorem homothetic_466 (h : Assignment) (H : Constraints h) :
    h 116 2 = h 1 2 + ((550094978867967299599421436073 : ℝ) / 1045616881782826808829398195552) * (h 3 0 - h 1 0) := by
  linear_combination value_466 h H + ((-181991951077660052977278309 : ℝ) / 33729576831704090607399941792) * (scales0 h H) + ((208182836301821096045651822331 : ℝ) / 522808440891413404414699097776) * (scales1 h H)

theorem homothetic_467 (h : Assignment) (H : Constraints h) :
    h 116 3 = h 1 3 + ((-7749326945362260727376169663 : ℝ) / 32675527555713337775918693611) * (h 3 0 - h 1 0) := by
  linear_combination value_467 h H + ((-267782522729277245542412112 : ℝ) / 1054049275990752831481248181) * (scales0 h H) + ((4002714589940938903161736386 : ℝ) / 32675527555713337775918693611) * (scales1 h H)

theorem homothetic_468 (h : Assignment) (H : Constraints h) :
    h 117 0 = h 1 0 + ((2559485950430847862138819501 : ℝ) / 3262316970720903125342558132) * (h 3 0 - h 1 0) := by
  linear_combination value_468 h H + ((-2496476032402122435583484089 : ℝ) / 3262316970720903125342558132) * (scales0 h H) + ((896822506056033586189872729 : ℝ) / 1631158485360451562671279066) * (scales1 h H)

theorem homothetic_469 (h : Assignment) (H : Constraints h) :
    h 117 1 = h 1 1 + ((386933626973084057587048918 : ℝ) / 815579242680225781335639533) * (h 3 0 - h 1 0) := by
  linear_combination value_469 h H + ((1258016102176186967585787260 : ℝ) / 8971371669482483594692034863) * (scales0 h H) + ((2998253794527737665871750838 : ℝ) / 8971371669482483594692034863) * (scales1 h H)

theorem homothetic_470 (h : Assignment) (H : Constraints h) :
    h 117 2 = h 1 2 + ((13732829524213089535259041889 : ℝ) / 26098535765767225002740465056) * (h 3 0 - h 1 0) := by
  linear_combination value_470 h H + ((4393522730936721890853175693 : ℝ) / 287083893423439475030145115616) * (scales0 h H) + ((73333801017703631498498142543 : ℝ) / 143541946711719737515072557808) * (scales1 h H)

theorem homothetic_471 (h : Assignment) (H : Constraints h) :
    h 117 3 = h 1 3 + ((-193484426833554591124006800 : ℝ) / 815579242680225781335639533) * (h 3 0 - h 1 0) := by
  linear_combination value_471 h H + ((-2426322943114626526678742106 : ℝ) / 8971371669482483594692034863) * (scales0 h H) + ((297994247945526024314667306 : ℝ) / 8971371669482483594692034863) * (scales1 h H)

theorem homothetic_472 (h : Assignment) (H : Constraints h) :
    h 118 0 = h 1 0 + ((815352184629613741817890564765 : ℝ) / 1037509863370409750592837102046) * (h 3 0 - h 1 0) := by
  linear_combination value_472 h H + ((-7559445924796185584949116101 : ℝ) / 16734030054361447590207050033) * (scales0 h H) + ((970664285983757617368809643177 : ℝ) / 518754931685204875296418551023) * (scales1 h H)

theorem homothetic_473 (h : Assignment) (H : Constraints h) :
    h 118 1 = h 1 1 + ((246573827856610733773743225345 : ℝ) / 518754931685204875296418551023) * (h 3 0 - h 1 0) := by
  linear_combination value_473 h H + ((9558511743461862457300452295 : ℝ) / 16734030054361447590207050033) * (scales0 h H) + ((-266286651705594267031295217288 : ℝ) / 518754931685204875296418551023) * (scales1 h H)

theorem homothetic_474 (h : Assignment) (H : Constraints h) :
    h 118 2 = h 1 2 + ((4366642872826104676091635747493 : ℝ) / 8300078906963278004742696816368) * (h 3 0 - h 1 0) := by
  linear_combination value_474 h H + ((-667303820618086860916687133 : ℝ) / 133872240434891580721656400264) * (scales0 h H) + ((1644188391755857818182070777339 : ℝ) / 4150039453481639002371348408184) * (scales1 h H)

theorem homothetic_475 (h : Assignment) (H : Constraints h) :
    h 118 3 = h 1 3 + ((-123017280524935410449489547363 : ℝ) / 518754931685204875296418551023) * (h 3 0 - h 1 0) := by
  linear_combination value_475 h H + ((-3927477000029399601288710976 : ℝ) / 16734030054361447590207050033) * (scales0 h H) + ((14335061367662622798576402618 : ℝ) / 518754931685204875296418551023) * (scales1 h H)

theorem homothetic_476 (h : Assignment) (H : Constraints h) :
    h 119 0 = h 1 0 + ((38372687645216636315735202943 : ℝ) / 48883993910614956372884063634) * (h 3 0 - h 1 0) := by
  linear_combination value_476 h H + ((-2231362585778583771038978354791 : ℝ) / 3764067531117351640712072899818) * (scales0 h H) + ((236998667223818854439752680264 : ℝ) / 627344588519558606785345483303) * (scales1 h H)

theorem homothetic_477 (h : Assignment) (H : Constraints h) :
    h 119 1 = h 1 1 + ((1660479031129104979232793601 : ℝ) / 3491713850758211169491718831) * (h 3 0 - h 1 0) := by
  linear_combination value_477 h H + ((14842406749753798300221437215 : ℝ) / 24441996955307478186442031817) * (scales0 h H) + ((-1073017843950021148530627336 : ℝ) / 8147332318435826062147343939) * (scales1 h H)

theorem homothetic_478 (h : Assignment) (H : Constraints h) :
    h 119 2 = h 1 2 + ((68590219495914303247941647397 : ℝ) / 130357317094973216994357503024) * (h 3 0 - h 1 0) := by
  linear_combination value_478 h H + ((66893936986311160142107637049 : ℝ) / 10037513416312937708565527732848) * (scales0 h H) + ((651819120524886273743674901565 : ℝ) / 1254689177039117213570690966606) * (scales1 h H)

theorem homothetic_479 (h : Assignment) (H : Constraints h) :
    h 119 3 = h 1 3 + ((-1932189183592177483300578859 : ℝ) / 8147332318435826062147343939) * (h 3 0 - h 1 0) := by
  linear_combination value_479 h H + ((-148866993062121542009973162791 : ℝ) / 627344588519558606785345483303) * (scales0 h H) + ((88425925523875795828590648 : ℝ) / 627344588519558606785345483303) * (scales1 h H)

theorem homothetic_480 (h : Assignment) (H : Constraints h) :
    h 120 0 = h 1 0 + ((57117792398369718875735622862 : ℝ) / 72674441298858640087278575651) * (h 3 0 - h 1 0) := by
  linear_combination value_480 h H + ((-35551202651472366183311254002 : ℝ) / 72674441298858640087278575651) * (scales0 h H) + ((149303068254927490314397680882 : ℝ) / 72674441298858640087278575651) * (scales1 h H)

theorem homothetic_481 (h : Assignment) (H : Constraints h) :
    h 120 1 = h 1 1 + ((34489688017312440758442635101 : ℝ) / 72674441298858640087278575651) * (h 3 0 - h 1 0) := by
  linear_combination value_481 h H + ((19134279502130384499223111215 : ℝ) / 72674441298858640087278575651) * (scales0 h H) + ((72478632673303706561023043496 : ℝ) / 72674441298858640087278575651) * (scales1 h H)

theorem homothetic_482 (h : Assignment) (H : Constraints h) :
    h 120 2 = h 1 2 + ((310361656748375544205985042169 : ℝ) / 581395530390869120698228605208) * (h 3 0 - h 1 0) := by
  linear_combination value_482 h H + ((-11499865489163555859586557291 : ℝ) / 581395530390869120698228605208) * (scales0 h H) + ((130070925129166839427359717251 : ℝ) / 290697765195434560349114302604) * (scales1 h H)

theorem homothetic_483 (h : Assignment) (H : Constraints h) :
    h 120 3 = h 1 3 + ((-17236832104620269945525241231 : ℝ) / 72674441298858640087278575651) * (h 3 0 - h 1 0) := by
  linear_combination value_483 h H + ((-18460491794733377438954686152 : ℝ) / 72674441298858640087278575651) * (scales0 h H) + ((8893840324418822981414494530 : ℝ) / 72674441298858640087278575651) * (scales1 h H)

theorem homothetic_484 (h : Assignment) (H : Constraints h) :
    h 121 0 = h 1 0 + ((1771507616629943951493344 : ℝ) / 2265443339121149296656307) * (h 3 0 - h 1 0) := by
  linear_combination value_484 h H + ((-18914006173254357364399801 : ℝ) / 24919876730332642263219377) * (scales0 h H) + ((13480713225851098567607208 : ℝ) / 24919876730332642263219377) * (scales1 h H)

theorem homothetic_485 (h : Assignment) (H : Constraints h) :
    h 121 1 = h 1 1 + ((7498087158674464836866999 : ℝ) / 15858103373848045076594149) * (h 3 0 - h 1 0) := by
  linear_combination value_485 h H + ((25136204748906855536985625 : ℝ) / 174439137112328495842535639) * (scales0 h H) + ((57342753996512257668551364 : ℝ) / 174439137112328495842535639) * (scales1 h H)

theorem homothetic_486 (h : Assignment) (H : Constraints h) :
    h 121 2 = h 1 2 + ((9679039782173769529790013 : ℝ) / 18123546712969194373250456) * (h 3 0 - h 1 0) := by
  linear_combination value_486 h H + ((-734066461754127170845303 : ℝ) / 199359013842661138105755016) * (scales0 h H) + ((53601752032832795999267723 : ℝ) / 99679506921330569052877508) * (scales1 h H)

theorem homothetic_487 (h : Assignment) (H : Constraints h) :
    h 121 3 = h 1 3 + ((-3764940308545379251029699 : ℝ) / 15858103373848045076594149) * (h 3 0 - h 1 0) := by
  linear_combination value_487 h H + ((-47102140364334606424138497 : ℝ) / 174439137112328495842535639) * (scales0 h H) + ((5687796970335434662811808 : ℝ) / 174439137112328495842535639) * (scales1 h H)

theorem homothetic_488 (h : Assignment) (H : Constraints h) :
    h 122 0 = h 1 0 + ((226662826025668122197608848679 : ℝ) / 288351569402810574529240132192) * (h 3 0 - h 1 0) := by
  linear_combination value_488 h H + ((-65177204861032671336070632337 : ℝ) / 144175784701405287264620066096) * (scales0 h H) + ((269928922810662604454177689353 : ℝ) / 144175784701405287264620066096) * (scales1 h H)

theorem homothetic_489 (h : Assignment) (H : Constraints h) :
    h 122 1 = h 1 1 + ((137140387230205721936245456467 : ℝ) / 288351569402810574529240132192) * (h 3 0 - h 1 0) := by
  linear_combination value_489 h H + ((82283379966487451553853467115 : ℝ) / 144175784701405287264620066096) * (scales0 h H) + ((-73776641543489070940041714339 : ℝ) / 144175784701405287264620066096) * (scales1 h H)

theorem homothetic_490 (h : Assignment) (H : Constraints h) :
    h 122 2 = h 1 2 + ((2462877092205180514685636204021 : ℝ) / 4613625110444969192467842115072) * (h 3 0 - h 1 0) := by
  linear_combination value_490 h H + ((-42166173460266371485150710067 : ℝ) / 2306812555222484596233921057536) * (scales0 h H) + ((1015175603829028825047716757755 : ℝ) / 2306812555222484596233921057536) * (scales1 h H)

theorem homothetic_491 (h : Assignment) (H : Constraints h) :
    h 122 3 = h 1 3 + ((-17093090215749250446173900913 : ℝ) / 72087892350702643632310033048) * (h 3 0 - h 1 0) := by
  linear_combination value_491 h H + ((-8461058739252797992854231153 : ℝ) / 36043946175351321816155016524) * (scales0 h H) + ((1001121979882274265817398609 : ℝ) / 36043946175351321816155016524) * (scales1 h H)

theorem homothetic_492 (h : Assignment) (H : Constraints h) :
    h 123 0 = h 1 0 + ((25999589691916191252747115 : ℝ) / 33194360854270403463010278) * (h 3 0 - h 1 0) := by
  linear_combination value_492 h H + ((-1076063047865449966450768109 : ℝ) / 1825689846984872190465565290) * (scales0 h H) + ((113391772322661382481049024 : ℝ) / 304281641164145365077594215) * (scales1 h H)

theorem homothetic_493 (h : Assignment) (H : Constraints h) :
    h 123 1 = h 1 1 + ((15811069717464985005318455 : ℝ) / 33194360854270403463010278) * (h 3 0 - h 1 0) := by
  linear_combination value_493 h H + ((100533724833727662965881243 : ℝ) / 165971804271352017315051390) * (scales0 h H) + ((-3579729374400456323214828 : ℝ) / 27661967378558669552508565) * (scales1 h H)

theorem homothetic_494 (h : Assignment) (H : Constraints h) :
    h 123 2 = h 1 2 + ((94541007463441608255985705 : ℝ) / 177036591222775485136054816) * (h 3 0 - h 1 0) := by
  linear_combination value_494 h H + ((-86306860777438791550635177 : ℝ) / 9737012517252651682483014880) * (scales0 h H) + ((660757783908340905703731119 : ℝ) / 1217126564656581460310376860) * (scales1 h H)

theorem homothetic_495 (h : Assignment) (H : Constraints h) :
    h 123 3 = h 1 3 + ((-1312098045054627791910868 : ℝ) / 5532393475711733910501713) * (h 3 0 - h 1 0) := by
  linear_combination value_495 h H + ((-14439774503848767519240428 : ℝ) / 60856328232829073015518843) * (scales0 h H) + ((6696008247861808220880 : ℝ) / 60856328232829073015518843) * (scales1 h H)

theorem homothetic_496 (h : Assignment) (H : Constraints h) :
    h 124 0 = h 1 0 + ((100340131284208498460027 : ℝ) / 120188033356954996197700) * (h 3 0 - h 1 0) := by
  linear_combination value_496 h H + ((16401952160911844438037 : ℝ) / 168725508366494513892925) * (scales0 h H) + ((-480774751631741289653908389 : ℝ) / 504489270015818596539845750) * (scales1 h H)

theorem homothetic_497 (h : Assignment) (H : Constraints h) :
    h 124 1 = h 1 1 + ((113794235583827978925919 : ℝ) / 240376066713909992395400) * (h 3 0 - h 1 0) := by
  linear_combination value_497 h H + ((-58023053356334461018911 : ℝ) / 337451016732989027785850) * (scales0 h H) + ((3161039314271773420806596667 : ℝ) / 1008978540031637193079691500) * (scales1 h H)

theorem homothetic_498 (h : Assignment) (H : Constraints h) :
    h 124 2 = h 1 2 + ((934816436068939411244123 : ℝ) / 1923008533711279939163200) * (h 3 0 - h 1 0) := by
  linear_combination value_498 h H + ((-18019105745549530002971079 : ℝ) / 45893338275686507778875600) * (scales0 h H) + ((19414839583517363453450513439 : ℝ) / 8071828320253097544637532000) * (scales1 h H)

theorem homothetic_499 (h : Assignment) (H : Constraints h) :
    h 124 3 = h 1 3 + ((-12759751460028199206351 : ℝ) / 60094016678477498098850) * (h 3 0 - h 1 0) := by
  linear_combination value_499 h H + ((9833358418001256641538 : ℝ) / 168725508366494513892925) * (scales0 h H) + ((-372304208406275240464072143 : ℝ) / 252244635007909298269922875) * (scales1 h H)

theorem homothetic_500 (h : Assignment) (H : Constraints h) :
    h 125 0 = h 1 0 + ((37945283165796075729259 : ℝ) / 47944807999223844799935) * (h 3 0 - h 1 0) := by
  linear_combination value_500 h H + ((-33569999458194540553426690 : ℝ) / 20299831706871375888292479) * (scales0 h H) + ((154529642813639551120678656 : ℝ) / 19952826036668446385928505) * (scales1 h H)

theorem homothetic_501 (h : Assignment) (H : Constraints h) :
    h 125 1 = h 1 1 + ((22643664462472705843084 : ℝ) / 47944807999223844799935) * (h 3 0 - h 1 0) := by
  linear_combination value_501 h H + ((-4402962579002190800932531 : ℝ) / 20299831706871375888292479) * (scales0 h H) + ((13393165800162739382713734 : ℝ) / 3990565207333689277185701) * (scales1 h H)

theorem homothetic_502 (h : Assignment) (H : Constraints h) :
    h 125 2 = h 1 2 + ((22443927884827818480627 : ℝ) / 42617607110421195377720) * (h 3 0 - h 1 0) := by
  linear_combination value_502 h H + ((380670708372338388420360203 : ℝ) / 306753012459389680089753016) * (scales0 h H) + ((-455697671901342475194376641 : ℝ) / 79811304146673785543714020) * (scales1 h H)

theorem homothetic_503 (h : Assignment) (H : Constraints h) :
    h 125 3 = h 1 3 + ((-11268276397206178816139 : ℝ) / 47944807999223844799935) * (h 3 0 - h 1 0) := by
  linear_combination value_503 h H + ((-599816457482315935619492 : ℝ) / 699994196788668134079051) * (scales0 h H) + ((2112356982453003366864414 : ℝ) / 688028484023049875376845) * (scales1 h H)

theorem homothetic_504 (h : Assignment) (H : Constraints h) :
    h 126 0 = h 1 0 + ((1027026933978880855912949 : ℝ) / 1231189400320748122982390) * (h 3 0 - h 1 0) := by
  linear_combination value_504 h H + ((240561965026707051757876 : ℝ) / 3456801008592869729912095) * (scales0 h H) + ((-4215936139788936757521194181 : ℝ) / 5167917507846340246218582025) * (scales1 h H)

theorem homothetic_505 (h : Assignment) (H : Constraints h) :
    h 126 1 = h 1 1 + ((621772335938949344656519 : ℝ) / 1231189400320748122982390) * (h 3 0 - h 1 0) := by
  linear_combination value_505 h H + ((3812586225892122318788211 : ℝ) / 3456801008592869729912095) * (scales0 h H) + ((-16537522489458809905008878751 : ℝ) / 5167917507846340246218582025) * (scales1 h H)

theorem homothetic_506 (h : Assignment) (H : Constraints h) :
    h 126 2 = h 1 2 + ((9630627783411212560211751 : ℝ) / 19699030405131969967718240) * (h 3 0 - h 1 0) := by
  linear_combination value_506 h H + ((-66070054400348276677560623 : ℝ) / 235062468584315141634022460) * (scales0 h H) + ((153061583650156223807045403051 : ℝ) / 82686680125541443939497312400) * (scales1 h H)

theorem homothetic_507 (h : Assignment) (H : Constraints h) :
    h 126 3 = h 1 3 + ((-130961908332148683270212 : ℝ) / 615594700160374061491195) * (h 3 0 - h 1 0) := by
  linear_combination value_507 h H + ((144222590130685097409224 : ℝ) / 3456801008592869729912095) * (scales0 h H) + ((-7202570310470526750271528524 : ℝ) / 5167917507846340246218582025) * (scales1 h H)

theorem homothetic_508 (h : Assignment) (H : Constraints h) :
    h 127 0 = h 1 0 + ((874063471235004430739378 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0) := by
  linear_combination value_508 h H + ((-125830091135666335619816958 : ℝ) / 80398009002116453602781515) * (scales0 h H) + ((67536049194508108851727272846 : ℝ) / 9245771035243392164319874225) * (scales1 h H)

theorem homothetic_509 (h : Assignment) (H : Constraints h) :
    h 127 1 = h 1 1 + ((529787797170143595009788 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0) := by
  linear_combination value_509 h H + ((10934925996985603570411377 : ℝ) / 80398009002116453602781515) * (scales0 h H) + ((14822215821356797205531829486 : ℝ) / 9245771035243392164319874225) * (scales1 h H)

theorem homothetic_510 (h : Assignment) (H : Constraints h) :
    h 127 2 = h 1 2 + ((578749084305489324838032 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0) := by
  linear_combination value_510 h H + ((13065867661683706731400226723 : ℝ) / 10934129224287837689978286040) * (scales0 h H) + ((-50677467186335059297991218311 : ℝ) / 9245771035243392164319874225) * (scales1 h H)

theorem homothetic_511 (h : Assignment) (H : Constraints h) :
    h 127 3 = h 1 3 + ((-257588362112298345612543 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0) := by
  linear_combination value_511 h H + ((-65195622996738853600374372 : ℝ) / 80398009002116453602781515) * (scales0 h H) + ((26274335083844763094555047894 : ℝ) / 9245771035243392164319874225) * (scales1 h H)

theorem homothetic_512 (h : Assignment) (H : Constraints h) :
    h 128 0 = h 1 0 + ((100340131284208498460027 : ℝ) / 120188033356954996197700) * (h 3 0 - h 1 0) := by
  linear_combination value_512 h H + ((16401952160911844438037 : ℝ) / 168725508366494513892925) * (scales0 h H) + ((-480774751631741289653908389 : ℝ) / 504489270015818596539845750) * (scales1 h H)

theorem homothetic_513 (h : Assignment) (H : Constraints h) :
    h 128 1 = h 1 1 + ((113794235583827978925919 : ℝ) / 240376066713909992395400) * (h 3 0 - h 1 0) := by
  linear_combination value_513 h H + ((-58023053356334461018911 : ℝ) / 337451016732989027785850) * (scales0 h H) + ((3161039314271773420806596667 : ℝ) / 1008978540031637193079691500) * (scales1 h H)

theorem homothetic_514 (h : Assignment) (H : Constraints h) :
    h 128 2 = h 1 2 + ((1076920901502988480947303 : ℝ) / 1923008533711279939163200) * (h 3 0 - h 1 0) := by
  linear_combination value_514 h H + ((14794973814770092723650381 : ℝ) / 45893338275686507778875600) * (scales0 h H) + ((-10500665848274917354430148421 : ℝ) / 8071828320253097544637532000) * (scales1 h H)

theorem homothetic_515 (h : Assignment) (H : Constraints h) :
    h 128 3 = h 1 3 + ((-12759751460028199206351 : ℝ) / 60094016678477498098850) * (h 3 0 - h 1 0) := by
  linear_combination value_515 h H + ((9833358418001256641538 : ℝ) / 168725508366494513892925) * (scales0 h H) + ((-372304208406275240464072143 : ℝ) / 252244635007909298269922875) * (scales1 h H)

theorem homothetic_516 (h : Assignment) (H : Constraints h) :
    h 129 0 = h 1 0 + ((37945283165796075729259 : ℝ) / 47944807999223844799935) * (h 3 0 - h 1 0) := by
  linear_combination value_516 h H + ((-33569999458194540553426690 : ℝ) / 20299831706871375888292479) * (scales0 h H) + ((154529642813639551120678656 : ℝ) / 19952826036668446385928505) * (scales1 h H)

theorem homothetic_517 (h : Assignment) (H : Constraints h) :
    h 129 1 = h 1 1 + ((22643664462472705843084 : ℝ) / 47944807999223844799935) * (h 3 0 - h 1 0) := by
  linear_combination value_517 h H + ((-4402962579002190800932531 : ℝ) / 20299831706871375888292479) * (scales0 h H) + ((13393165800162739382713734 : ℝ) / 3990565207333689277185701) * (scales1 h H)

theorem homothetic_518 (h : Assignment) (H : Constraints h) :
    h 129 2 = h 1 2 + ((204749156506201958443003 : ℝ) / 383558463993790758399480) * (h 3 0 - h 1 0) := by
  linear_combination value_518 h H + ((-2027064785014945318712380073 : ℝ) / 2760777112134507120807777144) * (scales0 h H) + ((315083883405342297140896639 : ℝ) / 79811304146673785543714020) * (scales1 h H)

theorem homothetic_519 (h : Assignment) (H : Constraints h) :
    h 129 3 = h 1 3 + ((-11268276397206178816139 : ℝ) / 47944807999223844799935) * (h 3 0 - h 1 0) := by
  linear_combination value_519 h H + ((-599816457482315935619492 : ℝ) / 699994196788668134079051) * (scales0 h H) + ((2112356982453003366864414 : ℝ) / 688028484023049875376845) * (scales1 h H)

theorem homothetic_520 (h : Assignment) (H : Constraints h) :
    h 130 0 = h 1 0 + ((1027026933978880855912949 : ℝ) / 1231189400320748122982390) * (h 3 0 - h 1 0) := by
  linear_combination value_520 h H + ((240561965026707051757876 : ℝ) / 3456801008592869729912095) * (scales0 h H) + ((-4215936139788936757521194181 : ℝ) / 5167917507846340246218582025) * (scales1 h H)

theorem homothetic_521 (h : Assignment) (H : Constraints h) :
    h 130 1 = h 1 1 + ((621772335938949344656519 : ℝ) / 1231189400320748122982390) * (h 3 0 - h 1 0) := by
  linear_combination value_521 h H + ((3812586225892122318788211 : ℝ) / 3456801008592869729912095) * (scales0 h H) + ((-16537522489458809905008878751 : ℝ) / 5167917507846340246218582025) * (scales1 h H)

theorem homothetic_522 (h : Assignment) (H : Constraints h) :
    h 130 2 = h 1 2 + ((10987079498918044589196651 : ℝ) / 19699030405131969967718240) * (h 3 0 - h 1 0) := by
  linear_combination value_522 h H + ((54248237320823673320051397 : ℝ) / 235062468584315141634022460) * (scales0 h H) + ((-69944775396722900818180883489 : ℝ) / 82686680125541443939497312400) * (scales1 h H)

theorem homothetic_523 (h : Assignment) (H : Constraints h) :
    h 130 3 = h 1 3 + ((-130961908332148683270212 : ℝ) / 615594700160374061491195) * (h 3 0 - h 1 0) := by
  linear_combination value_523 h H + ((144222590130685097409224 : ℝ) / 3456801008592869729912095) * (scales0 h H) + ((-7202570310470526750271528524 : ℝ) / 5167917507846340246218582025) * (scales1 h H)

theorem homothetic_524 (h : Assignment) (H : Constraints h) :
    h 131 0 = h 1 0 + ((874063471235004430739378 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0) := by
  linear_combination value_524 h H + ((-125830091135666335619816958 : ℝ) / 80398009002116453602781515) * (scales0 h H) + ((67536049194508108851727272846 : ℝ) / 9245771035243392164319874225) * (scales1 h H)

theorem homothetic_525 (h : Assignment) (H : Constraints h) :
    h 131 1 = h 1 1 + ((529787797170143595009788 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0) := by
  linear_combination value_525 h H + ((10934925996985603570411377 : ℝ) / 80398009002116453602781515) * (scales0 h H) + ((14822215821356797205531829486 : ℝ) / 9245771035243392164319874225) * (scales1 h H)

theorem homothetic_526 (h : Assignment) (H : Constraints h) :
    h 131 2 = h 1 2 + ((588731629397963846263462 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0) := by
  linear_combination value_526 h H + ((-7700484084216196182764171737 : ℝ) / 10934129224287837689978286040) * (scales0 h H) + ((35124268474128805285885696009 : ℝ) / 9245771035243392164319874225) * (scales1 h H)

theorem homothetic_527 (h : Assignment) (H : Constraints h) :
    h 131 3 = h 1 3 + ((-257588362112298345612543 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0) := by
  linear_combination value_527 h H + ((-65195622996738853600374372 : ℝ) / 80398009002116453602781515) * (scales0 h H) + ((26274335083844763094555047894 : ℝ) / 9245771035243392164319874225) * (scales1 h H)

theorem homothetic_528 (h : Assignment) (H : Constraints h) :
    h 132 0 = h 1 0 + ((2935064701642600779897 : ℝ) / 3726409371667389204473) * (h 3 0 - h 1 0) := by
  linear_combination value_528 h H + ((-109175811564558021538052 : ℝ) / 249669427901715076699691) * (scales0 h H) + ((10310189948343925385992056 : ℝ) / 5742396841739446764092893) * (scales1 h H)

theorem homothetic_529 (h : Assignment) (H : Constraints h) :
    h 132 1 = h 1 1 + ((1751923035161058628064 : ℝ) / 3726409371667389204473) * (h 3 0 - h 1 0) := by
  linear_combination value_529 h H + ((117696620438875313173079 : ℝ) / 249669427901715076699691) * (scales0 h H) + ((-291719362271465515182138 : ℝ) / 28711984208697233820464465) * (scales1 h H)

theorem homothetic_530 (h : Assignment) (H : Constraints h) :
    h 132 2 = h 1 2 + ((15699441442694853759603 : ℝ) / 29811274973339113635784) * (h 3 0 - h 1 0) := by
  linear_combination value_530 h H + ((21109129961762864834309105 : ℝ) / 16977521097316625215578988) * (scales0 h H) + ((-657088095247999863383620611 : ℝ) / 114847936834788935281857860) * (scales1 h H)

theorem homothetic_531 (h : Assignment) (H : Constraints h) :
    h 132 3 = h 1 3 + ((-882872984694381404469 : ℝ) / 3726409371667389204473) * (h 3 0 - h 1 0) := by
  linear_combination value_531 h H + ((-928717562452291111080 : ℝ) / 3726409371667389204473) * (scales0 h H) + ((42085322381761110668898 : ℝ) / 428537077741749758514395) * (scales1 h H)

theorem homothetic_532 (h : Assignment) (H : Constraints h) :
    h 133 0 = h 1 0 + ((756896934477189495856362 : ℝ) / 959290296601172289817895) * (h 3 0 - h 1 0) := by
  linear_combination value_532 h H + ((-414876610754063195580374 : ℝ) / 959290296601172289817895) * (scales0 h H) + ((195059622242413808686096038 : ℝ) / 110318384109134813329057925) * (scales1 h H)

theorem homothetic_533 (h : Assignment) (H : Constraints h) :
    h 133 1 = h 1 1 + ((20000684545103902867904 : ℝ) / 41708273765268360426865) * (h 3 0 - h 1 0) := by
  linear_combination value_533 h H + ((21026255172181169180277 : ℝ) / 41708273765268360426865) * (scales0 h H) + ((-941473835656930474758414 : ℝ) / 4796451483005861449089475) * (scales1 h H)

theorem homothetic_534 (h : Assignment) (H : Constraints h) :
    h 133 2 = h 1 2 + ((87640008256665869233209 : ℝ) / 166833095061073441707460) * (h 3 0 - h 1 0) := by
  linear_combination value_534 h H + ((1756706192469233448233147 : ℝ) / 1418081308019124254513410) * (scales0 h H) + ((-54635370603528972226547007 : ℝ) / 9592902966011722898178950) * (scales1 h H)

theorem homothetic_535 (h : Assignment) (H : Constraints h) :
    h 133 3 = h 1 3 + ((-226570796465936930441627 : ℝ) / 959290296601172289817895) * (h 3 0 - h 1 0) := by
  linear_combination value_535 h H + ((-236618073705471893872696 : ℝ) / 959290296601172289817895) * (scales0 h H) + ((9223400505893096429721342 : ℝ) / 110318384109134813329057925) * (scales1 h H)

theorem homothetic_536 (h : Assignment) (H : Constraints h) :
    h 134 0 = h 1 0 + ((2935064701642600779897 : ℝ) / 3726409371667389204473) * (h 3 0 - h 1 0) := by
  linear_combination value_536 h H + ((-109175811564558021538052 : ℝ) / 249669427901715076699691) * (scales0 h H) + ((10310189948343925385992056 : ℝ) / 5742396841739446764092893) * (scales1 h H)

theorem homothetic_537 (h : Assignment) (H : Constraints h) :
    h 134 1 = h 1 1 + ((1751923035161058628064 : ℝ) / 3726409371667389204473) * (h 3 0 - h 1 0) := by
  linear_combination value_537 h H + ((117696620438875313173079 : ℝ) / 249669427901715076699691) * (scales0 h H) + ((-291719362271465515182138 : ℝ) / 28711984208697233820464465) * (scales1 h H)

theorem homothetic_538 (h : Assignment) (H : Constraints h) :
    h 134 2 = h 1 2 + ((15937830579231558748867 : ℝ) / 29811274973339113635784) * (h 3 0 - h 1 0) := by
  linear_combination value_538 h H + ((-251753206123348448905855 : ℝ) / 253395837273382465904164) * (scales0 h H) + ((8940910464732447581878847 : ℝ) / 1714148310966999034057580) * (scales1 h H)

theorem homothetic_539 (h : Assignment) (H : Constraints h) :
    h 134 3 = h 1 3 + ((-882872984694381404469 : ℝ) / 3726409371667389204473) * (h 3 0 - h 1 0) := by
  linear_combination value_539 h H + ((-928717562452291111080 : ℝ) / 3726409371667389204473) * (scales0 h H) + ((42085322381761110668898 : ℝ) / 428537077741749758514395) * (scales1 h H)

theorem homothetic_540 (h : Assignment) (H : Constraints h) :
    h 135 0 = h 1 0 + ((756896934477189495856362 : ℝ) / 959290296601172289817895) * (h 3 0 - h 1 0) := by
  linear_combination value_540 h H + ((-414876610754063195580374 : ℝ) / 959290296601172289817895) * (scales0 h H) + ((195059622242413808686096038 : ℝ) / 110318384109134813329057925) * (scales1 h H)

theorem homothetic_541 (h : Assignment) (H : Constraints h) :
    h 135 1 = h 1 1 + ((20000684545103902867904 : ℝ) / 41708273765268360426865) * (h 3 0 - h 1 0) := by
  linear_combination value_541 h H + ((21026255172181169180277 : ℝ) / 41708273765268360426865) * (scales0 h H) + ((-941473835656930474758414 : ℝ) / 4796451483005861449089475) * (scales1 h H)

theorem homothetic_542 (h : Assignment) (H : Constraints h) :
    h 135 2 = h 1 2 + ((2055650370273213078065527 : ℝ) / 3837161186404689159271580) * (h 3 0 - h 1 0) := by
  linear_combination value_542 h H + ((-16139933799702809877368987 : ℝ) / 16307935042219928926904215) * (scales0 h H) + ((1146036153981825572140388119 : ℝ) / 220636768218269626658115850) * (scales1 h H)

theorem homothetic_543 (h : Assignment) (H : Constraints h) :
    h 135 3 = h 1 3 + ((-226570796465936930441627 : ℝ) / 959290296601172289817895) * (h 3 0 - h 1 0) := by
  linear_combination value_543 h H + ((-236618073705471893872696 : ℝ) / 959290296601172289817895) * (scales0 h H) + ((9223400505893096429721342 : ℝ) / 110318384109134813329057925) * (scales1 h H)

theorem homothetic_544 (h : Assignment) (H : Constraints h) :
    h 136 0 = h 1 0 + ((4148824248022565979793367417 : ℝ) / 5084639112497370014171714638) * (h 3 0 - h 1 0) := by
  linear_combination value_544 h H + ((-213187919756061655496661927 : ℝ) / 391126085576720770320901126) * (scales0 h H) + ((5709290239179495222494681169 : ℝ) / 2542319556248685007085857319) * (scales1 h H)

theorem homothetic_545 (h : Assignment) (H : Constraints h) :
    h 136 1 = h 1 1 + ((4938288334848929488318654189 : ℝ) / 10169278224994740028343429276) * (h 3 0 - h 1 0) := by
  linear_combination value_545 h H + ((189892052010983799264814005 : ℝ) / 782252171153441540641802252) * (scales0 h H) + ((5428426250568344182008510411 : ℝ) / 5084639112497370014171714638) * (scales1 h H)

theorem homothetic_546 (h : Assignment) (H : Constraints h) :
    h 136 2 = h 1 2 + ((40596238269230557822406629745 : ℝ) / 81354225799957920226747434208) * (h 3 0 - h 1 0) := by
  linear_combination value_546 h H + ((281873812034490437149632993 : ℝ) / 6258017369227532325134418016) * (scales0 h H) + ((9173994634686174881142454227 : ℝ) / 40677112899978960113373717104) * (scales1 h H)

theorem homothetic_547 (h : Assignment) (H : Constraints h) :
    h 136 3 = h 1 3 + ((-565250632961968976317651050 : ℝ) / 2542319556248685007085857319) * (h 3 0 - h 1 0) := by
  linear_combination value_547 h H + ((-55080332269817589302385951 : ℝ) / 195563042788360385160450563) * (scales0 h H) + ((551634595776523028599468848 : ℝ) / 2542319556248685007085857319) * (scales1 h H)

theorem homothetic_548 (h : Assignment) (H : Constraints h) :
    h 137 0 = h 1 0 + ((149202793612884591943313675 : ℝ) / 185859158465470735170299686) * (h 3 0 - h 1 0) := by
  linear_combination value_548 h H + ((-457728542401119020019870777 : ℝ) / 185859158465470735170299686) * (scales0 h H) + ((1085185267384402951048261791 : ℝ) / 92929579232735367585149843) * (scales1 h H)

theorem homothetic_549 (h : Assignment) (H : Constraints h) :
    h 137 1 = h 1 1 + ((222615224668037268577921484 : ℝ) / 464647896163676837925749215) * (h 3 0 - h 1 0) := by
  linear_combination value_549 h H + ((-65381281379215848390883959 : ℝ) / 92929579232735367585149843) * (scales0 h H) + ((2658624247514620828316061234 : ℝ) / 464647896163676837925749215) * (scales1 h H)

theorem homothetic_550 (h : Assignment) (H : Constraints h) :
    h 137 2 = h 1 2 + ((3818379522142608901893272387 : ℝ) / 7434366338618829406811987440) * (h 3 0 - h 1 0) := by
  linear_combination value_550 h H + ((3227092233895563801660850797 : ℝ) / 1486873267723765881362397488) * (scales0 h H) + ((-38017423363876502189231092239 : ℝ) / 3717183169309414703405993720) * (scales1 h H)

theorem homothetic_551 (h : Assignment) (H : Constraints h) :
    h 137 3 = h 1 3 + ((-106480836916872452880983463 : ℝ) / 464647896163676837925749215) * (h 3 0 - h 1 0) := by
  linear_combination value_551 h H + ((-118503728264286481403345688 : ℝ) / 92929579232735367585149843) * (scales0 h H) + ((2371339062383857627979294082 : ℝ) / 464647896163676837925749215) * (scales1 h H)

theorem homothetic_552 (h : Assignment) (H : Constraints h) :
    h 138 0 = h 1 0 + ((65835672595422239671695232802 : ℝ) / 80657737443519335659690486109) * (h 3 0 - h 1 0) := by
  linear_combination value_552 h H + ((-3126756156422237613951041596 : ℝ) / 6204441341809179666130037393) * (scales0 h H) + ((164826048525223839798807150750 : ℝ) / 80657737443519335659690486109) * (scales1 h H)

theorem homothetic_553 (h : Assignment) (H : Constraints h) :
    h 138 1 = h 1 1 + ((39338327489839858386171227646 : ℝ) / 80657737443519335659690486109) * (h 3 0 - h 1 0) := by
  linear_combination value_553 h H + ((3411671951808058856002223845 : ℝ) / 6204441341809179666130037393) * (scales0 h H) + ((-35724170004512650198172474382 : ℝ) / 80657737443519335659690486109) * (scales1 h H)

theorem homothetic_554 (h : Assignment) (H : Constraints h) :
    h 138 2 = h 1 2 + ((321974428085998725597296933773 : ℝ) / 645261899548154685277523888872) * (h 3 0 - h 1 0) := by
  linear_combination value_554 h H + ((1033537310793131602881987641 : ℝ) / 24817765367236718664520149572) * (scales0 h H) + ((78153896159066249752805747307 : ℝ) / 322630949774077342638761944436) * (scales1 h H)

theorem homothetic_555 (h : Assignment) (H : Constraints h) :
    h 138 3 = h 1 3 + ((-17921391158976226871865665829 : ℝ) / 80657737443519335659690486109) * (h 3 0 - h 1 0) := by
  linear_combination value_555 h H + ((-1615689746581315952869987896 : ℝ) / 6204441341809179666130037393) * (scales0 h H) + ((9074791502589585430862011494 : ℝ) / 80657737443519335659690486109) * (scales1 h H)

theorem homothetic_556 (h : Assignment) (H : Constraints h) :
    h 139 0 = h 1 0 + ((1670260968397920540156861991 : ℝ) / 2074506067496563827516624195) * (h 3 0 - h 1 0) := by
  linear_combination value_556 h H + ((-1021003474254000833751307629833 : ℝ) / 453072125141249539929630724188) * (scales0 h H) + ((66287825663355286117291959149 : ℝ) / 5993017528323406612825803230) * (scales1 h H)

theorem homothetic_557 (h : Assignment) (H : Constraints h) :
    h 139 1 = h 1 1 + ((1003897197976319768434290316 : ℝ) / 2074506067496563827516624195) * (h 3 0 - h 1 0) := by
  linear_combination value_557 h H + ((-4484282859963923348361441509 : ℝ) / 16181147326473197854629668721) * (scales0 h H) + ((13379951895815089576602050242 : ℝ) / 2996508764161703306412901615) * (scales1 h H)

theorem homothetic_558 (h : Assignment) (H : Constraints h) :
    h 139 2 = h 1 2 + ((2122341129024522150111233753 : ℝ) / 4149012134993127655033248390) * (h 3 0 - h 1 0) := by
  linear_combination value_558 h H + ((1028330136854063252507923764059 : ℝ) / 517796714447142331348149399072) * (scales0 h H) + ((-464292682002857386405736794337 : ℝ) / 47944140226587252902606425840) * (scales1 h H)

theorem homothetic_559 (h : Assignment) (H : Constraints h) :
    h 139 3 = h 1 3 + ((-472864766827913401537169891 : ℝ) / 2074506067496563827516624195) * (h 3 0 - h 1 0) := by
  linear_combination value_559 h H + ((-132166455728534812477523488076 : ℝ) / 113268031285312384982407681047) * (scales0 h H) + ((14335953079860154106054582218 : ℝ) / 2996508764161703306412901615) * (scales1 h H)

theorem homothetic_560 (h : Assignment) (H : Constraints h) :
    h 140 0 = h 1 0 + ((8304500581584305539562577334 : ℝ) / 10142285318032214414898904385) * (h 3 0 - h 1 0) := by
  linear_combination value_560 h H + ((-85875961378985222076361338 : ℝ) / 156035158738957144844598529) * (scales0 h H) + ((22960600609335036967202013198 : ℝ) / 10142285318032214414898904385) * (scales1 h H)

theorem homothetic_561 (h : Assignment) (H : Constraints h) :
    h 140 1 = h 1 1 + ((4906535356657251125339724649 : ℝ) / 10142285318032214414898904385) * (h 3 0 - h 1 0) := by
  linear_combination value_561 h H + ((38411663470918467880629255 : ℝ) / 156035158738957144844598529) * (scales0 h H) + ((10709194217554460098522315188 : ℝ) / 10142285318032214414898904385) * (scales1 h H)

theorem homothetic_562 (h : Assignment) (H : Constraints h) :
    h 140 2 = h 1 2 + ((44687036887344659550100205613 : ℝ) / 81138282544257715319191235080) * (h 3 0 - h 1 0) := by
  linear_combination value_562 h H + ((-64037000728352545155776199 : ℝ) / 1248281269911657158756788232) * (scales0 h H) + ((22530116888518686859564770383 : ℝ) / 40569141272128857659595617540) * (scales1 h H)

theorem homothetic_563 (h : Assignment) (H : Constraints h) :
    h 140 3 = h 1 3 + ((-2239717528780526923198348569 : ℝ) / 10142285318032214414898904385) * (h 3 0 - h 1 0) := by
  linear_combination value_563 h H + ((-44385079091353524376344828 : ℝ) / 156035158738957144844598529) * (scales0 h H) + ((2298096067182135113927703582 : ℝ) / 10142285318032214414898904385) * (scales1 h H)

theorem homothetic_564 (h : Assignment) (H : Constraints h) :
    h 141 0 = h 1 0 + ((13680129980524901849883997 : ℝ) / 17205283799270077026016280) * (h 3 0 - h 1 0) := by
  linear_combination value_564 h H + ((-1295134093827935973718659 : ℝ) / 860264189963503851300814) * (scales0 h H) + ((277343704725602265677456865 : ℝ) / 39572152738321177159837444) * (scales1 h H)

theorem homothetic_565 (h : Assignment) (H : Constraints h) :
    h 141 1 = h 1 1 + ((1020481614556172551615244 : ℝ) / 2150660474908759628252035) * (h 3 0 - h 1 0) := by
  linear_combination value_565 h H + ((-54950206021304685138747 : ℝ) / 430132094981751925650407) * (scales0 h H) + ((144110868863848355564920998 : ℝ) / 49465190922901471449796805) * (scales1 h H)

theorem homothetic_566 (h : Assignment) (H : Constraints h) :
    h 141 2 = h 1 2 + ((73792219984703345486771169 : ℝ) / 137642270394160616208130240) * (h 3 0 - h 1 0) := by
  linear_combination value_566 h H + ((-75046433451119088004039581 : ℝ) / 116995929835036523776910704) * (scales0 h H) + ((5519385069167698573864438273 : ℝ) / 1582886109532847086393497760) * (scales1 h H)

theorem homothetic_567 (h : Assignment) (H : Constraints h) :
    h 141 3 = h 1 3 + ((-501374243288405392583034 : ℝ) / 2150660474908759628252035) * (h 3 0 - h 1 0) := by
  linear_combination value_567 h H + ((-335616215828377762979568 : ℝ) / 430132094981751925650407) * (scales0 h H) + ((133037823446536300935042744 : ℝ) / 49465190922901471449796805) * (scales1 h H)

theorem homothetic_568 (h : Assignment) (H : Constraints h) :
    h 142 0 = h 1 0 + ((32894453627601669236924528203 : ℝ) / 40125038554912127264482075795) * (h 3 0 - h 1 0) := by
  linear_combination value_568 h H + ((-314878525056279147613324906 : ℝ) / 617308285460186573299724243) * (scales0 h H) + ((82808359645249467612955649736 : ℝ) / 40125038554912127264482075795) * (scales1 h H)

theorem homothetic_569 (h : Assignment) (H : Constraints h) :
    h 142 1 = h 1 1 + ((19707632172954535636665804033 : ℝ) / 40125038554912127264482075795) * (h 3 0 - h 1 0) := by
  linear_combination value_569 h H + ((335794842449942167076944285 : ℝ) / 617308285460186573299724243) * (scales0 h H) + ((-16988954485877604534684310704 : ℝ) / 40125038554912127264482075795) * (scales1 h H)

theorem homothetic_570 (h : Assignment) (H : Constraints h) :
    h 142 2 = h 1 2 + ((353642629134415506844988262617 : ℝ) / 642000616878594036231713212720) * (h 3 0 - h 1 0) := by
  linear_combination value_570 h H + ((-234802336003959332237846063 : ℝ) / 4938466283681492586397793944) * (scales0 h H) + ((172280964673096863417781854407 : ℝ) / 321000308439297018115856606360) * (scales1 h H)

theorem homothetic_571 (h : Assignment) (H : Constraints h) :
    h 142 3 = h 1 3 + ((-8840082381656969702886826773 : ℝ) / 40125038554912127264482075795) * (h 3 0 - h 1 0) := by
  linear_combination value_571 h H + ((-162745290001629589379931036 : ℝ) / 617308285460186573299724243) * (scales0 h H) + ((4942135071977515637471305614 : ℝ) / 40125038554912127264482075795) * (scales1 h H)

theorem homothetic_572 (h : Assignment) (H : Constraints h) :
    h 143 0 = h 1 0 + ((12023881457031766930853 : ℝ) / 15073723378247361660612) * (h 3 0 - h 1 0) := by
  linear_combination value_572 h H + ((-2888909663545370771091460211 : ℝ) / 1937048822721677210196945060) * (scales0 h H) + ((14865341638549968439249778579 : ℝ) / 2062598283453637770117117425) * (scales1 h H)

theorem homothetic_573 (h : Assignment) (H : Constraints h) :
    h 143 1 = h 1 1 + ((1816572152561131527176 : ℝ) / 3768430844561840415153) * (h 3 0 - h 1 0) := by
  linear_combination value_573 h H + ((-41701197932207330515473389 : ℝ) / 484262205680419302549236265) * (scales0 h H) + ((7217593650578870064146152214 : ℝ) / 2062598283453637770117117425) * (scales1 h H)

theorem homothetic_574 (h : Assignment) (H : Constraints h) :
    h 143 2 = h 1 2 + ((899744661814417380293 : ℝ) / 1674858153138595740068) * (h 3 0 - h 1 0) := by
  linear_combination value_574 h H + ((-18599735720609192380853033861 : ℝ) / 29270959987794233398531614240) * (scales0 h H) + ((117865192495578550643752549481 : ℝ) / 33001572535258204321873878800) * (scales1 h H)

theorem homothetic_575 (h : Assignment) (H : Constraints h) :
    h 143 3 = h 1 3 + ((-873519230859749645698 : ℝ) / 3768430844561840415153) * (h 3 0 - h 1 0) := by
  linear_combination value_575 h H + ((-374310634616781284906585336 : ℝ) / 484262205680419302549236265) * (scales0 h H) + ((5759642033963314397148106256 : ℝ) / 2062598283453637770117117425) * (scales1 h H)

/- Each rational-coordinate normalization is checked in a separate
four-coordinate theorem. Coverage groups contain at most 32 vertices. -/

private theorem homothetic_vertex000 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨0, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨0, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨0, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 0 0 = h 1 0 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0)
    convert homothetic_000 h H using 1 <;> norm_num
  · change h 0 1 = h 1 1 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0)
    convert homothetic_001 h H using 1 <;> norm_num
  · change h 0 2 = h 1 2 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0)
    convert homothetic_002 h H using 1 <;> norm_num
  · change h 0 3 = h 1 3 + ((29636437161 : ℝ) / 120001635295) * (h 3 0 - h 1 0)
    convert homothetic_003 h H using 1 <;> norm_num

private theorem homothetic_vertex001 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨1, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨1, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨1, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 1 0 = h 1 0 + (((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_004 h H using 1 <;> norm_num
  · change h 1 1 = h 1 1 + (((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_005 h H using 1 <;> norm_num
  · change h 1 2 = h 1 2 + (((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_006 h H using 1 <;> norm_num
  · change h 1 3 = h 1 3 + (((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_007 h H using 1 <;> norm_num

private theorem homothetic_vertex002 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨2, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨2, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨2, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 2 0 = h 1 0 + ((519521790728 : ℝ) / 999528331908) * (h 3 0 - h 1 0)
    convert homothetic_008 h H using 1 <;> norm_num
  · change h 2 1 = h 1 1 + ((351581980149 : ℝ) / 999528331908) * (h 3 0 - h 1 0)
    convert homothetic_009 h H using 1 <;> norm_num
  · change h 2 2 = h 1 2 + ((351581980149 : ℝ) / 999528331908) * (h 3 0 - h 1 0)
    convert homothetic_010 h H using 1 <;> norm_num
  · change h 2 3 = h 1 3 + ((237091497288 : ℝ) / 999528331908) * (h 3 0 - h 1 0)
    convert homothetic_011 h H using 1 <;> norm_num

private theorem homothetic_vertex003 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨3, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨3, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨3, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 3 0 = h 1 0 + (((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_012 h H using 1 <;> norm_num
  · change h 3 1 = h 1 1 + (((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_013 h H using 1 <;> norm_num
  · change h 3 2 = h 1 2 + (((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_014 h H using 1 <;> norm_num
  · change h 3 3 = h 1 3 + (((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_015 h H using 1 <;> norm_num

private theorem homothetic_vertex004 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨4, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨4, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨4, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 4 0 = h 1 0 + ((90365198134 : ℝ) / 240003270590) * (h 3 0 - h 1 0)
    convert homothetic_016 h H using 1 <;> norm_num
  · change h 4 1 = h 1 1 + ((160679098065 : ℝ) / 240003270590) * (h 3 0 - h 1 0)
    convert homothetic_017 h H using 1 <;> norm_num
  · change h 4 2 = h 1 2 + ((90365198134 : ℝ) / 240003270590) * (h 3 0 - h 1 0)
    convert homothetic_018 h H using 1 <;> norm_num
  · change h 4 3 = h 1 3 + ((59272874322 : ℝ) / 240003270590) * (h 3 0 - h 1 0)
    convert homothetic_019 h H using 1 <;> norm_num

private theorem homothetic_vertex005 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨5, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨5, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨5, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 5 0 = h 1 0 + (((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_020 h H using 1 <;> norm_num
  · change h 5 1 = h 1 1 + (((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_021 h H using 1 <;> norm_num
  · change h 5 2 = h 1 2 + (((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_022 h H using 1 <;> norm_num
  · change h 5 3 = h 1 3 + (((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_023 h H using 1 <;> norm_num

private theorem homothetic_vertex006 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨6, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨6, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨6, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 6 0 = h 1 0 + ((1039043581456 : ℝ) / 1999056663816) * (h 3 0 - h 1 0)
    convert homothetic_024 h H using 1 <;> norm_num
  · change h 6 1 = h 1 1 + ((1374342096003 : ℝ) / 1999056663816) * (h 3 0 - h 1 0)
    convert homothetic_025 h H using 1 <;> norm_num
  · change h 6 2 = h 1 2 + ((703163960298 : ℝ) / 1999056663816) * (h 3 0 - h 1 0)
    convert homothetic_026 h H using 1 <;> norm_num
  · change h 6 3 = h 1 3 + ((474182994576 : ℝ) / 1999056663816) * (h 3 0 - h 1 0)
    convert homothetic_027 h H using 1 <;> norm_num

private theorem homothetic_vertex007 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨7, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨7, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨7, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 7 0 = h 1 0 + (((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_028 h H using 1 <;> norm_num
  · change h 7 1 = h 1 1 + (((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_029 h H using 1 <;> norm_num
  · change h 7 2 = h 1 2 + (((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_030 h H using 1 <;> norm_num
  · change h 7 3 = h 1 3 + (((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_031 h H using 1 <;> norm_num

private theorem homothetic_vertex008 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨8, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨8, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨8, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 8 0 = h 1 0 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0)
    convert homothetic_032 h H using 1 <;> norm_num
  · change h 8 1 = h 1 1 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0)
    convert homothetic_033 h H using 1 <;> norm_num
  · change h 8 2 = h 1 2 + ((74819036228 : ℝ) / 120001635295) * (h 3 0 - h 1 0)
    convert homothetic_034 h H using 1 <;> norm_num
  · change h 8 3 = h 1 3 + ((29636437161 : ℝ) / 120001635295) * (h 3 0 - h 1 0)
    convert homothetic_035 h H using 1 <;> norm_num

private theorem homothetic_vertex009 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨9, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨9, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨9, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 9 0 = h 1 0 + (((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_036 h H using 1 <;> norm_num
  · change h 9 1 = h 1 1 + (((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_037 h H using 1 <;> norm_num
  · change h 9 2 = h 1 2 + (((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_038 h H using 1 <;> norm_num
  · change h 9 3 = h 1 3 + (((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_039 h H using 1 <;> norm_num

private theorem homothetic_vertex010 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨10, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨10, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨10, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 10 0 = h 1 0 + ((519521790728 : ℝ) / 999528331908) * (h 3 0 - h 1 0)
    convert homothetic_040 h H using 1 <;> norm_num
  · change h 10 1 = h 1 1 + ((351581980149 : ℝ) / 999528331908) * (h 3 0 - h 1 0)
    convert homothetic_041 h H using 1 <;> norm_num
  · change h 10 2 = h 1 2 + ((657825164146 : ℝ) / 999528331908) * (h 3 0 - h 1 0)
    convert homothetic_042 h H using 1 <;> norm_num
  · change h 10 3 = h 1 3 + ((237091497288 : ℝ) / 999528331908) * (h 3 0 - h 1 0)
    convert homothetic_043 h H using 1 <;> norm_num

private theorem homothetic_vertex011 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨11, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨11, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨11, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 11 0 = h 1 0 + (((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_044 h H using 1 <;> norm_num
  · change h 11 1 = h 1 1 + (((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_045 h H using 1 <;> norm_num
  · change h 11 2 = h 1 2 + (((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_046 h H using 1 <;> norm_num
  · change h 11 3 = h 1 3 + (((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_047 h H using 1 <;> norm_num

private theorem homothetic_vertex012 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨12, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨12, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨12, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 12 0 = h 1 0 + ((90365198134 : ℝ) / 240003270590) * (h 3 0 - h 1 0)
    convert homothetic_048 h H using 1 <;> norm_num
  · change h 12 1 = h 1 1 + ((160679098065 : ℝ) / 240003270590) * (h 3 0 - h 1 0)
    convert homothetic_049 h H using 1 <;> norm_num
  · change h 12 2 = h 1 2 + ((149638072456 : ℝ) / 240003270590) * (h 3 0 - h 1 0)
    convert homothetic_050 h H using 1 <;> norm_num
  · change h 12 3 = h 1 3 + ((59272874322 : ℝ) / 240003270590) * (h 3 0 - h 1 0)
    convert homothetic_051 h H using 1 <;> norm_num

private theorem homothetic_vertex013 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨13, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨13, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨13, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 13 0 = h 1 0 + (((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_052 h H using 1 <;> norm_num
  · change h 13 1 = h 1 1 + (((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_053 h H using 1 <;> norm_num
  · change h 13 2 = h 1 2 + (((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_054 h H using 1 <;> norm_num
  · change h 13 3 = h 1 3 + (((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_055 h H using 1 <;> norm_num

private theorem homothetic_vertex014 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨14, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨14, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨14, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 14 0 = h 1 0 + ((1039043581456 : ℝ) / 1999056663816) * (h 3 0 - h 1 0)
    convert homothetic_056 h H using 1 <;> norm_num
  · change h 14 1 = h 1 1 + ((1374342096003 : ℝ) / 1999056663816) * (h 3 0 - h 1 0)
    convert homothetic_057 h H using 1 <;> norm_num
  · change h 14 2 = h 1 2 + ((1315650328292 : ℝ) / 1999056663816) * (h 3 0 - h 1 0)
    convert homothetic_058 h H using 1 <;> norm_num
  · change h 14 3 = h 1 3 + ((474182994576 : ℝ) / 1999056663816) * (h 3 0 - h 1 0)
    convert homothetic_059 h H using 1 <;> norm_num

private theorem homothetic_vertex015 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨15, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨15, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨15, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 15 0 = h 1 0 + (((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_060 h H using 1 <;> norm_num
  · change h 15 1 = h 1 1 + (((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_061 h H using 1 <;> norm_num
  · change h 15 2 = h 1 2 + (((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_062 h H using 1 <;> norm_num
  · change h 15 3 = h 1 3 + (((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)) * (h 3 0 - h 1 0)
    convert homothetic_063 h H using 1 <;> norm_num

private theorem homothetic_vertex016 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨16, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨16, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨16, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 16 0 = h 1 0 + ((282243102288077 : ℝ) / 617857941263449) * (h 3 0 - h 1 0)
    convert homothetic_064 h H using 1 <;> norm_num
  · change h 16 1 = h 1 1 + ((158648699407709 : ℝ) / 617857941263449) * (h 3 0 - h 1 0)
    convert homothetic_065 h H using 1 <;> norm_num
  · change h 16 2 = h 1 2 + ((158648699407709 : ℝ) / 617857941263449) * (h 3 0 - h 1 0)
    convert homothetic_066 h H using 1 <;> norm_num
  · change h 16 3 = h 1 3 + ((144596176908519 : ℝ) / 617857941263449) * (h 3 0 - h 1 0)
    convert homothetic_067 h H using 1 <;> norm_num

private theorem homothetic_vertex017 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨17, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨17, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨17, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 17 0 = h 1 0 + ((5880080129455 : ℝ) / 13520913290240) * (h 3 0 - h 1 0)
    convert homothetic_068 h H using 1 <;> norm_num
  · change h 17 1 = h 1 1 + ((2975709287677 : ℝ) / 13520913290240) * (h 3 0 - h 1 0)
    convert homothetic_069 h H using 1 <;> norm_num
  · change h 17 2 = h 1 2 + ((2975709287677 : ℝ) / 13520913290240) * (h 3 0 - h 1 0)
    convert homothetic_070 h H using 1 <;> norm_num
  · change h 17 3 = h 1 3 + ((2904370841778 : ℝ) / 13520913290240) * (h 3 0 - h 1 0)
    convert homothetic_071 h H using 1 <;> norm_num

private theorem homothetic_vertex018 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨18, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨18, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨18, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 18 0 = h 1 0 + ((79926674830002 : ℝ) / 167585073310154) * (h 3 0 - h 1 0)
    convert homothetic_072 h H using 1 <;> norm_num
  · change h 18 1 = h 1 1 + ((42614921436437 : ℝ) / 167585073310154) * (h 3 0 - h 1 0)
    convert homothetic_073 h H using 1 <;> norm_num
  · change h 18 2 = h 1 2 + ((42614921436437 : ℝ) / 167585073310154) * (h 3 0 - h 1 0)
    convert homothetic_074 h H using 1 <;> norm_num
  · change h 18 3 = h 1 3 + ((39001551303876 : ℝ) / 167585073310154) * (h 3 0 - h 1 0)
    convert homothetic_075 h H using 1 <;> norm_num

private theorem homothetic_vertex019 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨19, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨19, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨19, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 19 0 = h 1 0 + ((6880164606986 : ℝ) / 13520913290240) * (h 3 0 - h 1 0)
    convert homothetic_076 h H using 1 <;> norm_num
  · change h 19 1 = h 1 1 + ((2975709287677 : ℝ) / 13520913290240) * (h 3 0 - h 1 0)
    convert homothetic_077 h H using 1 <;> norm_num
  · change h 19 2 = h 1 2 + ((2975709287677 : ℝ) / 13520913290240) * (h 3 0 - h 1 0)
    convert homothetic_078 h H using 1 <;> norm_num
  · change h 19 3 = h 1 3 + ((2904370841778 : ℝ) / 13520913290240) * (h 3 0 - h 1 0)
    convert homothetic_079 h H using 1 <;> norm_num

private theorem homothetic_vertex020 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨20, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨20, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨20, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 20 0 = h 1 0 + ((2200075481498470 : ℝ) / 5084219205547142) * (h 3 0 - h 1 0)
    convert homothetic_080 h H using 1 <;> norm_num
  · change h 20 1 = h 1 1 + ((3643447258418433 : ℝ) / 5084219205547142) * (h 3 0 - h 1 0)
    convert homothetic_081 h H using 1 <;> norm_num
  · change h 20 2 = h 1 2 + ((1488089715142606 : ℝ) / 5084219205547142) * (h 3 0 - h 1 0)
    convert homothetic_082 h H using 1 <;> norm_num
  · change h 20 3 = h 1 3 + ((1209581546289054 : ℝ) / 5084219205547142) * (h 3 0 - h 1 0)
    convert homothetic_083 h H using 1 <;> norm_num

private theorem homothetic_vertex021 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨21, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨21, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨21, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 21 0 = h 1 0 + ((240003270590 : ℝ) / 717098038468) * (h 3 0 - h 1 0)
    convert homothetic_084 h H using 1 <;> norm_num
  · change h 21 1 = h 1 1 + ((588086130579 : ℝ) / 717098038468) * (h 3 0 - h 1 0)
    convert homothetic_085 h H using 1 <;> norm_num
  · change h 21 2 = h 1 2 + ((121457521946 : ℝ) / 717098038468) * (h 3 0 - h 1 0)
    convert homothetic_086 h H using 1 <;> norm_num
  · change h 21 3 = h 1 3 + ((118545748644 : ℝ) / 717098038468) * (h 3 0 - h 1 0)
    convert homothetic_087 h H using 1 <;> norm_num

private theorem homothetic_vertex022 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨22, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨22, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨22, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 22 0 = h 1 0 + ((19293474916189080 : ℝ) / 39290953518325328) * (h 3 0 - h 1 0)
    convert homothetic_088 h H using 1 <;> norm_num
  · change h 22 1 = h 1 1 + ((28364274250472077 : ℝ) / 39290953518325328) * (h 3 0 - h 1 0)
    convert homothetic_089 h H using 1 <;> norm_num
  · change h 22 2 = h 1 2 + ((11252536543291334 : ℝ) / 39290953518325328) * (h 3 0 - h 1 0)
    convert homothetic_090 h H using 1 <;> norm_num
  · change h 22 3 = h 1 3 + ((9201995192741856 : ℝ) / 39290953518325328) * (h 3 0 - h 1 0)
    convert homothetic_091 h H using 1 <;> norm_num

private theorem homothetic_vertex023 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨23, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨23, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨23, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 23 0 = h 1 0 + ((3122329502632 : ℝ) / 5019686269276) * (h 3 0 - h 1 0)
    convert homothetic_092 h H using 1 <;> norm_num
  · change h 23 1 = h 1 1 + ((4116602914053 : ℝ) / 5019686269276) * (h 3 0 - h 1 0)
    convert homothetic_093 h H using 1 <;> norm_num
  · change h 23 2 = h 1 2 + ((850202653622 : ℝ) / 5019686269276) * (h 3 0 - h 1 0)
    convert homothetic_094 h H using 1 <;> norm_num
  · change h 23 3 = h 1 3 + ((829820240508 : ℝ) / 5019686269276) * (h 3 0 - h 1 0)
    convert homothetic_095 h H using 1 <;> norm_num

private theorem homothetic_vertex024 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨24, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨24, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨24, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 24 0 = h 1 0 + ((1100037740749235 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0)
    convert homothetic_096 h H using 1 <;> norm_num
  · change h 24 1 = h 1 1 + ((744044857571303 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0)
    convert homothetic_097 h H using 1 <;> norm_num
  · change h 24 2 = h 1 2 + ((1976061186791234 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0)
    convert homothetic_098 h H using 1 <;> norm_num
  · change h 24 3 = h 1 3 + ((604790773144527 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0)
    convert homothetic_099 h H using 1 <;> norm_num

private theorem homothetic_vertex025 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨25, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨25, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨25, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 25 0 = h 1 0 + ((120001635295 : ℝ) / 358549019234) * (h 3 0 - h 1 0)
    convert homothetic_100 h H using 1 <;> norm_num
  · change h 25 1 = h 1 1 + ((60728760973 : ℝ) / 358549019234) * (h 3 0 - h 1 0)
    convert homothetic_101 h H using 1 <;> norm_num
  · change h 25 2 = h 1 2 + ((327456695422 : ℝ) / 358549019234) * (h 3 0 - h 1 0)
    convert homothetic_102 h H using 1 <;> norm_num
  · change h 25 3 = h 1 3 + ((59272874322 : ℝ) / 358549019234) * (h 3 0 - h 1 0)
    convert homothetic_103 h H using 1 <;> norm_num

private theorem homothetic_vertex026 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨26, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨26, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨26, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 26 0 = h 1 0 + ((9646737458094540 : ℝ) / 19645476759162664) * (h 3 0 - h 1 0)
    convert homothetic_104 h H using 1 <;> norm_num
  · change h 26 1 = h 1 1 + ((5626268271645667 : ℝ) / 19645476759162664) * (h 3 0 - h 1 0)
    convert homothetic_105 h H using 1 <;> norm_num
  · change h 26 2 = h 1 2 + ((15407448355824946 : ℝ) / 19645476759162664) * (h 3 0 - h 1 0)
    convert homothetic_106 h H using 1 <;> norm_num
  · change h 26 3 = h 1 3 + ((4600997596370928 : ℝ) / 19645476759162664) * (h 3 0 - h 1 0)
    convert homothetic_107 h H using 1 <;> norm_num

private theorem homothetic_vertex027 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨27, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨27, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨27, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 27 0 = h 1 0 + ((1561164751316 : ℝ) / 2509843134638) * (h 3 0 - h 1 0)
    convert homothetic_108 h H using 1 <;> norm_num
  · change h 27 1 = h 1 1 + ((425101326811 : ℝ) / 2509843134638) * (h 3 0 - h 1 0)
    convert homothetic_109 h H using 1 <;> norm_num
  · change h 27 2 = h 1 2 + ((2292196867954 : ℝ) / 2509843134638) * (h 3 0 - h 1 0)
    convert homothetic_110 h H using 1 <;> norm_num
  · change h 27 3 = h 1 3 + ((414910120254 : ℝ) / 2509843134638) * (h 3 0 - h 1 0)
    convert homothetic_111 h H using 1 <;> norm_num

private theorem homothetic_vertex028 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨28, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨28, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨28, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 28 0 = h 1 0 + ((2200075481498470 : ℝ) / 5084219205547142) * (h 3 0 - h 1 0)
    convert homothetic_112 h H using 1 <;> norm_num
  · change h 28 1 = h 1 1 + ((3643447258418433 : ℝ) / 5084219205547142) * (h 3 0 - h 1 0)
    convert homothetic_113 h H using 1 <;> norm_num
  · change h 28 2 = h 1 2 + ((3952122373582468 : ℝ) / 5084219205547142) * (h 3 0 - h 1 0)
    convert homothetic_114 h H using 1 <;> norm_num
  · change h 28 3 = h 1 3 + ((1209581546289054 : ℝ) / 5084219205547142) * (h 3 0 - h 1 0)
    convert homothetic_115 h H using 1 <;> norm_num

private theorem homothetic_vertex029 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨29, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨29, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨29, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 29 0 = h 1 0 + ((240003270590 : ℝ) / 717098038468) * (h 3 0 - h 1 0)
    convert homothetic_116 h H using 1 <;> norm_num
  · change h 29 1 = h 1 1 + ((588086130579 : ℝ) / 717098038468) * (h 3 0 - h 1 0)
    convert homothetic_117 h H using 1 <;> norm_num
  · change h 29 2 = h 1 2 + ((654913390844 : ℝ) / 717098038468) * (h 3 0 - h 1 0)
    convert homothetic_118 h H using 1 <;> norm_num
  · change h 29 3 = h 1 3 + ((118545748644 : ℝ) / 717098038468) * (h 3 0 - h 1 0)
    convert homothetic_119 h H using 1 <;> norm_num

private theorem homothetic_vertex030 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨30, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨30, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨30, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 30 0 = h 1 0 + ((19293474916189080 : ℝ) / 39290953518325328) * (h 3 0 - h 1 0)
    convert homothetic_120 h H using 1 <;> norm_num
  · change h 30 1 = h 1 1 + ((28364274250472077 : ℝ) / 39290953518325328) * (h 3 0 - h 1 0)
    convert homothetic_121 h H using 1 <;> norm_num
  · change h 30 2 = h 1 2 + ((30814896711649892 : ℝ) / 39290953518325328) * (h 3 0 - h 1 0)
    convert homothetic_122 h H using 1 <;> norm_num
  · change h 30 3 = h 1 3 + ((9201995192741856 : ℝ) / 39290953518325328) * (h 3 0 - h 1 0)
    convert homothetic_123 h H using 1 <;> norm_num

private theorem homothetic_vertex031 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨31, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨31, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨31, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 31 0 = h 1 0 + ((3122329502632 : ℝ) / 5019686269276) * (h 3 0 - h 1 0)
    convert homothetic_124 h H using 1 <;> norm_num
  · change h 31 1 = h 1 1 + ((4116602914053 : ℝ) / 5019686269276) * (h 3 0 - h 1 0)
    convert homothetic_125 h H using 1 <;> norm_num
  · change h 31 2 = h 1 2 + ((4584393735908 : ℝ) / 5019686269276) * (h 3 0 - h 1 0)
    convert homothetic_126 h H using 1 <;> norm_num
  · change h 31 3 = h 1 3 + ((829820240508 : ℝ) / 5019686269276) * (h 3 0 - h 1 0)
    convert homothetic_127 h H using 1 <;> norm_num

private theorem homothetic_vertex032 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨32, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨32, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨32, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 32 0 = h 1 0 + ((20631022303002567255165056 : ℝ) / 43593967997045105315402336) * (h 3 0 - h 1 0)
    convert homothetic_128 h H using 1 <;> norm_num
  · change h 32 1 = h 1 1 + ((22977346258318728988718983 : ℝ) / 43593967997045105315402336) * (h 3 0 - h 1 0)
    convert homothetic_129 h H using 1 <;> norm_num
  · change h 32 2 = h 1 2 + ((34277022476771290488192312 : ℝ) / 43593967997045105315402336) * (h 3 0 - h 1 0)
    convert homothetic_130 h H using 1 <;> norm_num
  · change h 32 3 = h 1 3 + ((10342179174716050358974176 : ℝ) / 43593967997045105315402336) * (h 3 0 - h 1 0)
    convert homothetic_131 h H using 1 <;> norm_num

private theorem homothetic_vertex033 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨33, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨33, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨33, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 33 0 = h 1 0 + ((32752045938949025092020272 : ℝ) / 69650407353842049756369072) * (h 3 0 - h 1 0)
    convert homothetic_132 h H using 1 <;> norm_num
  · change h 33 1 = h 1 1 + ((36728407848088434627054561 : ℝ) / 69650407353842049756369072) * (h 3 0 - h 1 0)
    convert homothetic_133 h H using 1 <;> norm_num
  · change h 33 2 = h 1 2 + ((54173244258288834119698744 : ℝ) / 69650407353842049756369072) * (h 3 0 - h 1 0)
    convert homothetic_134 h H using 1 <;> norm_num
  · change h 33 3 = h 1 3 + ((16556086252303255881035952 : ℝ) / 69650407353842049756369072) * (h 3 0 - h 1 0)
    convert homothetic_135 h H using 1 <;> norm_num

private theorem homothetic_vertex034 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨34, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨34, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨34, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 34 0 = h 1 0 + ((71998965174915341055154712 : ℝ) / 151157195873225645395870332) * (h 3 0 - h 1 0)
    convert homothetic_136 h H using 1 <;> norm_num
  · change h 34 1 = h 1 1 + ((79648627327030898094758421 : ℝ) / 151157195873225645395870332) * (h 3 0 - h 1 0)
    convert homothetic_137 h H using 1 <;> norm_num
  · change h 34 2 = h 1 2 + ((118892073488280052516017694 : ℝ) / 151157195873225645395870332) * (h 3 0 - h 1 0)
    convert homothetic_138 h H using 1 <;> norm_num
  · change h 34 3 = h 1 3 + ((35832025220364569554866492 : ℝ) / 151157195873225645395870332) * (h 3 0 - h 1 0)
    convert homothetic_139 h H using 1 <;> norm_num

private theorem homothetic_vertex035 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨35, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨35, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨35, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 35 0 = h 1 0 + ((11012452477181888872350512 : ℝ) / 23059496543247088807794352) * (h 3 0 - h 1 0)
    convert homothetic_140 h H using 1 <;> norm_num
  · change h 35 1 = h 1 1 + ((12156889629218154062180811 : ℝ) / 23059496543247088807794352) * (h 3 0 - h 1 0)
    convert homothetic_141 h H using 1 <;> norm_num
  · change h 35 2 = h 1 2 + ((17997003212972647231928744 : ℝ) / 23059496543247088807794352) * (h 3 0 - h 1 0)
    convert homothetic_142 h H using 1 <;> norm_num
  · change h 35 3 = h 1 3 + ((5469327194431635539235312 : ℝ) / 23059496543247088807794352) * (h 3 0 - h 1 0)
    convert homothetic_143 h H using 1 <;> norm_num

private theorem homothetic_vertex036 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨36, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨36, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨36, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 36 0 = h 1 0 + ((20631022303002567255165056 : ℝ) / 43593967997045105315402336) * (h 3 0 - h 1 0)
    convert homothetic_144 h H using 1 <;> norm_num
  · change h 36 1 = h 1 1 + ((23261555189186827128125343 : ℝ) / 43593967997045105315402336) * (h 3 0 - h 1 0)
    convert homothetic_145 h H using 1 <;> norm_num
  · change h 36 2 = h 1 2 + ((34277022476771290488192312 : ℝ) / 43593967997045105315402336) * (h 3 0 - h 1 0)
    convert homothetic_146 h H using 1 <;> norm_num
  · change h 36 3 = h 1 3 + ((10342179174716050358974176 : ℝ) / 43593967997045105315402336) * (h 3 0 - h 1 0)
    convert homothetic_147 h H using 1 <;> norm_num

private theorem homothetic_vertex037 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨37, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨37, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨37, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 37 0 = h 1 0 + ((32752045938949025092020272 : ℝ) / 69650407353842049756369072) * (h 3 0 - h 1 0)
    convert homothetic_148 h H using 1 <;> norm_num
  · change h 37 1 = h 1 1 + ((37207570012527211655475201 : ℝ) / 69650407353842049756369072) * (h 3 0 - h 1 0)
    convert homothetic_149 h H using 1 <;> norm_num
  · change h 37 2 = h 1 2 + ((54173244258288834119698744 : ℝ) / 69650407353842049756369072) * (h 3 0 - h 1 0)
    convert homothetic_150 h H using 1 <;> norm_num
  · change h 37 3 = h 1 3 + ((16556086252303255881035952 : ℝ) / 69650407353842049756369072) * (h 3 0 - h 1 0)
    convert homothetic_151 h H using 1 <;> norm_num

private theorem homothetic_vertex038 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨38, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨38, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨38, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 38 0 = h 1 0 + ((35999482587457670527577356 : ℝ) / 75578597936612822697935166) * (h 3 0 - h 1 0)
    convert homothetic_152 h H using 1 <;> norm_num
  · change h 38 1 = h 1 1 + ((40332983056830511058248548 : ℝ) / 75578597936612822697935166) * (h 3 0 - h 1 0)
    convert homothetic_153 h H using 1 <;> norm_num
  · change h 38 2 = h 1 2 + ((59446036744140026258008847 : ℝ) / 75578597936612822697935166) * (h 3 0 - h 1 0)
    convert homothetic_154 h H using 1 <;> norm_num
  · change h 38 3 = h 1 3 + ((17916012610182284777433246 : ℝ) / 75578597936612822697935166) * (h 3 0 - h 1 0)
    convert homothetic_155 h H using 1 <;> norm_num

private theorem homothetic_vertex039 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨39, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨39, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨39, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 39 0 = h 1 0 + ((11012452477181888872350512 : ℝ) / 23059496543247088807794352) * (h 3 0 - h 1 0)
    convert homothetic_156 h H using 1 <;> norm_num
  · change h 39 1 = h 1 1 + ((12316610350697746404987691 : ℝ) / 23059496543247088807794352) * (h 3 0 - h 1 0)
    convert homothetic_157 h H using 1 <;> norm_num
  · change h 39 2 = h 1 2 + ((17997003212972647231928744 : ℝ) / 23059496543247088807794352) * (h 3 0 - h 1 0)
    convert homothetic_158 h H using 1 <;> norm_num
  · change h 39 3 = h 1 3 + ((5469327194431635539235312 : ℝ) / 23059496543247088807794352) * (h 3 0 - h 1 0)
    convert homothetic_159 h H using 1 <;> norm_num

private theorem homothetic_vertex040 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨40, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨40, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨40, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 40 0 = h 1 0 + ((10587999992185503947104 : ℝ) / 22541406790489933660064) * (h 3 0 - h 1 0)
    convert homothetic_160 h H using 1 <;> norm_num
  · change h 40 1 = h 1 1 + ((11748196884205232413579 : ℝ) / 22541406790489933660064) * (h 3 0 - h 1 0)
    convert homothetic_161 h H using 1 <;> norm_num
  · change h 40 2 = h 1 2 + ((17730888915597721573096 : ℝ) / 22541406790489933660064) * (h 3 0 - h 1 0)
    convert homothetic_162 h H using 1 <;> norm_num
  · change h 40 3 = h 1 3 + ((5350507353181007259936 : ℝ) / 22541406790489933660064) * (h 3 0 - h 1 0)
    convert homothetic_163 h H using 1 <;> norm_num

private theorem homothetic_vertex041 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨41, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨41, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨41, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 41 0 = h 1 0 + ((1385755762125216557168 : ℝ) / 3071407120199047912112) * (h 3 0 - h 1 0)
    convert homothetic_164 h H using 1 <;> norm_num
  · change h 41 1 = h 1 1 + ((1582787225885989341909 : ℝ) / 3071407120199047912112) * (h 3 0 - h 1 0)
    convert homothetic_165 h H using 1 <;> norm_num
  · change h 41 2 = h 1 2 + ((2293494347764053290040 : ℝ) / 3071407120199047912112) * (h 3 0 - h 1 0)
    convert homothetic_166 h H using 1 <;> norm_num
  · change h 41 3 = h 1 3 + ((736249408133750375088 : ℝ) / 3071407120199047912112) * (h 3 0 - h 1 0)
    convert homothetic_167 h H using 1 <;> norm_num

private theorem homothetic_vertex042 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨42, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨42, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨42, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 42 0 = h 1 0 + ((13295497267524074476976 : ℝ) / 27775822889558374356240) * (h 3 0 - h 1 0)
    convert homothetic_168 h H using 1 <;> norm_num
  · change h 42 1 = h 1 1 + ((14397052723137184347689 : ℝ) / 27775822889558374356240) * (h 3 0 - h 1 0)
    convert homothetic_169 h H using 1 <;> norm_num
  · change h 42 2 = h 1 2 + ((21876771090952130043656 : ℝ) / 27775822889558374356240) * (h 3 0 - h 1 0)
    convert homothetic_170 h H using 1 <;> norm_num
  · change h 42 3 = h 1 3 + ((6576739924629061478416 : ℝ) / 27775822889558374356240) * (h 3 0 - h 1 0)
    convert homothetic_171 h H using 1 <;> norm_num

private theorem homothetic_vertex043 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨43, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨43, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨43, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 43 0 = h 1 0 + ((6916152814365802751080144 : ℝ) / 14224765346051660926469904) * (h 3 0 - h 1 0)
    convert homothetic_172 h H using 1 <;> norm_num
  · change h 43 1 = h 1 1 + ((7315897915430486560522437 : ℝ) / 14224765346051660926469904) * (h 3 0 - h 1 0)
    convert homothetic_173 h H using 1 <;> norm_num
  · change h 43 2 = h 1 2 + ((10792135834680102568928888 : ℝ) / 14224765346051660926469904) * (h 3 0 - h 1 0)
    convert homothetic_174 h H using 1 <;> norm_num
  · change h 43 3 = h 1 3 + ((3374848748911646281466064 : ℝ) / 14224765346051660926469904) * (h 3 0 - h 1 0)
    convert homothetic_175 h H using 1 <;> norm_num

private theorem homothetic_vertex044 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨44, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨44, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨44, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 44 0 = h 1 0 + ((10587999992185503947104 : ℝ) / 22541406790489933660064) * (h 3 0 - h 1 0)
    convert homothetic_176 h H using 1 <;> norm_num
  · change h 44 1 = h 1 1 + ((12145691892412362678483 : ℝ) / 22541406790489933660064) * (h 3 0 - h 1 0)
    convert homothetic_177 h H using 1 <;> norm_num
  · change h 44 2 = h 1 2 + ((17730888915597721573096 : ℝ) / 22541406790489933660064) * (h 3 0 - h 1 0)
    convert homothetic_178 h H using 1 <;> norm_num
  · change h 44 3 = h 1 3 + ((5350507353181007259936 : ℝ) / 22541406790489933660064) * (h 3 0 - h 1 0)
    convert homothetic_179 h H using 1 <;> norm_num

private theorem homothetic_vertex045 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨45, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨45, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨45, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 45 0 = h 1 0 + ((1385755762125216557168 : ℝ) / 3071407120199047912112) * (h 3 0 - h 1 0)
    convert homothetic_180 h H using 1 <;> norm_num
  · change h 45 1 = h 1 1 + ((1682925609258774509813 : ℝ) / 3071407120199047912112) * (h 3 0 - h 1 0)
    convert homothetic_181 h H using 1 <;> norm_num
  · change h 45 2 = h 1 2 + ((2293494347764053290040 : ℝ) / 3071407120199047912112) * (h 3 0 - h 1 0)
    convert homothetic_182 h H using 1 <;> norm_num
  · change h 45 3 = h 1 3 + ((736249408133750375088 : ℝ) / 3071407120199047912112) * (h 3 0 - h 1 0)
    convert homothetic_183 h H using 1 <;> norm_num

private theorem homothetic_vertex046 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨46, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨46, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨46, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 46 0 = h 1 0 + ((13295497267524074476976 : ℝ) / 27775822889558374356240) * (h 3 0 - h 1 0)
    convert homothetic_184 h H using 1 <;> norm_num
  · change h 46 1 = h 1 1 + ((15029431145284891587309 : ℝ) / 27775822889558374356240) * (h 3 0 - h 1 0)
    convert homothetic_185 h H using 1 <;> norm_num
  · change h 46 2 = h 1 2 + ((21876771090952130043656 : ℝ) / 27775822889558374356240) * (h 3 0 - h 1 0)
    convert homothetic_186 h H using 1 <;> norm_num
  · change h 46 3 = h 1 3 + ((6576739924629061478416 : ℝ) / 27775822889558374356240) * (h 3 0 - h 1 0)
    convert homothetic_187 h H using 1 <;> norm_num

private theorem homothetic_vertex047 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨47, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨47, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨47, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 47 0 = h 1 0 + ((6916152814365802751080144 : ℝ) / 14224765346051660926469904) * (h 3 0 - h 1 0)
    convert homothetic_188 h H using 1 <;> norm_num
  · change h 47 1 = h 1 1 + ((7795060079869263588943077 : ℝ) / 14224765346051660926469904) * (h 3 0 - h 1 0)
    convert homothetic_189 h H using 1 <;> norm_num
  · change h 47 2 = h 1 2 + ((10792135834680102568928888 : ℝ) / 14224765346051660926469904) * (h 3 0 - h 1 0)
    convert homothetic_190 h H using 1 <;> norm_num
  · change h 47 3 = h 1 3 + ((3374848748911646281466064 : ℝ) / 14224765346051660926469904) * (h 3 0 - h 1 0)
    convert homothetic_191 h H using 1 <;> norm_num

private theorem homothetic_vertex048 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨48, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨48, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨48, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 48 0 = h 1 0 + ((496659593780964693269920504000 : ℝ) / 1045616881782826808829398195552) * (h 3 0 - h 1 0)
    convert homothetic_192 h H using 1 <;> norm_num
  · change h 48 1 = h 1 1 + ((550094978867967299599421436073 : ℝ) / 1045616881782826808829398195552) * (h 3 0 - h 1 0)
    convert homothetic_193 h H using 1 <;> norm_num
  · change h 48 2 = h 1 2 + ((821682077579475289258482455176 : ℝ) / 1045616881782826808829398195552) * (h 3 0 - h 1 0)
    convert homothetic_194 h H using 1 <;> norm_num
  · change h 48 3 = h 1 3 + ((247978462251592343276037429216 : ℝ) / 1045616881782826808829398195552) * (h 3 0 - h 1 0)
    convert homothetic_195 h H using 1 <;> norm_num

private theorem homothetic_vertex049 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨49, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨49, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨49, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 49 0 = h 1 0 + ((12381876063138689842785565376 : ℝ) / 26098535765767225002740465056) * (h 3 0 - h 1 0)
    convert homothetic_196 h H using 1 <;> norm_num
  · change h 49 1 = h 1 1 + ((13732829524213089535259041889 : ℝ) / 26098535765767225002740465056) * (h 3 0 - h 1 0)
    convert homothetic_197 h H using 1 <;> norm_num
  · change h 49 2 = h 1 2 + ((20475887603446782897110556008 : ℝ) / 26098535765767225002740465056) * (h 3 0 - h 1 0)
    convert homothetic_198 h H using 1 <;> norm_num
  · change h 49 3 = h 1 3 + ((6191501658673746915968217600 : ℝ) / 26098535765767225002740465056) * (h 3 0 - h 1 0)
    convert homothetic_199 h H using 1 <;> norm_num

private theorem homothetic_vertex050 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨50, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨50, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨50, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 50 0 = h 1 0 + ((3945181245705771740379891605520 : ℝ) / 8300078906963278004742696816368) * (h 3 0 - h 1 0)
    convert homothetic_200 h H using 1 <;> norm_num
  · change h 50 1 = h 1 1 + ((4366642872826104676091635747493 : ℝ) / 8300078906963278004742696816368) * (h 3 0 - h 1 0)
    convert homothetic_201 h H using 1 <;> norm_num
  · change h 50 2 = h 1 2 + ((6522817477036909934543124518120 : ℝ) / 8300078906963278004742696816368) * (h 3 0 - h 1 0)
    convert homothetic_202 h H using 1 <;> norm_num
  · change h 50 3 = h 1 3 + ((1968276488398966567191832757808 : ℝ) / 8300078906963278004742696816368) * (h 3 0 - h 1 0)
    convert homothetic_203 h H using 1 <;> norm_num

private theorem homothetic_vertex051 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨51, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨51, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨51, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 51 0 = h 1 0 + ((185973651486459757674072883312 : ℝ) / 391071951284919650983072509072) * (h 3 0 - h 1 0)
    convert homothetic_204 h H using 1 <;> norm_num
  · change h 51 1 = h 1 1 + ((205770658487742909743824942191 : ℝ) / 391071951284919650983072509072) * (h 3 0 - h 1 0)
    convert homothetic_205 h H using 1 <;> norm_num
  · change h 51 2 = h 1 2 + ((306981501161733090525881623544 : ℝ) / 391071951284919650983072509072) * (h 3 0 - h 1 0)
    convert homothetic_206 h H using 1 <;> norm_num
  · change h 51 3 = h 1 3 + ((92745080812424519198427785232 : ℝ) / 391071951284919650983072509072) * (h 3 0 - h 1 0)
    convert homothetic_207 h H using 1 <;> norm_num

private theorem homothetic_vertex052 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨52, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨52, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨52, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 52 0 = h 1 0 + ((275917504138499526067541080808 : ℝ) / 581395530390869120698228605208) * (h 3 0 - h 1 0)
    convert homothetic_208 h H using 1 <;> norm_num
  · change h 52 1 = h 1 1 + ((310361656748375544205985042169 : ℝ) / 581395530390869120698228605208) * (h 3 0 - h 1 0)
    convert homothetic_209 h H using 1 <;> norm_num
  · change h 52 2 = h 1 2 + ((456942339186957751005884982896 : ℝ) / 581395530390869120698228605208) * (h 3 0 - h 1 0)
    convert homothetic_210 h H using 1 <;> norm_num
  · change h 52 3 = h 1 3 + ((137894656836962159564201929848 : ℝ) / 581395530390869120698228605208) * (h 3 0 - h 1 0)
    convert homothetic_211 h H using 1 <;> norm_num

private theorem homothetic_vertex053 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨53, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨53, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨53, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 53 0 = h 1 0 + ((59984697269395718694935992 : ℝ) / 126864826990784360612753192) * (h 3 0 - h 1 0)
    convert homothetic_212 h H using 1 <;> norm_num
  · change h 53 1 = h 1 1 + ((67753278475216386708530091 : ℝ) / 126864826990784360612753192) * (h 3 0 - h 1 0)
    convert homothetic_213 h H using 1 <;> norm_num
  · change h 53 2 = h 1 2 + ((99204426531276861283627264 : ℝ) / 126864826990784360612753192) * (h 3 0 - h 1 0)
    convert homothetic_214 h H using 1 <;> norm_num
  · change h 53 3 = h 1 3 + ((30119522468363034008237592 : ℝ) / 126864826990784360612753192) * (h 3 0 - h 1 0)
    convert homothetic_215 h H using 1 <;> norm_num

private theorem homothetic_vertex054 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨54, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨54, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨54, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 54 0 = h 1 0 + ((2194246195683291550979927303472 : ℝ) / 4613625110444969192467842115072) * (h 3 0 - h 1 0)
    convert homothetic_216 h H using 1 <;> norm_num
  · change h 54 1 = h 1 1 + ((2462877092205180514685636204021 : ℝ) / 4613625110444969192467842115072) * (h 3 0 - h 1 0)
    convert homothetic_217 h H using 1 <;> norm_num
  · change h 54 2 = h 1 2 + ((3626605216410689955161741578864 : ℝ) / 4613625110444969192467842115072) * (h 3 0 - h 1 0)
    convert homothetic_218 h H using 1 <;> norm_num
  · change h 54 3 = h 1 3 + ((1093957773807952028555129658432 : ℝ) / 4613625110444969192467842115072) * (h 3 0 - h 1 0)
    convert homothetic_219 h H using 1 <;> norm_num

private theorem homothetic_vertex055 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨55, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨55, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨55, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 55 0 = h 1 0 + ((252977115479439760085095280 : ℝ) / 531109773668326455408164448) * (h 3 0 - h 1 0)
    convert homothetic_220 h H using 1 <;> norm_num
  · change h 55 1 = h 1 1 + ((283623022390324824767957115 : ℝ) / 531109773668326455408164448) * (h 3 0 - h 1 0)
    convert homothetic_221 h H using 1 <;> norm_num
  · change h 55 2 = h 1 2 + ((415993435070659060043953840 : ℝ) / 531109773668326455408164448) * (h 3 0 - h 1 0)
    convert homothetic_222 h H using 1 <;> norm_num
  · change h 55 3 = h 1 3 + ((125961412325244268023443328 : ℝ) / 531109773668326455408164448) * (h 3 0 - h 1 0)
    convert homothetic_223 h H using 1 <;> norm_num

private theorem homothetic_vertex056 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨56, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨56, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨56, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 56 0 = h 1 0 + ((910353884670623831407352 : ℝ) / 1923008533711279939163200) * (h 3 0 - h 1 0)
    convert homothetic_224 h H using 1 <;> norm_num
  · change h 56 1 = h 1 1 + ((934816436068939411244123 : ℝ) / 1923008533711279939163200) * (h 3 0 - h 1 0)
    convert homothetic_225 h H using 1 <;> norm_num
  · change h 56 2 = h 1 2 + ((1605442100547335975360432 : ℝ) / 1923008533711279939163200) * (h 3 0 - h 1 0)
    convert homothetic_226 h H using 1 <;> norm_num
  · change h 56 3 = h 1 3 + ((408312046720902374603232 : ℝ) / 1923008533711279939163200) * (h 3 0 - h 1 0)
    convert homothetic_227 h H using 1 <;> norm_num

private theorem homothetic_vertex057 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨57, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨57, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨57, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 57 0 = h 1 0 + ((181149315699781646744672 : ℝ) / 383558463993790758399480) * (h 3 0 - h 1 0)
    convert homothetic_228 h H using 1 <;> norm_num
  · change h 57 1 = h 1 1 + ((201995350963450366325643 : ℝ) / 383558463993790758399480) * (h 3 0 - h 1 0)
    convert homothetic_229 h H using 1 <;> norm_num
  · change h 57 2 = h 1 2 + ((303562265326368605834072 : ℝ) / 383558463993790758399480) * (h 3 0 - h 1 0)
    convert homothetic_230 h H using 1 <;> norm_num
  · change h 57 3 = h 1 3 + ((90146211177649430529112 : ℝ) / 383558463993790758399480) * (h 3 0 - h 1 0)
    convert homothetic_231 h H using 1 <;> norm_num

private theorem homothetic_vertex058 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨58, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨58, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨58, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 58 0 = h 1 0 + ((9948357375023189514504304 : ℝ) / 19699030405131969967718240) * (h 3 0 - h 1 0)
    convert homothetic_232 h H using 1 <;> norm_num
  · change h 58 1 = h 1 1 + ((9630627783411212560211751 : ℝ) / 19699030405131969967718240) * (h 3 0 - h 1 0)
    convert homothetic_233 h H using 1 <;> norm_num
  · change h 58 2 = h 1 2 + ((16432430943662093694607184 : ℝ) / 19699030405131969967718240) * (h 3 0 - h 1 0)
    convert homothetic_234 h H using 1 <;> norm_num
  · change h 58 3 = h 1 3 + ((4190781066628757864646784 : ℝ) / 19699030405131969967718240) * (h 3 0 - h 1 0)
    convert homothetic_235 h H using 1 <;> norm_num

private theorem homothetic_vertex059 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨59, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨59, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨59, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 59 0 = h 1 0 + ((529787797170143595009788 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0)
    convert homothetic_236 h H using 1 <;> norm_num
  · change h 59 1 = h 1 1 + ((578749084305489324838032 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0)
    convert homothetic_237 h H using 1 <;> norm_num
  · change h 59 2 = h 1 2 + ((874063471235004430739378 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0)
    convert homothetic_238 h H using 1 <;> norm_num
  · change h 59 3 = h 1 3 + ((257588362112298345612543 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0)
    convert homothetic_239 h H using 1 <;> norm_num

private theorem homothetic_vertex060 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨60, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨60, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨60, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 60 0 = h 1 0 + ((910353884670623831407352 : ℝ) / 1923008533711279939163200) * (h 3 0 - h 1 0)
    convert homothetic_240 h H using 1 <;> norm_num
  · change h 60 1 = h 1 1 + ((1076920901502988480947303 : ℝ) / 1923008533711279939163200) * (h 3 0 - h 1 0)
    convert homothetic_241 h H using 1 <;> norm_num
  · change h 60 2 = h 1 2 + ((1605442100547335975360432 : ℝ) / 1923008533711279939163200) * (h 3 0 - h 1 0)
    convert homothetic_242 h H using 1 <;> norm_num
  · change h 60 3 = h 1 3 + ((408312046720902374603232 : ℝ) / 1923008533711279939163200) * (h 3 0 - h 1 0)
    convert homothetic_243 h H using 1 <;> norm_num

private theorem homothetic_vertex061 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨61, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨61, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨61, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 61 0 = h 1 0 + ((181149315699781646744672 : ℝ) / 383558463993790758399480) * (h 3 0 - h 1 0)
    convert homothetic_244 h H using 1 <;> norm_num
  · change h 61 1 = h 1 1 + ((204749156506201958443003 : ℝ) / 383558463993790758399480) * (h 3 0 - h 1 0)
    convert homothetic_245 h H using 1 <;> norm_num
  · change h 61 2 = h 1 2 + ((303562265326368605834072 : ℝ) / 383558463993790758399480) * (h 3 0 - h 1 0)
    convert homothetic_246 h H using 1 <;> norm_num
  · change h 61 3 = h 1 3 + ((90146211177649430529112 : ℝ) / 383558463993790758399480) * (h 3 0 - h 1 0)
    convert homothetic_247 h H using 1 <;> norm_num

private theorem homothetic_vertex062 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨62, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨62, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨62, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 62 0 = h 1 0 + ((9948357375023189514504304 : ℝ) / 19699030405131969967718240) * (h 3 0 - h 1 0)
    convert homothetic_248 h H using 1 <;> norm_num
  · change h 62 1 = h 1 1 + ((10987079498918044589196651 : ℝ) / 19699030405131969967718240) * (h 3 0 - h 1 0)
    convert homothetic_249 h H using 1 <;> norm_num
  · change h 62 2 = h 1 2 + ((16432430943662093694607184 : ℝ) / 19699030405131969967718240) * (h 3 0 - h 1 0)
    convert homothetic_250 h H using 1 <;> norm_num
  · change h 62 3 = h 1 3 + ((4190781066628757864646784 : ℝ) / 19699030405131969967718240) * (h 3 0 - h 1 0)
    convert homothetic_251 h H using 1 <;> norm_num

private theorem homothetic_vertex063 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨63, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨63, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨63, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 63 0 = h 1 0 + ((529787797170143595009788 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0)
    convert homothetic_252 h H using 1 <;> norm_num
  · change h 63 1 = h 1 1 + ((588731629397963846263462 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0)
    convert homothetic_253 h H using 1 <;> norm_num
  · change h 63 2 = h 1 2 + ((874063471235004430739378 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0)
    convert homothetic_254 h H using 1 <;> norm_num
  · change h 63 3 = h 1 3 + ((257588362112298345612543 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0)
    convert homothetic_255 h H using 1 <;> norm_num

private theorem homothetic_vertex064 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨64, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨64, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨64, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 64 0 = h 1 0 + ((14015384281288469024512 : ℝ) / 29811274973339113635784) * (h 3 0 - h 1 0)
    convert homothetic_256 h H using 1 <;> norm_num
  · change h 64 1 = h 1 1 + ((15699441442694853759603 : ℝ) / 29811274973339113635784) * (h 3 0 - h 1 0)
    convert homothetic_257 h H using 1 <;> norm_num
  · change h 64 2 = h 1 2 + ((23480517613140806239176 : ℝ) / 29811274973339113635784) * (h 3 0 - h 1 0)
    convert homothetic_258 h H using 1 <;> norm_num
  · change h 64 3 = h 1 3 + ((7062983877555051235752 : ℝ) / 29811274973339113635784) * (h 3 0 - h 1 0)
    convert homothetic_259 h H using 1 <;> norm_num

private theorem homothetic_vertex065 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨65, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨65, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨65, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 65 0 = h 1 0 + ((1840062978149559063847168 : ℝ) / 3837161186404689159271580) * (h 3 0 - h 1 0)
    convert homothetic_260 h H using 1 <;> norm_num
  · change h 65 1 = h 1 1 + ((2015720189903314992363807 : ℝ) / 3837161186404689159271580) * (h 3 0 - h 1 0)
    convert homothetic_261 h H using 1 <;> norm_num
  · change h 65 2 = h 1 2 + ((3027587737908757983425448 : ℝ) / 3837161186404689159271580) * (h 3 0 - h 1 0)
    convert homothetic_262 h H using 1 <;> norm_num
  · change h 65 3 = h 1 3 + ((906283185863747721766508 : ℝ) / 3837161186404689159271580) * (h 3 0 - h 1 0)
    convert homothetic_263 h H using 1 <;> norm_num

private theorem homothetic_vertex066 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨66, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨66, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨66, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 66 0 = h 1 0 + ((14015384281288469024512 : ℝ) / 29811274973339113635784) * (h 3 0 - h 1 0)
    convert homothetic_264 h H using 1 <;> norm_num
  · change h 66 1 = h 1 1 + ((15937830579231558748867 : ℝ) / 29811274973339113635784) * (h 3 0 - h 1 0)
    convert homothetic_265 h H using 1 <;> norm_num
  · change h 66 2 = h 1 2 + ((23480517613140806239176 : ℝ) / 29811274973339113635784) * (h 3 0 - h 1 0)
    convert homothetic_266 h H using 1 <;> norm_num
  · change h 66 3 = h 1 3 + ((7062983877555051235752 : ℝ) / 29811274973339113635784) * (h 3 0 - h 1 0)
    convert homothetic_267 h H using 1 <;> norm_num

private theorem homothetic_vertex067 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨67, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨67, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨67, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 67 0 = h 1 0 + ((1840062978149559063847168 : ℝ) / 3837161186404689159271580) * (h 3 0 - h 1 0)
    convert homothetic_268 h H using 1 <;> norm_num
  · change h 67 1 = h 1 1 + ((2055650370273213078065527 : ℝ) / 3837161186404689159271580) * (h 3 0 - h 1 0)
    convert homothetic_269 h H using 1 <;> norm_num
  · change h 67 2 = h 1 2 + ((3027587737908757983425448 : ℝ) / 3837161186404689159271580) * (h 3 0 - h 1 0)
    convert homothetic_270 h H using 1 <;> norm_num
  · change h 67 3 = h 1 3 + ((906283185863747721766508 : ℝ) / 3837161186404689159271580) * (h 3 0 - h 1 0)
    convert homothetic_271 h H using 1 <;> norm_num

private theorem homothetic_vertex068 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨68, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨68, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨68, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 68 0 = h 1 0 + ((39506306678791435906549233512 : ℝ) / 81354225799957920226747434208) * (h 3 0 - h 1 0)
    convert homothetic_272 h H using 1 <;> norm_num
  · change h 68 1 = h 1 1 + ((40596238269230557822406629745 : ℝ) / 81354225799957920226747434208) * (h 3 0 - h 1 0)
    convert homothetic_273 h H using 1 <;> norm_num
  · change h 68 2 = h 1 2 + ((66381187968361055676693878672 : ℝ) / 81354225799957920226747434208) * (h 3 0 - h 1 0)
    convert homothetic_274 h H using 1 <;> norm_num
  · change h 68 3 = h 1 3 + ((18088020254783007242164833600 : ℝ) / 81354225799957920226747434208) * (h 3 0 - h 1 0)
    convert homothetic_275 h H using 1 <;> norm_num

private theorem homothetic_vertex069 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨69, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨69, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨69, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 69 0 = h 1 0 + ((3561843594688596297246743744 : ℝ) / 7434366338618829406811987440) * (h 3 0 - h 1 0)
    convert homothetic_276 h H using 1 <;> norm_num
  · change h 69 1 = h 1 1 + ((3818379522142608901893272387 : ℝ) / 7434366338618829406811987440) * (h 3 0 - h 1 0)
    convert homothetic_277 h H using 1 <;> norm_num
  · change h 69 2 = h 1 2 + ((5968111744515383677732547000 : ℝ) / 7434366338618829406811987440) * (h 3 0 - h 1 0)
    convert homothetic_278 h H using 1 <;> norm_num
  · change h 69 3 = h 1 3 + ((1703693390669959246095735408 : ℝ) / 7434366338618829406811987440) * (h 3 0 - h 1 0)
    convert homothetic_279 h H using 1 <;> norm_num

private theorem homothetic_vertex070 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨70, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨70, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨70, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 70 0 = h 1 0 + ((314706619918718867089369821168 : ℝ) / 645261899548154685277523888872) * (h 3 0 - h 1 0)
    convert homothetic_280 h H using 1 <;> norm_num
  · change h 70 1 = h 1 1 + ((321974428085998725597296933773 : ℝ) / 645261899548154685277523888872) * (h 3 0 - h 1 0)
    convert homothetic_281 h H using 1 <;> norm_num
  · change h 70 2 = h 1 2 + ((526685380763377917373561862416 : ℝ) / 645261899548154685277523888872) * (h 3 0 - h 1 0)
    convert homothetic_282 h H using 1 <;> norm_num
  · change h 70 3 = h 1 3 + ((143371129271809814974925326632 : ℝ) / 645261899548154685277523888872) * (h 3 0 - h 1 0)
    convert homothetic_283 h H using 1 <;> norm_num

private theorem homothetic_vertex071 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨71, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨71, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨71, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 71 0 = h 1 0 + ((2007794395952639536868580632 : ℝ) / 4149012134993127655033248390) * (h 3 0 - h 1 0)
    convert homothetic_284 h H using 1 <;> norm_num
  · change h 71 1 = h 1 1 + ((2122341129024522150111233753 : ℝ) / 4149012134993127655033248390) * (h 3 0 - h 1 0)
    convert homothetic_285 h H using 1 <;> norm_num
  · change h 71 2 = h 1 2 + ((3340521936795841080313723982 : ℝ) / 4149012134993127655033248390) * (h 3 0 - h 1 0)
    convert homothetic_286 h H using 1 <;> norm_num
  · change h 71 3 = h 1 3 + ((945729533655826803074339782 : ℝ) / 4149012134993127655033248390) * (h 3 0 - h 1 0)
    convert homothetic_287 h H using 1 <;> norm_num

private theorem homothetic_vertex072 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨72, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨72, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨72, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 72 0 = h 1 0 + ((39252282853258009002717797192 : ℝ) / 81138282544257715319191235080) * (h 3 0 - h 1 0)
    convert homothetic_288 h H using 1 <;> norm_num
  · change h 72 1 = h 1 1 + ((44687036887344659550100205613 : ℝ) / 81138282544257715319191235080) * (h 3 0 - h 1 0)
    convert homothetic_289 h H using 1 <;> norm_num
  · change h 72 2 = h 1 2 + ((66436004652674444316500618672 : ℝ) / 81138282544257715319191235080) * (h 3 0 - h 1 0)
    convert homothetic_290 h H using 1 <;> norm_num
  · change h 72 3 = h 1 3 + ((17917740230244215385586788552 : ℝ) / 81138282544257715319191235080) * (h 3 0 - h 1 0)
    convert homothetic_291 h H using 1 <;> norm_num

private theorem homothetic_vertex073 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨73, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨73, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨73, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 73 0 = h 1 0 + ((65310823331595043303375616 : ℝ) / 137642270394160616208130240) * (h 3 0 - h 1 0)
    convert homothetic_292 h H using 1 <;> norm_num
  · change h 73 1 = h 1 1 + ((73792219984703345486771169 : ℝ) / 137642270394160616208130240) * (h 3 0 - h 1 0)
    convert homothetic_293 h H using 1 <;> norm_num
  · change h 73 2 = h 1 2 + ((109441039844199214799071976 : ℝ) / 137642270394160616208130240) * (h 3 0 - h 1 0)
    convert homothetic_294 h H using 1 <;> norm_num
  · change h 73 3 = h 1 3 + ((32087951570457945125314176 : ℝ) / 137642270394160616208130240) * (h 3 0 - h 1 0)
    convert homothetic_295 h H using 1 <;> norm_num

private theorem homothetic_vertex074 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨74, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨74, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨74, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 74 0 = h 1 0 + ((315322114767272570186652864528 : ℝ) / 642000616878594036231713212720) * (h 3 0 - h 1 0)
    convert homothetic_296 h H using 1 <;> norm_num
  · change h 74 1 = h 1 1 + ((353642629134415506844988262617 : ℝ) / 642000616878594036231713212720) * (h 3 0 - h 1 0)
    convert homothetic_297 h H using 1 <;> norm_num
  · change h 74 2 = h 1 2 + ((526311258041626707790792451248 : ℝ) / 642000616878594036231713212720) * (h 3 0 - h 1 0)
    convert homothetic_298 h H using 1 <;> norm_num
  · change h 74 3 = h 1 3 + ((141441318106511515246189228368 : ℝ) / 642000616878594036231713212720) * (h 3 0 - h 1 0)
    convert homothetic_299 h H using 1 <;> norm_num

private theorem homothetic_vertex075 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨75, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨75, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨75, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 75 0 = h 1 0 + ((7266288610244526108704 : ℝ) / 15073723378247361660612) * (h 3 0 - h 1 0)
    convert homothetic_300 h H using 1 <;> norm_num
  · change h 75 1 = h 1 1 + ((8097701956329756422637 : ℝ) / 15073723378247361660612) * (h 3 0 - h 1 0)
    convert homothetic_301 h H using 1 <;> norm_num
  · change h 75 2 = h 1 2 + ((12023881457031766930853 : ℝ) / 15073723378247361660612) * (h 3 0 - h 1 0)
    convert homothetic_302 h H using 1 <;> norm_num
  · change h 75 3 = h 1 3 + ((3494076923438998582792 : ℝ) / 15073723378247361660612) * (h 3 0 - h 1 0)
    convert homothetic_303 h H using 1 <;> norm_num

private theorem homothetic_vertex076 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨76, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨76, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨76, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 76 0 = h 1 0 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0)
    convert homothetic_304 h H using 1 <;> norm_num
  · change h 76 1 = h 1 1 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0)
    convert homothetic_305 h H using 1 <;> norm_num
  · change h 76 2 = h 1 2 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0)
    convert homothetic_306 h H using 1 <;> norm_num
  · change h 76 3 = h 1 3 + (((-29636437161 : ℤ) : ℝ) / 120001635295) * (h 3 0 - h 1 0)
    convert homothetic_307 h H using 1 <;> norm_num

private theorem homothetic_vertex077 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨77, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨77, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨77, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 77 0 = h 1 0 + ((351581980149 : ℝ) / 999528331908) * (h 3 0 - h 1 0)
    convert homothetic_308 h H using 1 <;> norm_num
  · change h 77 1 = h 1 1 + ((519521790728 : ℝ) / 999528331908) * (h 3 0 - h 1 0)
    convert homothetic_309 h H using 1 <;> norm_num
  · change h 77 2 = h 1 2 + ((351581980149 : ℝ) / 999528331908) * (h 3 0 - h 1 0)
    convert homothetic_310 h H using 1 <;> norm_num
  · change h 77 3 = h 1 3 + (((-237091497288 : ℤ) : ℝ) / 999528331908) * (h 3 0 - h 1 0)
    convert homothetic_311 h H using 1 <;> norm_num

private theorem homothetic_vertex078 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨78, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨78, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨78, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 78 0 = h 1 0 + ((90365198134 : ℝ) / 240003270590) * (h 3 0 - h 1 0)
    convert homothetic_312 h H using 1 <;> norm_num
  · change h 78 1 = h 1 1 + ((90365198134 : ℝ) / 240003270590) * (h 3 0 - h 1 0)
    convert homothetic_313 h H using 1 <;> norm_num
  · change h 78 2 = h 1 2 + ((160679098065 : ℝ) / 240003270590) * (h 3 0 - h 1 0)
    convert homothetic_314 h H using 1 <;> norm_num
  · change h 78 3 = h 1 3 + (((-59272874322 : ℤ) : ℝ) / 240003270590) * (h 3 0 - h 1 0)
    convert homothetic_315 h H using 1 <;> norm_num

private theorem homothetic_vertex079 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨79, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨79, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨79, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 79 0 = h 1 0 + ((703163960298 : ℝ) / 1999056663816) * (h 3 0 - h 1 0)
    convert homothetic_316 h H using 1 <;> norm_num
  · change h 79 1 = h 1 1 + ((1039043581456 : ℝ) / 1999056663816) * (h 3 0 - h 1 0)
    convert homothetic_317 h H using 1 <;> norm_num
  · change h 79 2 = h 1 2 + ((1374342096003 : ℝ) / 1999056663816) * (h 3 0 - h 1 0)
    convert homothetic_318 h H using 1 <;> norm_num
  · change h 79 3 = h 1 3 + (((-474182994576 : ℤ) : ℝ) / 1999056663816) * (h 3 0 - h 1 0)
    convert homothetic_319 h H using 1 <;> norm_num

private theorem homothetic_vertex080 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨80, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨80, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨80, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 80 0 = h 1 0 + ((74819036228 : ℝ) / 120001635295) * (h 3 0 - h 1 0)
    convert homothetic_320 h H using 1 <;> norm_num
  · change h 80 1 = h 1 1 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0)
    convert homothetic_321 h H using 1 <;> norm_num
  · change h 80 2 = h 1 2 + ((45182599067 : ℝ) / 120001635295) * (h 3 0 - h 1 0)
    convert homothetic_322 h H using 1 <;> norm_num
  · change h 80 3 = h 1 3 + (((-29636437161 : ℤ) : ℝ) / 120001635295) * (h 3 0 - h 1 0)
    convert homothetic_323 h H using 1 <;> norm_num

private theorem homothetic_vertex081 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨81, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨81, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨81, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 81 0 = h 1 0 + ((657825164146 : ℝ) / 999528331908) * (h 3 0 - h 1 0)
    convert homothetic_324 h H using 1 <;> norm_num
  · change h 81 1 = h 1 1 + ((519521790728 : ℝ) / 999528331908) * (h 3 0 - h 1 0)
    convert homothetic_325 h H using 1 <;> norm_num
  · change h 81 2 = h 1 2 + ((351581980149 : ℝ) / 999528331908) * (h 3 0 - h 1 0)
    convert homothetic_326 h H using 1 <;> norm_num
  · change h 81 3 = h 1 3 + (((-237091497288 : ℤ) : ℝ) / 999528331908) * (h 3 0 - h 1 0)
    convert homothetic_327 h H using 1 <;> norm_num

private theorem homothetic_vertex082 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨82, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨82, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨82, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 82 0 = h 1 0 + ((149638072456 : ℝ) / 240003270590) * (h 3 0 - h 1 0)
    convert homothetic_328 h H using 1 <;> norm_num
  · change h 82 1 = h 1 1 + ((90365198134 : ℝ) / 240003270590) * (h 3 0 - h 1 0)
    convert homothetic_329 h H using 1 <;> norm_num
  · change h 82 2 = h 1 2 + ((160679098065 : ℝ) / 240003270590) * (h 3 0 - h 1 0)
    convert homothetic_330 h H using 1 <;> norm_num
  · change h 82 3 = h 1 3 + (((-59272874322 : ℤ) : ℝ) / 240003270590) * (h 3 0 - h 1 0)
    convert homothetic_331 h H using 1 <;> norm_num

private theorem homothetic_vertex083 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨83, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨83, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨83, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 83 0 = h 1 0 + ((1315650328292 : ℝ) / 1999056663816) * (h 3 0 - h 1 0)
    convert homothetic_332 h H using 1 <;> norm_num
  · change h 83 1 = h 1 1 + ((1039043581456 : ℝ) / 1999056663816) * (h 3 0 - h 1 0)
    convert homothetic_333 h H using 1 <;> norm_num
  · change h 83 2 = h 1 2 + ((1374342096003 : ℝ) / 1999056663816) * (h 3 0 - h 1 0)
    convert homothetic_334 h H using 1 <;> norm_num
  · change h 83 3 = h 1 3 + (((-474182994576 : ℤ) : ℝ) / 1999056663816) * (h 3 0 - h 1 0)
    convert homothetic_335 h H using 1 <;> norm_num

private theorem homothetic_vertex084 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨84, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨84, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨84, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 84 0 = h 1 0 + ((158648699407709 : ℝ) / 617857941263449) * (h 3 0 - h 1 0)
    convert homothetic_336 h H using 1 <;> norm_num
  · change h 84 1 = h 1 1 + ((282243102288077 : ℝ) / 617857941263449) * (h 3 0 - h 1 0)
    convert homothetic_337 h H using 1 <;> norm_num
  · change h 84 2 = h 1 2 + ((158648699407709 : ℝ) / 617857941263449) * (h 3 0 - h 1 0)
    convert homothetic_338 h H using 1 <;> norm_num
  · change h 84 3 = h 1 3 + (((-144596176908519 : ℤ) : ℝ) / 617857941263449) * (h 3 0 - h 1 0)
    convert homothetic_339 h H using 1 <;> norm_num

private theorem homothetic_vertex085 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨85, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨85, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨85, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 85 0 = h 1 0 + ((2975709287677 : ℝ) / 13520913290240) * (h 3 0 - h 1 0)
    convert homothetic_340 h H using 1 <;> norm_num
  · change h 85 1 = h 1 1 + ((5880080129455 : ℝ) / 13520913290240) * (h 3 0 - h 1 0)
    convert homothetic_341 h H using 1 <;> norm_num
  · change h 85 2 = h 1 2 + ((2975709287677 : ℝ) / 13520913290240) * (h 3 0 - h 1 0)
    convert homothetic_342 h H using 1 <;> norm_num
  · change h 85 3 = h 1 3 + (((-2904370841778 : ℤ) : ℝ) / 13520913290240) * (h 3 0 - h 1 0)
    convert homothetic_343 h H using 1 <;> norm_num

private theorem homothetic_vertex086 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨86, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨86, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨86, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 86 0 = h 1 0 + ((42614921436437 : ℝ) / 167585073310154) * (h 3 0 - h 1 0)
    convert homothetic_344 h H using 1 <;> norm_num
  · change h 86 1 = h 1 1 + ((79926674830002 : ℝ) / 167585073310154) * (h 3 0 - h 1 0)
    convert homothetic_345 h H using 1 <;> norm_num
  · change h 86 2 = h 1 2 + ((42614921436437 : ℝ) / 167585073310154) * (h 3 0 - h 1 0)
    convert homothetic_346 h H using 1 <;> norm_num
  · change h 86 3 = h 1 3 + (((-39001551303876 : ℤ) : ℝ) / 167585073310154) * (h 3 0 - h 1 0)
    convert homothetic_347 h H using 1 <;> norm_num

private theorem homothetic_vertex087 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨87, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨87, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨87, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 87 0 = h 1 0 + ((2975709287677 : ℝ) / 13520913290240) * (h 3 0 - h 1 0)
    convert homothetic_348 h H using 1 <;> norm_num
  · change h 87 1 = h 1 1 + ((6880164606986 : ℝ) / 13520913290240) * (h 3 0 - h 1 0)
    convert homothetic_349 h H using 1 <;> norm_num
  · change h 87 2 = h 1 2 + ((2975709287677 : ℝ) / 13520913290240) * (h 3 0 - h 1 0)
    convert homothetic_350 h H using 1 <;> norm_num
  · change h 87 3 = h 1 3 + (((-2904370841778 : ℤ) : ℝ) / 13520913290240) * (h 3 0 - h 1 0)
    convert homothetic_351 h H using 1 <;> norm_num

private theorem homothetic_vertex088 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨88, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨88, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨88, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 88 0 = h 1 0 + ((1488089715142606 : ℝ) / 5084219205547142) * (h 3 0 - h 1 0)
    convert homothetic_352 h H using 1 <;> norm_num
  · change h 88 1 = h 1 1 + ((2200075481498470 : ℝ) / 5084219205547142) * (h 3 0 - h 1 0)
    convert homothetic_353 h H using 1 <;> norm_num
  · change h 88 2 = h 1 2 + ((3643447258418433 : ℝ) / 5084219205547142) * (h 3 0 - h 1 0)
    convert homothetic_354 h H using 1 <;> norm_num
  · change h 88 3 = h 1 3 + (((-1209581546289054 : ℤ) : ℝ) / 5084219205547142) * (h 3 0 - h 1 0)
    convert homothetic_355 h H using 1 <;> norm_num

private theorem homothetic_vertex089 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨89, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨89, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨89, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 89 0 = h 1 0 + ((121457521946 : ℝ) / 717098038468) * (h 3 0 - h 1 0)
    convert homothetic_356 h H using 1 <;> norm_num
  · change h 89 1 = h 1 1 + ((240003270590 : ℝ) / 717098038468) * (h 3 0 - h 1 0)
    convert homothetic_357 h H using 1 <;> norm_num
  · change h 89 2 = h 1 2 + ((588086130579 : ℝ) / 717098038468) * (h 3 0 - h 1 0)
    convert homothetic_358 h H using 1 <;> norm_num
  · change h 89 3 = h 1 3 + (((-118545748644 : ℤ) : ℝ) / 717098038468) * (h 3 0 - h 1 0)
    convert homothetic_359 h H using 1 <;> norm_num

private theorem homothetic_vertex090 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨90, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨90, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨90, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 90 0 = h 1 0 + ((11252536543291334 : ℝ) / 39290953518325328) * (h 3 0 - h 1 0)
    convert homothetic_360 h H using 1 <;> norm_num
  · change h 90 1 = h 1 1 + ((19293474916189080 : ℝ) / 39290953518325328) * (h 3 0 - h 1 0)
    convert homothetic_361 h H using 1 <;> norm_num
  · change h 90 2 = h 1 2 + ((28364274250472077 : ℝ) / 39290953518325328) * (h 3 0 - h 1 0)
    convert homothetic_362 h H using 1 <;> norm_num
  · change h 90 3 = h 1 3 + (((-9201995192741856 : ℤ) : ℝ) / 39290953518325328) * (h 3 0 - h 1 0)
    convert homothetic_363 h H using 1 <;> norm_num

private theorem homothetic_vertex091 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨91, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨91, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨91, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 91 0 = h 1 0 + ((850202653622 : ℝ) / 5019686269276) * (h 3 0 - h 1 0)
    convert homothetic_364 h H using 1 <;> norm_num
  · change h 91 1 = h 1 1 + ((3122329502632 : ℝ) / 5019686269276) * (h 3 0 - h 1 0)
    convert homothetic_365 h H using 1 <;> norm_num
  · change h 91 2 = h 1 2 + ((4116602914053 : ℝ) / 5019686269276) * (h 3 0 - h 1 0)
    convert homothetic_366 h H using 1 <;> norm_num
  · change h 91 3 = h 1 3 + (((-829820240508 : ℤ) : ℝ) / 5019686269276) * (h 3 0 - h 1 0)
    convert homothetic_367 h H using 1 <;> norm_num

private theorem homothetic_vertex092 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨92, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨92, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨92, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 92 0 = h 1 0 + ((1976061186791234 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0)
    convert homothetic_368 h H using 1 <;> norm_num
  · change h 92 1 = h 1 1 + ((1100037740749235 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0)
    convert homothetic_369 h H using 1 <;> norm_num
  · change h 92 2 = h 1 2 + ((744044857571303 : ℝ) / 2542109602773571) * (h 3 0 - h 1 0)
    convert homothetic_370 h H using 1 <;> norm_num
  · change h 92 3 = h 1 3 + (((-604790773144527 : ℤ) : ℝ) / 2542109602773571) * (h 3 0 - h 1 0)
    convert homothetic_371 h H using 1 <;> norm_num

private theorem homothetic_vertex093 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨93, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨93, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨93, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 93 0 = h 1 0 + ((327456695422 : ℝ) / 358549019234) * (h 3 0 - h 1 0)
    convert homothetic_372 h H using 1 <;> norm_num
  · change h 93 1 = h 1 1 + ((120001635295 : ℝ) / 358549019234) * (h 3 0 - h 1 0)
    convert homothetic_373 h H using 1 <;> norm_num
  · change h 93 2 = h 1 2 + ((60728760973 : ℝ) / 358549019234) * (h 3 0 - h 1 0)
    convert homothetic_374 h H using 1 <;> norm_num
  · change h 93 3 = h 1 3 + (((-59272874322 : ℤ) : ℝ) / 358549019234) * (h 3 0 - h 1 0)
    convert homothetic_375 h H using 1 <;> norm_num

private theorem homothetic_vertex094 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨94, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨94, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨94, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 94 0 = h 1 0 + ((15407448355824946 : ℝ) / 19645476759162664) * (h 3 0 - h 1 0)
    convert homothetic_376 h H using 1 <;> norm_num
  · change h 94 1 = h 1 1 + ((9646737458094540 : ℝ) / 19645476759162664) * (h 3 0 - h 1 0)
    convert homothetic_377 h H using 1 <;> norm_num
  · change h 94 2 = h 1 2 + ((5626268271645667 : ℝ) / 19645476759162664) * (h 3 0 - h 1 0)
    convert homothetic_378 h H using 1 <;> norm_num
  · change h 94 3 = h 1 3 + (((-4600997596370928 : ℤ) : ℝ) / 19645476759162664) * (h 3 0 - h 1 0)
    convert homothetic_379 h H using 1 <;> norm_num

private theorem homothetic_vertex095 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨95, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨95, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨95, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 95 0 = h 1 0 + ((2292196867954 : ℝ) / 2509843134638) * (h 3 0 - h 1 0)
    convert homothetic_380 h H using 1 <;> norm_num
  · change h 95 1 = h 1 1 + ((1561164751316 : ℝ) / 2509843134638) * (h 3 0 - h 1 0)
    convert homothetic_381 h H using 1 <;> norm_num
  · change h 95 2 = h 1 2 + ((425101326811 : ℝ) / 2509843134638) * (h 3 0 - h 1 0)
    convert homothetic_382 h H using 1 <;> norm_num
  · change h 95 3 = h 1 3 + (((-414910120254 : ℤ) : ℝ) / 2509843134638) * (h 3 0 - h 1 0)
    convert homothetic_383 h H using 1 <;> norm_num

private theorem homothetic_vertex096 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨96, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨96, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨96, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 96 0 = h 1 0 + ((3952122373582468 : ℝ) / 5084219205547142) * (h 3 0 - h 1 0)
    convert homothetic_384 h H using 1 <;> norm_num
  · change h 96 1 = h 1 1 + ((2200075481498470 : ℝ) / 5084219205547142) * (h 3 0 - h 1 0)
    convert homothetic_385 h H using 1 <;> norm_num
  · change h 96 2 = h 1 2 + ((3643447258418433 : ℝ) / 5084219205547142) * (h 3 0 - h 1 0)
    convert homothetic_386 h H using 1 <;> norm_num
  · change h 96 3 = h 1 3 + (((-1209581546289054 : ℤ) : ℝ) / 5084219205547142) * (h 3 0 - h 1 0)
    convert homothetic_387 h H using 1 <;> norm_num

private theorem homothetic_vertex097 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨97, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨97, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨97, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 97 0 = h 1 0 + ((654913390844 : ℝ) / 717098038468) * (h 3 0 - h 1 0)
    convert homothetic_388 h H using 1 <;> norm_num
  · change h 97 1 = h 1 1 + ((240003270590 : ℝ) / 717098038468) * (h 3 0 - h 1 0)
    convert homothetic_389 h H using 1 <;> norm_num
  · change h 97 2 = h 1 2 + ((588086130579 : ℝ) / 717098038468) * (h 3 0 - h 1 0)
    convert homothetic_390 h H using 1 <;> norm_num
  · change h 97 3 = h 1 3 + (((-118545748644 : ℤ) : ℝ) / 717098038468) * (h 3 0 - h 1 0)
    convert homothetic_391 h H using 1 <;> norm_num

private theorem homothetic_vertex098 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨98, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨98, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨98, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 98 0 = h 1 0 + ((30814896711649892 : ℝ) / 39290953518325328) * (h 3 0 - h 1 0)
    convert homothetic_392 h H using 1 <;> norm_num
  · change h 98 1 = h 1 1 + ((19293474916189080 : ℝ) / 39290953518325328) * (h 3 0 - h 1 0)
    convert homothetic_393 h H using 1 <;> norm_num
  · change h 98 2 = h 1 2 + ((28364274250472077 : ℝ) / 39290953518325328) * (h 3 0 - h 1 0)
    convert homothetic_394 h H using 1 <;> norm_num
  · change h 98 3 = h 1 3 + (((-9201995192741856 : ℤ) : ℝ) / 39290953518325328) * (h 3 0 - h 1 0)
    convert homothetic_395 h H using 1 <;> norm_num

private theorem homothetic_vertex099 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨99, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨99, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨99, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 99 0 = h 1 0 + ((4584393735908 : ℝ) / 5019686269276) * (h 3 0 - h 1 0)
    convert homothetic_396 h H using 1 <;> norm_num
  · change h 99 1 = h 1 1 + ((3122329502632 : ℝ) / 5019686269276) * (h 3 0 - h 1 0)
    convert homothetic_397 h H using 1 <;> norm_num
  · change h 99 2 = h 1 2 + ((4116602914053 : ℝ) / 5019686269276) * (h 3 0 - h 1 0)
    convert homothetic_398 h H using 1 <;> norm_num
  · change h 99 3 = h 1 3 + (((-829820240508 : ℤ) : ℝ) / 5019686269276) * (h 3 0 - h 1 0)
    convert homothetic_399 h H using 1 <;> norm_num

private theorem homothetic_vertex100 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨100, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨100, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨100, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 100 0 = h 1 0 + ((34277022476771290488192312 : ℝ) / 43593967997045105315402336) * (h 3 0 - h 1 0)
    convert homothetic_400 h H using 1 <;> norm_num
  · change h 100 1 = h 1 1 + ((20631022303002567255165056 : ℝ) / 43593967997045105315402336) * (h 3 0 - h 1 0)
    convert homothetic_401 h H using 1 <;> norm_num
  · change h 100 2 = h 1 2 + ((22977346258318728988718983 : ℝ) / 43593967997045105315402336) * (h 3 0 - h 1 0)
    convert homothetic_402 h H using 1 <;> norm_num
  · change h 100 3 = h 1 3 + (((-10342179174716050358974176 : ℤ) : ℝ) / 43593967997045105315402336) * (h 3 0 - h 1 0)
    convert homothetic_403 h H using 1 <;> norm_num

private theorem homothetic_vertex101 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨101, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨101, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨101, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 101 0 = h 1 0 + ((54173244258288834119698744 : ℝ) / 69650407353842049756369072) * (h 3 0 - h 1 0)
    convert homothetic_404 h H using 1 <;> norm_num
  · change h 101 1 = h 1 1 + ((32752045938949025092020272 : ℝ) / 69650407353842049756369072) * (h 3 0 - h 1 0)
    convert homothetic_405 h H using 1 <;> norm_num
  · change h 101 2 = h 1 2 + ((36728407848088434627054561 : ℝ) / 69650407353842049756369072) * (h 3 0 - h 1 0)
    convert homothetic_406 h H using 1 <;> norm_num
  · change h 101 3 = h 1 3 + (((-16556086252303255881035952 : ℤ) : ℝ) / 69650407353842049756369072) * (h 3 0 - h 1 0)
    convert homothetic_407 h H using 1 <;> norm_num

private theorem homothetic_vertex102 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨102, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨102, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨102, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 102 0 = h 1 0 + ((118892073488280052516017694 : ℝ) / 151157195873225645395870332) * (h 3 0 - h 1 0)
    convert homothetic_408 h H using 1 <;> norm_num
  · change h 102 1 = h 1 1 + ((71998965174915341055154712 : ℝ) / 151157195873225645395870332) * (h 3 0 - h 1 0)
    convert homothetic_409 h H using 1 <;> norm_num
  · change h 102 2 = h 1 2 + ((79648627327030898094758421 : ℝ) / 151157195873225645395870332) * (h 3 0 - h 1 0)
    convert homothetic_410 h H using 1 <;> norm_num
  · change h 102 3 = h 1 3 + (((-35832025220364569554866492 : ℤ) : ℝ) / 151157195873225645395870332) * (h 3 0 - h 1 0)
    convert homothetic_411 h H using 1 <;> norm_num

private theorem homothetic_vertex103 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨103, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨103, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨103, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 103 0 = h 1 0 + ((17997003212972647231928744 : ℝ) / 23059496543247088807794352) * (h 3 0 - h 1 0)
    convert homothetic_412 h H using 1 <;> norm_num
  · change h 103 1 = h 1 1 + ((11012452477181888872350512 : ℝ) / 23059496543247088807794352) * (h 3 0 - h 1 0)
    convert homothetic_413 h H using 1 <;> norm_num
  · change h 103 2 = h 1 2 + ((12156889629218154062180811 : ℝ) / 23059496543247088807794352) * (h 3 0 - h 1 0)
    convert homothetic_414 h H using 1 <;> norm_num
  · change h 103 3 = h 1 3 + (((-5469327194431635539235312 : ℤ) : ℝ) / 23059496543247088807794352) * (h 3 0 - h 1 0)
    convert homothetic_415 h H using 1 <;> norm_num

private theorem homothetic_vertex104 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨104, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨104, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨104, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 104 0 = h 1 0 + ((34277022476771290488192312 : ℝ) / 43593967997045105315402336) * (h 3 0 - h 1 0)
    convert homothetic_416 h H using 1 <;> norm_num
  · change h 104 1 = h 1 1 + ((20631022303002567255165056 : ℝ) / 43593967997045105315402336) * (h 3 0 - h 1 0)
    convert homothetic_417 h H using 1 <;> norm_num
  · change h 104 2 = h 1 2 + ((23261555189186827128125343 : ℝ) / 43593967997045105315402336) * (h 3 0 - h 1 0)
    convert homothetic_418 h H using 1 <;> norm_num
  · change h 104 3 = h 1 3 + (((-10342179174716050358974176 : ℤ) : ℝ) / 43593967997045105315402336) * (h 3 0 - h 1 0)
    convert homothetic_419 h H using 1 <;> norm_num

private theorem homothetic_vertex105 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨105, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨105, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨105, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 105 0 = h 1 0 + ((54173244258288834119698744 : ℝ) / 69650407353842049756369072) * (h 3 0 - h 1 0)
    convert homothetic_420 h H using 1 <;> norm_num
  · change h 105 1 = h 1 1 + ((32752045938949025092020272 : ℝ) / 69650407353842049756369072) * (h 3 0 - h 1 0)
    convert homothetic_421 h H using 1 <;> norm_num
  · change h 105 2 = h 1 2 + ((37207570012527211655475201 : ℝ) / 69650407353842049756369072) * (h 3 0 - h 1 0)
    convert homothetic_422 h H using 1 <;> norm_num
  · change h 105 3 = h 1 3 + (((-16556086252303255881035952 : ℤ) : ℝ) / 69650407353842049756369072) * (h 3 0 - h 1 0)
    convert homothetic_423 h H using 1 <;> norm_num

private theorem homothetic_vertex106 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨106, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨106, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨106, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 106 0 = h 1 0 + ((59446036744140026258008847 : ℝ) / 75578597936612822697935166) * (h 3 0 - h 1 0)
    convert homothetic_424 h H using 1 <;> norm_num
  · change h 106 1 = h 1 1 + ((35999482587457670527577356 : ℝ) / 75578597936612822697935166) * (h 3 0 - h 1 0)
    convert homothetic_425 h H using 1 <;> norm_num
  · change h 106 2 = h 1 2 + ((40332983056830511058248548 : ℝ) / 75578597936612822697935166) * (h 3 0 - h 1 0)
    convert homothetic_426 h H using 1 <;> norm_num
  · change h 106 3 = h 1 3 + (((-17916012610182284777433246 : ℤ) : ℝ) / 75578597936612822697935166) * (h 3 0 - h 1 0)
    convert homothetic_427 h H using 1 <;> norm_num

private theorem homothetic_vertex107 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨107, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨107, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨107, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 107 0 = h 1 0 + ((17997003212972647231928744 : ℝ) / 23059496543247088807794352) * (h 3 0 - h 1 0)
    convert homothetic_428 h H using 1 <;> norm_num
  · change h 107 1 = h 1 1 + ((11012452477181888872350512 : ℝ) / 23059496543247088807794352) * (h 3 0 - h 1 0)
    convert homothetic_429 h H using 1 <;> norm_num
  · change h 107 2 = h 1 2 + ((12316610350697746404987691 : ℝ) / 23059496543247088807794352) * (h 3 0 - h 1 0)
    convert homothetic_430 h H using 1 <;> norm_num
  · change h 107 3 = h 1 3 + (((-5469327194431635539235312 : ℤ) : ℝ) / 23059496543247088807794352) * (h 3 0 - h 1 0)
    convert homothetic_431 h H using 1 <;> norm_num

private theorem homothetic_vertex108 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨108, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨108, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨108, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 108 0 = h 1 0 + ((17730888915597721573096 : ℝ) / 22541406790489933660064) * (h 3 0 - h 1 0)
    convert homothetic_432 h H using 1 <;> norm_num
  · change h 108 1 = h 1 1 + ((10587999992185503947104 : ℝ) / 22541406790489933660064) * (h 3 0 - h 1 0)
    convert homothetic_433 h H using 1 <;> norm_num
  · change h 108 2 = h 1 2 + ((11748196884205232413579 : ℝ) / 22541406790489933660064) * (h 3 0 - h 1 0)
    convert homothetic_434 h H using 1 <;> norm_num
  · change h 108 3 = h 1 3 + (((-5350507353181007259936 : ℤ) : ℝ) / 22541406790489933660064) * (h 3 0 - h 1 0)
    convert homothetic_435 h H using 1 <;> norm_num

private theorem homothetic_vertex109 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨109, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨109, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨109, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 109 0 = h 1 0 + ((2293494347764053290040 : ℝ) / 3071407120199047912112) * (h 3 0 - h 1 0)
    convert homothetic_436 h H using 1 <;> norm_num
  · change h 109 1 = h 1 1 + ((1385755762125216557168 : ℝ) / 3071407120199047912112) * (h 3 0 - h 1 0)
    convert homothetic_437 h H using 1 <;> norm_num
  · change h 109 2 = h 1 2 + ((1582787225885989341909 : ℝ) / 3071407120199047912112) * (h 3 0 - h 1 0)
    convert homothetic_438 h H using 1 <;> norm_num
  · change h 109 3 = h 1 3 + (((-736249408133750375088 : ℤ) : ℝ) / 3071407120199047912112) * (h 3 0 - h 1 0)
    convert homothetic_439 h H using 1 <;> norm_num

private theorem homothetic_vertex110 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨110, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨110, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨110, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 110 0 = h 1 0 + ((21876771090952130043656 : ℝ) / 27775822889558374356240) * (h 3 0 - h 1 0)
    convert homothetic_440 h H using 1 <;> norm_num
  · change h 110 1 = h 1 1 + ((13295497267524074476976 : ℝ) / 27775822889558374356240) * (h 3 0 - h 1 0)
    convert homothetic_441 h H using 1 <;> norm_num
  · change h 110 2 = h 1 2 + ((14397052723137184347689 : ℝ) / 27775822889558374356240) * (h 3 0 - h 1 0)
    convert homothetic_442 h H using 1 <;> norm_num
  · change h 110 3 = h 1 3 + (((-6576739924629061478416 : ℤ) : ℝ) / 27775822889558374356240) * (h 3 0 - h 1 0)
    convert homothetic_443 h H using 1 <;> norm_num

private theorem homothetic_vertex111 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨111, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨111, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨111, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 111 0 = h 1 0 + ((10792135834680102568928888 : ℝ) / 14224765346051660926469904) * (h 3 0 - h 1 0)
    convert homothetic_444 h H using 1 <;> norm_num
  · change h 111 1 = h 1 1 + ((6916152814365802751080144 : ℝ) / 14224765346051660926469904) * (h 3 0 - h 1 0)
    convert homothetic_445 h H using 1 <;> norm_num
  · change h 111 2 = h 1 2 + ((7315897915430486560522437 : ℝ) / 14224765346051660926469904) * (h 3 0 - h 1 0)
    convert homothetic_446 h H using 1 <;> norm_num
  · change h 111 3 = h 1 3 + (((-3374848748911646281466064 : ℤ) : ℝ) / 14224765346051660926469904) * (h 3 0 - h 1 0)
    convert homothetic_447 h H using 1 <;> norm_num

private theorem homothetic_vertex112 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨112, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨112, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨112, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 112 0 = h 1 0 + ((17730888915597721573096 : ℝ) / 22541406790489933660064) * (h 3 0 - h 1 0)
    convert homothetic_448 h H using 1 <;> norm_num
  · change h 112 1 = h 1 1 + ((10587999992185503947104 : ℝ) / 22541406790489933660064) * (h 3 0 - h 1 0)
    convert homothetic_449 h H using 1 <;> norm_num
  · change h 112 2 = h 1 2 + ((12145691892412362678483 : ℝ) / 22541406790489933660064) * (h 3 0 - h 1 0)
    convert homothetic_450 h H using 1 <;> norm_num
  · change h 112 3 = h 1 3 + (((-5350507353181007259936 : ℤ) : ℝ) / 22541406790489933660064) * (h 3 0 - h 1 0)
    convert homothetic_451 h H using 1 <;> norm_num

private theorem homothetic_vertex113 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨113, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨113, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨113, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 113 0 = h 1 0 + ((2293494347764053290040 : ℝ) / 3071407120199047912112) * (h 3 0 - h 1 0)
    convert homothetic_452 h H using 1 <;> norm_num
  · change h 113 1 = h 1 1 + ((1385755762125216557168 : ℝ) / 3071407120199047912112) * (h 3 0 - h 1 0)
    convert homothetic_453 h H using 1 <;> norm_num
  · change h 113 2 = h 1 2 + ((1682925609258774509813 : ℝ) / 3071407120199047912112) * (h 3 0 - h 1 0)
    convert homothetic_454 h H using 1 <;> norm_num
  · change h 113 3 = h 1 3 + (((-736249408133750375088 : ℤ) : ℝ) / 3071407120199047912112) * (h 3 0 - h 1 0)
    convert homothetic_455 h H using 1 <;> norm_num

private theorem homothetic_vertex114 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨114, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨114, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨114, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 114 0 = h 1 0 + ((21876771090952130043656 : ℝ) / 27775822889558374356240) * (h 3 0 - h 1 0)
    convert homothetic_456 h H using 1 <;> norm_num
  · change h 114 1 = h 1 1 + ((13295497267524074476976 : ℝ) / 27775822889558374356240) * (h 3 0 - h 1 0)
    convert homothetic_457 h H using 1 <;> norm_num
  · change h 114 2 = h 1 2 + ((15029431145284891587309 : ℝ) / 27775822889558374356240) * (h 3 0 - h 1 0)
    convert homothetic_458 h H using 1 <;> norm_num
  · change h 114 3 = h 1 3 + (((-6576739924629061478416 : ℤ) : ℝ) / 27775822889558374356240) * (h 3 0 - h 1 0)
    convert homothetic_459 h H using 1 <;> norm_num

private theorem homothetic_vertex115 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨115, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨115, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨115, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 115 0 = h 1 0 + ((10792135834680102568928888 : ℝ) / 14224765346051660926469904) * (h 3 0 - h 1 0)
    convert homothetic_460 h H using 1 <;> norm_num
  · change h 115 1 = h 1 1 + ((6916152814365802751080144 : ℝ) / 14224765346051660926469904) * (h 3 0 - h 1 0)
    convert homothetic_461 h H using 1 <;> norm_num
  · change h 115 2 = h 1 2 + ((7795060079869263588943077 : ℝ) / 14224765346051660926469904) * (h 3 0 - h 1 0)
    convert homothetic_462 h H using 1 <;> norm_num
  · change h 115 3 = h 1 3 + (((-3374848748911646281466064 : ℤ) : ℝ) / 14224765346051660926469904) * (h 3 0 - h 1 0)
    convert homothetic_463 h H using 1 <;> norm_num

private theorem homothetic_vertex116 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨116, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨116, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨116, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 116 0 = h 1 0 + ((821682077579475289258482455176 : ℝ) / 1045616881782826808829398195552) * (h 3 0 - h 1 0)
    convert homothetic_464 h H using 1 <;> norm_num
  · change h 116 1 = h 1 1 + ((496659593780964693269920504000 : ℝ) / 1045616881782826808829398195552) * (h 3 0 - h 1 0)
    convert homothetic_465 h H using 1 <;> norm_num
  · change h 116 2 = h 1 2 + ((550094978867967299599421436073 : ℝ) / 1045616881782826808829398195552) * (h 3 0 - h 1 0)
    convert homothetic_466 h H using 1 <;> norm_num
  · change h 116 3 = h 1 3 + (((-247978462251592343276037429216 : ℤ) : ℝ) / 1045616881782826808829398195552) * (h 3 0 - h 1 0)
    convert homothetic_467 h H using 1 <;> norm_num

private theorem homothetic_vertex117 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨117, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨117, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨117, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 117 0 = h 1 0 + ((20475887603446782897110556008 : ℝ) / 26098535765767225002740465056) * (h 3 0 - h 1 0)
    convert homothetic_468 h H using 1 <;> norm_num
  · change h 117 1 = h 1 1 + ((12381876063138689842785565376 : ℝ) / 26098535765767225002740465056) * (h 3 0 - h 1 0)
    convert homothetic_469 h H using 1 <;> norm_num
  · change h 117 2 = h 1 2 + ((13732829524213089535259041889 : ℝ) / 26098535765767225002740465056) * (h 3 0 - h 1 0)
    convert homothetic_470 h H using 1 <;> norm_num
  · change h 117 3 = h 1 3 + (((-6191501658673746915968217600 : ℤ) : ℝ) / 26098535765767225002740465056) * (h 3 0 - h 1 0)
    convert homothetic_471 h H using 1 <;> norm_num

private theorem homothetic_vertex118 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨118, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨118, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨118, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 118 0 = h 1 0 + ((6522817477036909934543124518120 : ℝ) / 8300078906963278004742696816368) * (h 3 0 - h 1 0)
    convert homothetic_472 h H using 1 <;> norm_num
  · change h 118 1 = h 1 1 + ((3945181245705771740379891605520 : ℝ) / 8300078906963278004742696816368) * (h 3 0 - h 1 0)
    convert homothetic_473 h H using 1 <;> norm_num
  · change h 118 2 = h 1 2 + ((4366642872826104676091635747493 : ℝ) / 8300078906963278004742696816368) * (h 3 0 - h 1 0)
    convert homothetic_474 h H using 1 <;> norm_num
  · change h 118 3 = h 1 3 + (((-1968276488398966567191832757808 : ℤ) : ℝ) / 8300078906963278004742696816368) * (h 3 0 - h 1 0)
    convert homothetic_475 h H using 1 <;> norm_num

private theorem homothetic_vertex119 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨119, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨119, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨119, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 119 0 = h 1 0 + ((306981501161733090525881623544 : ℝ) / 391071951284919650983072509072) * (h 3 0 - h 1 0)
    convert homothetic_476 h H using 1 <;> norm_num
  · change h 119 1 = h 1 1 + ((185973651486459757674072883312 : ℝ) / 391071951284919650983072509072) * (h 3 0 - h 1 0)
    convert homothetic_477 h H using 1 <;> norm_num
  · change h 119 2 = h 1 2 + ((205770658487742909743824942191 : ℝ) / 391071951284919650983072509072) * (h 3 0 - h 1 0)
    convert homothetic_478 h H using 1 <;> norm_num
  · change h 119 3 = h 1 3 + (((-92745080812424519198427785232 : ℤ) : ℝ) / 391071951284919650983072509072) * (h 3 0 - h 1 0)
    convert homothetic_479 h H using 1 <;> norm_num

private theorem homothetic_vertex120 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨120, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨120, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨120, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 120 0 = h 1 0 + ((456942339186957751005884982896 : ℝ) / 581395530390869120698228605208) * (h 3 0 - h 1 0)
    convert homothetic_480 h H using 1 <;> norm_num
  · change h 120 1 = h 1 1 + ((275917504138499526067541080808 : ℝ) / 581395530390869120698228605208) * (h 3 0 - h 1 0)
    convert homothetic_481 h H using 1 <;> norm_num
  · change h 120 2 = h 1 2 + ((310361656748375544205985042169 : ℝ) / 581395530390869120698228605208) * (h 3 0 - h 1 0)
    convert homothetic_482 h H using 1 <;> norm_num
  · change h 120 3 = h 1 3 + (((-137894656836962159564201929848 : ℤ) : ℝ) / 581395530390869120698228605208) * (h 3 0 - h 1 0)
    convert homothetic_483 h H using 1 <;> norm_num

private theorem homothetic_vertex121 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨121, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨121, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨121, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 121 0 = h 1 0 + ((99204426531276861283627264 : ℝ) / 126864826990784360612753192) * (h 3 0 - h 1 0)
    convert homothetic_484 h H using 1 <;> norm_num
  · change h 121 1 = h 1 1 + ((59984697269395718694935992 : ℝ) / 126864826990784360612753192) * (h 3 0 - h 1 0)
    convert homothetic_485 h H using 1 <;> norm_num
  · change h 121 2 = h 1 2 + ((67753278475216386708530091 : ℝ) / 126864826990784360612753192) * (h 3 0 - h 1 0)
    convert homothetic_486 h H using 1 <;> norm_num
  · change h 121 3 = h 1 3 + (((-30119522468363034008237592 : ℤ) : ℝ) / 126864826990784360612753192) * (h 3 0 - h 1 0)
    convert homothetic_487 h H using 1 <;> norm_num

private theorem homothetic_vertex122 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨122, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨122, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨122, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 122 0 = h 1 0 + ((3626605216410689955161741578864 : ℝ) / 4613625110444969192467842115072) * (h 3 0 - h 1 0)
    convert homothetic_488 h H using 1 <;> norm_num
  · change h 122 1 = h 1 1 + ((2194246195683291550979927303472 : ℝ) / 4613625110444969192467842115072) * (h 3 0 - h 1 0)
    convert homothetic_489 h H using 1 <;> norm_num
  · change h 122 2 = h 1 2 + ((2462877092205180514685636204021 : ℝ) / 4613625110444969192467842115072) * (h 3 0 - h 1 0)
    convert homothetic_490 h H using 1 <;> norm_num
  · change h 122 3 = h 1 3 + (((-1093957773807952028555129658432 : ℤ) : ℝ) / 4613625110444969192467842115072) * (h 3 0 - h 1 0)
    convert homothetic_491 h H using 1 <;> norm_num

private theorem homothetic_vertex123 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨123, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨123, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨123, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 123 0 = h 1 0 + ((415993435070659060043953840 : ℝ) / 531109773668326455408164448) * (h 3 0 - h 1 0)
    convert homothetic_492 h H using 1 <;> norm_num
  · change h 123 1 = h 1 1 + ((252977115479439760085095280 : ℝ) / 531109773668326455408164448) * (h 3 0 - h 1 0)
    convert homothetic_493 h H using 1 <;> norm_num
  · change h 123 2 = h 1 2 + ((283623022390324824767957115 : ℝ) / 531109773668326455408164448) * (h 3 0 - h 1 0)
    convert homothetic_494 h H using 1 <;> norm_num
  · change h 123 3 = h 1 3 + (((-125961412325244268023443328 : ℤ) : ℝ) / 531109773668326455408164448) * (h 3 0 - h 1 0)
    convert homothetic_495 h H using 1 <;> norm_num

private theorem homothetic_vertex124 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨124, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨124, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨124, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 124 0 = h 1 0 + ((1605442100547335975360432 : ℝ) / 1923008533711279939163200) * (h 3 0 - h 1 0)
    convert homothetic_496 h H using 1 <;> norm_num
  · change h 124 1 = h 1 1 + ((910353884670623831407352 : ℝ) / 1923008533711279939163200) * (h 3 0 - h 1 0)
    convert homothetic_497 h H using 1 <;> norm_num
  · change h 124 2 = h 1 2 + ((934816436068939411244123 : ℝ) / 1923008533711279939163200) * (h 3 0 - h 1 0)
    convert homothetic_498 h H using 1 <;> norm_num
  · change h 124 3 = h 1 3 + (((-408312046720902374603232 : ℤ) : ℝ) / 1923008533711279939163200) * (h 3 0 - h 1 0)
    convert homothetic_499 h H using 1 <;> norm_num

private theorem homothetic_vertex125 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨125, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨125, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨125, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 125 0 = h 1 0 + ((303562265326368605834072 : ℝ) / 383558463993790758399480) * (h 3 0 - h 1 0)
    convert homothetic_500 h H using 1 <;> norm_num
  · change h 125 1 = h 1 1 + ((181149315699781646744672 : ℝ) / 383558463993790758399480) * (h 3 0 - h 1 0)
    convert homothetic_501 h H using 1 <;> norm_num
  · change h 125 2 = h 1 2 + ((201995350963450366325643 : ℝ) / 383558463993790758399480) * (h 3 0 - h 1 0)
    convert homothetic_502 h H using 1 <;> norm_num
  · change h 125 3 = h 1 3 + (((-90146211177649430529112 : ℤ) : ℝ) / 383558463993790758399480) * (h 3 0 - h 1 0)
    convert homothetic_503 h H using 1 <;> norm_num

private theorem homothetic_vertex126 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨126, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨126, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨126, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 126 0 = h 1 0 + ((16432430943662093694607184 : ℝ) / 19699030405131969967718240) * (h 3 0 - h 1 0)
    convert homothetic_504 h H using 1 <;> norm_num
  · change h 126 1 = h 1 1 + ((9948357375023189514504304 : ℝ) / 19699030405131969967718240) * (h 3 0 - h 1 0)
    convert homothetic_505 h H using 1 <;> norm_num
  · change h 126 2 = h 1 2 + ((9630627783411212560211751 : ℝ) / 19699030405131969967718240) * (h 3 0 - h 1 0)
    convert homothetic_506 h H using 1 <;> norm_num
  · change h 126 3 = h 1 3 + (((-4190781066628757864646784 : ℤ) : ℝ) / 19699030405131969967718240) * (h 3 0 - h 1 0)
    convert homothetic_507 h H using 1 <;> norm_num

private theorem homothetic_vertex127 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨127, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨127, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨127, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 127 0 = h 1 0 + ((874063471235004430739378 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0)
    convert homothetic_508 h H using 1 <;> norm_num
  · change h 127 1 = h 1 1 + ((529787797170143595009788 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0)
    convert homothetic_509 h H using 1 <;> norm_num
  · change h 127 2 = h 1 2 + ((578749084305489324838032 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0)
    convert homothetic_510 h H using 1 <;> norm_num
  · change h 127 3 = h 1 3 + (((-257588362112298345612543 : ℤ) : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0)
    convert homothetic_511 h H using 1 <;> norm_num

private theorem homothetic_vertex128 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨128, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨128, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨128, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 128 0 = h 1 0 + ((1605442100547335975360432 : ℝ) / 1923008533711279939163200) * (h 3 0 - h 1 0)
    convert homothetic_512 h H using 1 <;> norm_num
  · change h 128 1 = h 1 1 + ((910353884670623831407352 : ℝ) / 1923008533711279939163200) * (h 3 0 - h 1 0)
    convert homothetic_513 h H using 1 <;> norm_num
  · change h 128 2 = h 1 2 + ((1076920901502988480947303 : ℝ) / 1923008533711279939163200) * (h 3 0 - h 1 0)
    convert homothetic_514 h H using 1 <;> norm_num
  · change h 128 3 = h 1 3 + (((-408312046720902374603232 : ℤ) : ℝ) / 1923008533711279939163200) * (h 3 0 - h 1 0)
    convert homothetic_515 h H using 1 <;> norm_num

private theorem homothetic_vertex129 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨129, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨129, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨129, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 129 0 = h 1 0 + ((303562265326368605834072 : ℝ) / 383558463993790758399480) * (h 3 0 - h 1 0)
    convert homothetic_516 h H using 1 <;> norm_num
  · change h 129 1 = h 1 1 + ((181149315699781646744672 : ℝ) / 383558463993790758399480) * (h 3 0 - h 1 0)
    convert homothetic_517 h H using 1 <;> norm_num
  · change h 129 2 = h 1 2 + ((204749156506201958443003 : ℝ) / 383558463993790758399480) * (h 3 0 - h 1 0)
    convert homothetic_518 h H using 1 <;> norm_num
  · change h 129 3 = h 1 3 + (((-90146211177649430529112 : ℤ) : ℝ) / 383558463993790758399480) * (h 3 0 - h 1 0)
    convert homothetic_519 h H using 1 <;> norm_num

private theorem homothetic_vertex130 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨130, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨130, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨130, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 130 0 = h 1 0 + ((16432430943662093694607184 : ℝ) / 19699030405131969967718240) * (h 3 0 - h 1 0)
    convert homothetic_520 h H using 1 <;> norm_num
  · change h 130 1 = h 1 1 + ((9948357375023189514504304 : ℝ) / 19699030405131969967718240) * (h 3 0 - h 1 0)
    convert homothetic_521 h H using 1 <;> norm_num
  · change h 130 2 = h 1 2 + ((10987079498918044589196651 : ℝ) / 19699030405131969967718240) * (h 3 0 - h 1 0)
    convert homothetic_522 h H using 1 <;> norm_num
  · change h 130 3 = h 1 3 + (((-4190781066628757864646784 : ℤ) : ℝ) / 19699030405131969967718240) * (h 3 0 - h 1 0)
    convert homothetic_523 h H using 1 <;> norm_num

private theorem homothetic_vertex131 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨131, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨131, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨131, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 131 0 = h 1 0 + ((874063471235004430739378 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0)
    convert homothetic_524 h H using 1 <;> norm_num
  · change h 131 1 = h 1 1 + ((529787797170143595009788 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0)
    convert homothetic_525 h H using 1 <;> norm_num
  · change h 131 2 = h 1 2 + ((588731629397963846263462 : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0)
    convert homothetic_526 h H using 1 <;> norm_num
  · change h 131 3 = h 1 3 + (((-257588362112298345612543 : ℤ) : ℝ) / 1101342589070088405517555) * (h 3 0 - h 1 0)
    convert homothetic_527 h H using 1 <;> norm_num

private theorem homothetic_vertex132 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨132, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨132, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨132, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 132 0 = h 1 0 + ((23480517613140806239176 : ℝ) / 29811274973339113635784) * (h 3 0 - h 1 0)
    convert homothetic_528 h H using 1 <;> norm_num
  · change h 132 1 = h 1 1 + ((14015384281288469024512 : ℝ) / 29811274973339113635784) * (h 3 0 - h 1 0)
    convert homothetic_529 h H using 1 <;> norm_num
  · change h 132 2 = h 1 2 + ((15699441442694853759603 : ℝ) / 29811274973339113635784) * (h 3 0 - h 1 0)
    convert homothetic_530 h H using 1 <;> norm_num
  · change h 132 3 = h 1 3 + (((-7062983877555051235752 : ℤ) : ℝ) / 29811274973339113635784) * (h 3 0 - h 1 0)
    convert homothetic_531 h H using 1 <;> norm_num

private theorem homothetic_vertex133 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨133, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨133, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨133, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 133 0 = h 1 0 + ((3027587737908757983425448 : ℝ) / 3837161186404689159271580) * (h 3 0 - h 1 0)
    convert homothetic_532 h H using 1 <;> norm_num
  · change h 133 1 = h 1 1 + ((1840062978149559063847168 : ℝ) / 3837161186404689159271580) * (h 3 0 - h 1 0)
    convert homothetic_533 h H using 1 <;> norm_num
  · change h 133 2 = h 1 2 + ((2015720189903314992363807 : ℝ) / 3837161186404689159271580) * (h 3 0 - h 1 0)
    convert homothetic_534 h H using 1 <;> norm_num
  · change h 133 3 = h 1 3 + (((-906283185863747721766508 : ℤ) : ℝ) / 3837161186404689159271580) * (h 3 0 - h 1 0)
    convert homothetic_535 h H using 1 <;> norm_num

private theorem homothetic_vertex134 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨134, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨134, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨134, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 134 0 = h 1 0 + ((23480517613140806239176 : ℝ) / 29811274973339113635784) * (h 3 0 - h 1 0)
    convert homothetic_536 h H using 1 <;> norm_num
  · change h 134 1 = h 1 1 + ((14015384281288469024512 : ℝ) / 29811274973339113635784) * (h 3 0 - h 1 0)
    convert homothetic_537 h H using 1 <;> norm_num
  · change h 134 2 = h 1 2 + ((15937830579231558748867 : ℝ) / 29811274973339113635784) * (h 3 0 - h 1 0)
    convert homothetic_538 h H using 1 <;> norm_num
  · change h 134 3 = h 1 3 + (((-7062983877555051235752 : ℤ) : ℝ) / 29811274973339113635784) * (h 3 0 - h 1 0)
    convert homothetic_539 h H using 1 <;> norm_num

private theorem homothetic_vertex135 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨135, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨135, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨135, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 135 0 = h 1 0 + ((3027587737908757983425448 : ℝ) / 3837161186404689159271580) * (h 3 0 - h 1 0)
    convert homothetic_540 h H using 1 <;> norm_num
  · change h 135 1 = h 1 1 + ((1840062978149559063847168 : ℝ) / 3837161186404689159271580) * (h 3 0 - h 1 0)
    convert homothetic_541 h H using 1 <;> norm_num
  · change h 135 2 = h 1 2 + ((2055650370273213078065527 : ℝ) / 3837161186404689159271580) * (h 3 0 - h 1 0)
    convert homothetic_542 h H using 1 <;> norm_num
  · change h 135 3 = h 1 3 + (((-906283185863747721766508 : ℤ) : ℝ) / 3837161186404689159271580) * (h 3 0 - h 1 0)
    convert homothetic_543 h H using 1 <;> norm_num

private theorem homothetic_vertex136 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨136, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨136, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨136, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 136 0 = h 1 0 + ((66381187968361055676693878672 : ℝ) / 81354225799957920226747434208) * (h 3 0 - h 1 0)
    convert homothetic_544 h H using 1 <;> norm_num
  · change h 136 1 = h 1 1 + ((39506306678791435906549233512 : ℝ) / 81354225799957920226747434208) * (h 3 0 - h 1 0)
    convert homothetic_545 h H using 1 <;> norm_num
  · change h 136 2 = h 1 2 + ((40596238269230557822406629745 : ℝ) / 81354225799957920226747434208) * (h 3 0 - h 1 0)
    convert homothetic_546 h H using 1 <;> norm_num
  · change h 136 3 = h 1 3 + (((-18088020254783007242164833600 : ℤ) : ℝ) / 81354225799957920226747434208) * (h 3 0 - h 1 0)
    convert homothetic_547 h H using 1 <;> norm_num

private theorem homothetic_vertex137 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨137, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨137, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨137, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 137 0 = h 1 0 + ((5968111744515383677732547000 : ℝ) / 7434366338618829406811987440) * (h 3 0 - h 1 0)
    convert homothetic_548 h H using 1 <;> norm_num
  · change h 137 1 = h 1 1 + ((3561843594688596297246743744 : ℝ) / 7434366338618829406811987440) * (h 3 0 - h 1 0)
    convert homothetic_549 h H using 1 <;> norm_num
  · change h 137 2 = h 1 2 + ((3818379522142608901893272387 : ℝ) / 7434366338618829406811987440) * (h 3 0 - h 1 0)
    convert homothetic_550 h H using 1 <;> norm_num
  · change h 137 3 = h 1 3 + (((-1703693390669959246095735408 : ℤ) : ℝ) / 7434366338618829406811987440) * (h 3 0 - h 1 0)
    convert homothetic_551 h H using 1 <;> norm_num

private theorem homothetic_vertex138 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨138, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨138, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨138, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 138 0 = h 1 0 + ((526685380763377917373561862416 : ℝ) / 645261899548154685277523888872) * (h 3 0 - h 1 0)
    convert homothetic_552 h H using 1 <;> norm_num
  · change h 138 1 = h 1 1 + ((314706619918718867089369821168 : ℝ) / 645261899548154685277523888872) * (h 3 0 - h 1 0)
    convert homothetic_553 h H using 1 <;> norm_num
  · change h 138 2 = h 1 2 + ((321974428085998725597296933773 : ℝ) / 645261899548154685277523888872) * (h 3 0 - h 1 0)
    convert homothetic_554 h H using 1 <;> norm_num
  · change h 138 3 = h 1 3 + (((-143371129271809814974925326632 : ℤ) : ℝ) / 645261899548154685277523888872) * (h 3 0 - h 1 0)
    convert homothetic_555 h H using 1 <;> norm_num

private theorem homothetic_vertex139 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨139, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨139, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨139, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 139 0 = h 1 0 + ((3340521936795841080313723982 : ℝ) / 4149012134993127655033248390) * (h 3 0 - h 1 0)
    convert homothetic_556 h H using 1 <;> norm_num
  · change h 139 1 = h 1 1 + ((2007794395952639536868580632 : ℝ) / 4149012134993127655033248390) * (h 3 0 - h 1 0)
    convert homothetic_557 h H using 1 <;> norm_num
  · change h 139 2 = h 1 2 + ((2122341129024522150111233753 : ℝ) / 4149012134993127655033248390) * (h 3 0 - h 1 0)
    convert homothetic_558 h H using 1 <;> norm_num
  · change h 139 3 = h 1 3 + (((-945729533655826803074339782 : ℤ) : ℝ) / 4149012134993127655033248390) * (h 3 0 - h 1 0)
    convert homothetic_559 h H using 1 <;> norm_num

private theorem homothetic_vertex140 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨140, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨140, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨140, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 140 0 = h 1 0 + ((66436004652674444316500618672 : ℝ) / 81138282544257715319191235080) * (h 3 0 - h 1 0)
    convert homothetic_560 h H using 1 <;> norm_num
  · change h 140 1 = h 1 1 + ((39252282853258009002717797192 : ℝ) / 81138282544257715319191235080) * (h 3 0 - h 1 0)
    convert homothetic_561 h H using 1 <;> norm_num
  · change h 140 2 = h 1 2 + ((44687036887344659550100205613 : ℝ) / 81138282544257715319191235080) * (h 3 0 - h 1 0)
    convert homothetic_562 h H using 1 <;> norm_num
  · change h 140 3 = h 1 3 + (((-17917740230244215385586788552 : ℤ) : ℝ) / 81138282544257715319191235080) * (h 3 0 - h 1 0)
    convert homothetic_563 h H using 1 <;> norm_num

private theorem homothetic_vertex141 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨141, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨141, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨141, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 141 0 = h 1 0 + ((109441039844199214799071976 : ℝ) / 137642270394160616208130240) * (h 3 0 - h 1 0)
    convert homothetic_564 h H using 1 <;> norm_num
  · change h 141 1 = h 1 1 + ((65310823331595043303375616 : ℝ) / 137642270394160616208130240) * (h 3 0 - h 1 0)
    convert homothetic_565 h H using 1 <;> norm_num
  · change h 141 2 = h 1 2 + ((73792219984703345486771169 : ℝ) / 137642270394160616208130240) * (h 3 0 - h 1 0)
    convert homothetic_566 h H using 1 <;> norm_num
  · change h 141 3 = h 1 3 + (((-32087951570457945125314176 : ℤ) : ℝ) / 137642270394160616208130240) * (h 3 0 - h 1 0)
    convert homothetic_567 h H using 1 <;> norm_num

private theorem homothetic_vertex142 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨142, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨142, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨142, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 142 0 = h 1 0 + ((526311258041626707790792451248 : ℝ) / 642000616878594036231713212720) * (h 3 0 - h 1 0)
    convert homothetic_568 h H using 1 <;> norm_num
  · change h 142 1 = h 1 1 + ((315322114767272570186652864528 : ℝ) / 642000616878594036231713212720) * (h 3 0 - h 1 0)
    convert homothetic_569 h H using 1 <;> norm_num
  · change h 142 2 = h 1 2 + ((353642629134415506844988262617 : ℝ) / 642000616878594036231713212720) * (h 3 0 - h 1 0)
    convert homothetic_570 h H using 1 <;> norm_num
  · change h 142 3 = h 1 3 + (((-141441318106511515246189228368 : ℤ) : ℝ) / 642000616878594036231713212720) * (h 3 0 - h 1 0)
    convert homothetic_571 h H using 1 <;> norm_num

private theorem homothetic_vertex143 (h : Assignment) (H : Constraints h) (i : Fin 4) :
    h (⟨143, by decide⟩ : Fin 144) i = h 1 i + ((q (⟨143, by decide⟩ : Fin 144) i.castSucc : ℝ) / (q (⟨143, by decide⟩ : Fin 144) 4 : ℝ)) * (h 3 0 - h 1 0) := by
  fin_cases i
  · change h 143 0 = h 1 0 + ((12023881457031766930853 : ℝ) / 15073723378247361660612) * (h 3 0 - h 1 0)
    convert homothetic_572 h H using 1 <;> norm_num
  · change h 143 1 = h 1 1 + ((7266288610244526108704 : ℝ) / 15073723378247361660612) * (h 3 0 - h 1 0)
    convert homothetic_573 h H using 1 <;> norm_num
  · change h 143 2 = h 1 2 + ((8097701956329756422637 : ℝ) / 15073723378247361660612) * (h 3 0 - h 1 0)
    convert homothetic_574 h H using 1 <;> norm_num
  · change h 143 3 = h 1 3 + (((-3494076923438998582792 : ℤ) : ℝ) / 15073723378247361660612) * (h 3 0 - h 1 0)
    convert homothetic_575 h H using 1 <;> norm_num

private theorem homothetic_group00 (h : Assignment) (H : Constraints h)
    (v : Fin 144) (i : Fin 4) (hlo : 0 ≤ v.val) (hhi : v.val < 32) :
    h v i = h 1 i + ((q v i.castSucc : ℝ) / (q v 4 : ℝ)) * (h 3 0 - h 1 0) := by
  have hv_bound := v.isLt
  by_cases h16 : v.val < 16
  ·
    by_cases h8 : v.val < 8
    ·
      by_cases h4 : v.val < 4
      ·
        by_cases h2 : v.val < 2
        ·
          by_cases h1 : v.val < 1
          ·
            have he : (⟨0, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 0 = v.val
              omega
            simpa only [he] using homothetic_vertex000 h H i
          ·
            have he : (⟨1, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 1 = v.val
              omega
            simpa only [he] using homothetic_vertex001 h H i
        ·
          by_cases h3 : v.val < 3
          ·
            have he : (⟨2, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 2 = v.val
              omega
            simpa only [he] using homothetic_vertex002 h H i
          ·
            have he : (⟨3, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 3 = v.val
              omega
            simpa only [he] using homothetic_vertex003 h H i
      ·
        by_cases h6 : v.val < 6
        ·
          by_cases h5 : v.val < 5
          ·
            have he : (⟨4, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 4 = v.val
              omega
            simpa only [he] using homothetic_vertex004 h H i
          ·
            have he : (⟨5, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 5 = v.val
              omega
            simpa only [he] using homothetic_vertex005 h H i
        ·
          by_cases h7 : v.val < 7
          ·
            have he : (⟨6, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 6 = v.val
              omega
            simpa only [he] using homothetic_vertex006 h H i
          ·
            have he : (⟨7, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 7 = v.val
              omega
            simpa only [he] using homothetic_vertex007 h H i
    ·
      by_cases h12 : v.val < 12
      ·
        by_cases h10 : v.val < 10
        ·
          by_cases h9 : v.val < 9
          ·
            have he : (⟨8, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 8 = v.val
              omega
            simpa only [he] using homothetic_vertex008 h H i
          ·
            have he : (⟨9, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 9 = v.val
              omega
            simpa only [he] using homothetic_vertex009 h H i
        ·
          by_cases h11 : v.val < 11
          ·
            have he : (⟨10, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 10 = v.val
              omega
            simpa only [he] using homothetic_vertex010 h H i
          ·
            have he : (⟨11, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 11 = v.val
              omega
            simpa only [he] using homothetic_vertex011 h H i
      ·
        by_cases h14 : v.val < 14
        ·
          by_cases h13 : v.val < 13
          ·
            have he : (⟨12, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 12 = v.val
              omega
            simpa only [he] using homothetic_vertex012 h H i
          ·
            have he : (⟨13, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 13 = v.val
              omega
            simpa only [he] using homothetic_vertex013 h H i
        ·
          by_cases h15 : v.val < 15
          ·
            have he : (⟨14, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 14 = v.val
              omega
            simpa only [he] using homothetic_vertex014 h H i
          ·
            have he : (⟨15, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 15 = v.val
              omega
            simpa only [he] using homothetic_vertex015 h H i
  ·
    by_cases h24 : v.val < 24
    ·
      by_cases h20 : v.val < 20
      ·
        by_cases h18 : v.val < 18
        ·
          by_cases h17 : v.val < 17
          ·
            have he : (⟨16, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 16 = v.val
              omega
            simpa only [he] using homothetic_vertex016 h H i
          ·
            have he : (⟨17, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 17 = v.val
              omega
            simpa only [he] using homothetic_vertex017 h H i
        ·
          by_cases h19 : v.val < 19
          ·
            have he : (⟨18, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 18 = v.val
              omega
            simpa only [he] using homothetic_vertex018 h H i
          ·
            have he : (⟨19, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 19 = v.val
              omega
            simpa only [he] using homothetic_vertex019 h H i
      ·
        by_cases h22 : v.val < 22
        ·
          by_cases h21 : v.val < 21
          ·
            have he : (⟨20, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 20 = v.val
              omega
            simpa only [he] using homothetic_vertex020 h H i
          ·
            have he : (⟨21, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 21 = v.val
              omega
            simpa only [he] using homothetic_vertex021 h H i
        ·
          by_cases h23 : v.val < 23
          ·
            have he : (⟨22, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 22 = v.val
              omega
            simpa only [he] using homothetic_vertex022 h H i
          ·
            have he : (⟨23, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 23 = v.val
              omega
            simpa only [he] using homothetic_vertex023 h H i
    ·
      by_cases h28 : v.val < 28
      ·
        by_cases h26 : v.val < 26
        ·
          by_cases h25 : v.val < 25
          ·
            have he : (⟨24, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 24 = v.val
              omega
            simpa only [he] using homothetic_vertex024 h H i
          ·
            have he : (⟨25, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 25 = v.val
              omega
            simpa only [he] using homothetic_vertex025 h H i
        ·
          by_cases h27 : v.val < 27
          ·
            have he : (⟨26, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 26 = v.val
              omega
            simpa only [he] using homothetic_vertex026 h H i
          ·
            have he : (⟨27, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 27 = v.val
              omega
            simpa only [he] using homothetic_vertex027 h H i
      ·
        by_cases h30 : v.val < 30
        ·
          by_cases h29 : v.val < 29
          ·
            have he : (⟨28, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 28 = v.val
              omega
            simpa only [he] using homothetic_vertex028 h H i
          ·
            have he : (⟨29, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 29 = v.val
              omega
            simpa only [he] using homothetic_vertex029 h H i
        ·
          by_cases h31 : v.val < 31
          ·
            have he : (⟨30, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 30 = v.val
              omega
            simpa only [he] using homothetic_vertex030 h H i
          ·
            have he : (⟨31, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 31 = v.val
              omega
            simpa only [he] using homothetic_vertex031 h H i

private theorem homothetic_group01 (h : Assignment) (H : Constraints h)
    (v : Fin 144) (i : Fin 4) (hlo : 32 ≤ v.val) (hhi : v.val < 64) :
    h v i = h 1 i + ((q v i.castSucc : ℝ) / (q v 4 : ℝ)) * (h 3 0 - h 1 0) := by
  have hv_bound := v.isLt
  by_cases h48 : v.val < 48
  ·
    by_cases h40 : v.val < 40
    ·
      by_cases h36 : v.val < 36
      ·
        by_cases h34 : v.val < 34
        ·
          by_cases h33 : v.val < 33
          ·
            have he : (⟨32, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 32 = v.val
              omega
            simpa only [he] using homothetic_vertex032 h H i
          ·
            have he : (⟨33, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 33 = v.val
              omega
            simpa only [he] using homothetic_vertex033 h H i
        ·
          by_cases h35 : v.val < 35
          ·
            have he : (⟨34, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 34 = v.val
              omega
            simpa only [he] using homothetic_vertex034 h H i
          ·
            have he : (⟨35, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 35 = v.val
              omega
            simpa only [he] using homothetic_vertex035 h H i
      ·
        by_cases h38 : v.val < 38
        ·
          by_cases h37 : v.val < 37
          ·
            have he : (⟨36, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 36 = v.val
              omega
            simpa only [he] using homothetic_vertex036 h H i
          ·
            have he : (⟨37, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 37 = v.val
              omega
            simpa only [he] using homothetic_vertex037 h H i
        ·
          by_cases h39 : v.val < 39
          ·
            have he : (⟨38, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 38 = v.val
              omega
            simpa only [he] using homothetic_vertex038 h H i
          ·
            have he : (⟨39, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 39 = v.val
              omega
            simpa only [he] using homothetic_vertex039 h H i
    ·
      by_cases h44 : v.val < 44
      ·
        by_cases h42 : v.val < 42
        ·
          by_cases h41 : v.val < 41
          ·
            have he : (⟨40, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 40 = v.val
              omega
            simpa only [he] using homothetic_vertex040 h H i
          ·
            have he : (⟨41, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 41 = v.val
              omega
            simpa only [he] using homothetic_vertex041 h H i
        ·
          by_cases h43 : v.val < 43
          ·
            have he : (⟨42, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 42 = v.val
              omega
            simpa only [he] using homothetic_vertex042 h H i
          ·
            have he : (⟨43, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 43 = v.val
              omega
            simpa only [he] using homothetic_vertex043 h H i
      ·
        by_cases h46 : v.val < 46
        ·
          by_cases h45 : v.val < 45
          ·
            have he : (⟨44, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 44 = v.val
              omega
            simpa only [he] using homothetic_vertex044 h H i
          ·
            have he : (⟨45, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 45 = v.val
              omega
            simpa only [he] using homothetic_vertex045 h H i
        ·
          by_cases h47 : v.val < 47
          ·
            have he : (⟨46, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 46 = v.val
              omega
            simpa only [he] using homothetic_vertex046 h H i
          ·
            have he : (⟨47, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 47 = v.val
              omega
            simpa only [he] using homothetic_vertex047 h H i
  ·
    by_cases h56 : v.val < 56
    ·
      by_cases h52 : v.val < 52
      ·
        by_cases h50 : v.val < 50
        ·
          by_cases h49 : v.val < 49
          ·
            have he : (⟨48, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 48 = v.val
              omega
            simpa only [he] using homothetic_vertex048 h H i
          ·
            have he : (⟨49, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 49 = v.val
              omega
            simpa only [he] using homothetic_vertex049 h H i
        ·
          by_cases h51 : v.val < 51
          ·
            have he : (⟨50, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 50 = v.val
              omega
            simpa only [he] using homothetic_vertex050 h H i
          ·
            have he : (⟨51, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 51 = v.val
              omega
            simpa only [he] using homothetic_vertex051 h H i
      ·
        by_cases h54 : v.val < 54
        ·
          by_cases h53 : v.val < 53
          ·
            have he : (⟨52, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 52 = v.val
              omega
            simpa only [he] using homothetic_vertex052 h H i
          ·
            have he : (⟨53, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 53 = v.val
              omega
            simpa only [he] using homothetic_vertex053 h H i
        ·
          by_cases h55 : v.val < 55
          ·
            have he : (⟨54, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 54 = v.val
              omega
            simpa only [he] using homothetic_vertex054 h H i
          ·
            have he : (⟨55, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 55 = v.val
              omega
            simpa only [he] using homothetic_vertex055 h H i
    ·
      by_cases h60 : v.val < 60
      ·
        by_cases h58 : v.val < 58
        ·
          by_cases h57 : v.val < 57
          ·
            have he : (⟨56, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 56 = v.val
              omega
            simpa only [he] using homothetic_vertex056 h H i
          ·
            have he : (⟨57, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 57 = v.val
              omega
            simpa only [he] using homothetic_vertex057 h H i
        ·
          by_cases h59 : v.val < 59
          ·
            have he : (⟨58, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 58 = v.val
              omega
            simpa only [he] using homothetic_vertex058 h H i
          ·
            have he : (⟨59, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 59 = v.val
              omega
            simpa only [he] using homothetic_vertex059 h H i
      ·
        by_cases h62 : v.val < 62
        ·
          by_cases h61 : v.val < 61
          ·
            have he : (⟨60, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 60 = v.val
              omega
            simpa only [he] using homothetic_vertex060 h H i
          ·
            have he : (⟨61, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 61 = v.val
              omega
            simpa only [he] using homothetic_vertex061 h H i
        ·
          by_cases h63 : v.val < 63
          ·
            have he : (⟨62, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 62 = v.val
              omega
            simpa only [he] using homothetic_vertex062 h H i
          ·
            have he : (⟨63, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 63 = v.val
              omega
            simpa only [he] using homothetic_vertex063 h H i

private theorem homothetic_group02 (h : Assignment) (H : Constraints h)
    (v : Fin 144) (i : Fin 4) (hlo : 64 ≤ v.val) (hhi : v.val < 96) :
    h v i = h 1 i + ((q v i.castSucc : ℝ) / (q v 4 : ℝ)) * (h 3 0 - h 1 0) := by
  have hv_bound := v.isLt
  by_cases h80 : v.val < 80
  ·
    by_cases h72 : v.val < 72
    ·
      by_cases h68 : v.val < 68
      ·
        by_cases h66 : v.val < 66
        ·
          by_cases h65 : v.val < 65
          ·
            have he : (⟨64, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 64 = v.val
              omega
            simpa only [he] using homothetic_vertex064 h H i
          ·
            have he : (⟨65, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 65 = v.val
              omega
            simpa only [he] using homothetic_vertex065 h H i
        ·
          by_cases h67 : v.val < 67
          ·
            have he : (⟨66, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 66 = v.val
              omega
            simpa only [he] using homothetic_vertex066 h H i
          ·
            have he : (⟨67, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 67 = v.val
              omega
            simpa only [he] using homothetic_vertex067 h H i
      ·
        by_cases h70 : v.val < 70
        ·
          by_cases h69 : v.val < 69
          ·
            have he : (⟨68, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 68 = v.val
              omega
            simpa only [he] using homothetic_vertex068 h H i
          ·
            have he : (⟨69, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 69 = v.val
              omega
            simpa only [he] using homothetic_vertex069 h H i
        ·
          by_cases h71 : v.val < 71
          ·
            have he : (⟨70, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 70 = v.val
              omega
            simpa only [he] using homothetic_vertex070 h H i
          ·
            have he : (⟨71, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 71 = v.val
              omega
            simpa only [he] using homothetic_vertex071 h H i
    ·
      by_cases h76 : v.val < 76
      ·
        by_cases h74 : v.val < 74
        ·
          by_cases h73 : v.val < 73
          ·
            have he : (⟨72, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 72 = v.val
              omega
            simpa only [he] using homothetic_vertex072 h H i
          ·
            have he : (⟨73, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 73 = v.val
              omega
            simpa only [he] using homothetic_vertex073 h H i
        ·
          by_cases h75 : v.val < 75
          ·
            have he : (⟨74, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 74 = v.val
              omega
            simpa only [he] using homothetic_vertex074 h H i
          ·
            have he : (⟨75, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 75 = v.val
              omega
            simpa only [he] using homothetic_vertex075 h H i
      ·
        by_cases h78 : v.val < 78
        ·
          by_cases h77 : v.val < 77
          ·
            have he : (⟨76, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 76 = v.val
              omega
            simpa only [he] using homothetic_vertex076 h H i
          ·
            have he : (⟨77, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 77 = v.val
              omega
            simpa only [he] using homothetic_vertex077 h H i
        ·
          by_cases h79 : v.val < 79
          ·
            have he : (⟨78, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 78 = v.val
              omega
            simpa only [he] using homothetic_vertex078 h H i
          ·
            have he : (⟨79, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 79 = v.val
              omega
            simpa only [he] using homothetic_vertex079 h H i
  ·
    by_cases h88 : v.val < 88
    ·
      by_cases h84 : v.val < 84
      ·
        by_cases h82 : v.val < 82
        ·
          by_cases h81 : v.val < 81
          ·
            have he : (⟨80, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 80 = v.val
              omega
            simpa only [he] using homothetic_vertex080 h H i
          ·
            have he : (⟨81, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 81 = v.val
              omega
            simpa only [he] using homothetic_vertex081 h H i
        ·
          by_cases h83 : v.val < 83
          ·
            have he : (⟨82, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 82 = v.val
              omega
            simpa only [he] using homothetic_vertex082 h H i
          ·
            have he : (⟨83, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 83 = v.val
              omega
            simpa only [he] using homothetic_vertex083 h H i
      ·
        by_cases h86 : v.val < 86
        ·
          by_cases h85 : v.val < 85
          ·
            have he : (⟨84, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 84 = v.val
              omega
            simpa only [he] using homothetic_vertex084 h H i
          ·
            have he : (⟨85, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 85 = v.val
              omega
            simpa only [he] using homothetic_vertex085 h H i
        ·
          by_cases h87 : v.val < 87
          ·
            have he : (⟨86, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 86 = v.val
              omega
            simpa only [he] using homothetic_vertex086 h H i
          ·
            have he : (⟨87, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 87 = v.val
              omega
            simpa only [he] using homothetic_vertex087 h H i
    ·
      by_cases h92 : v.val < 92
      ·
        by_cases h90 : v.val < 90
        ·
          by_cases h89 : v.val < 89
          ·
            have he : (⟨88, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 88 = v.val
              omega
            simpa only [he] using homothetic_vertex088 h H i
          ·
            have he : (⟨89, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 89 = v.val
              omega
            simpa only [he] using homothetic_vertex089 h H i
        ·
          by_cases h91 : v.val < 91
          ·
            have he : (⟨90, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 90 = v.val
              omega
            simpa only [he] using homothetic_vertex090 h H i
          ·
            have he : (⟨91, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 91 = v.val
              omega
            simpa only [he] using homothetic_vertex091 h H i
      ·
        by_cases h94 : v.val < 94
        ·
          by_cases h93 : v.val < 93
          ·
            have he : (⟨92, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 92 = v.val
              omega
            simpa only [he] using homothetic_vertex092 h H i
          ·
            have he : (⟨93, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 93 = v.val
              omega
            simpa only [he] using homothetic_vertex093 h H i
        ·
          by_cases h95 : v.val < 95
          ·
            have he : (⟨94, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 94 = v.val
              omega
            simpa only [he] using homothetic_vertex094 h H i
          ·
            have he : (⟨95, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 95 = v.val
              omega
            simpa only [he] using homothetic_vertex095 h H i

private theorem homothetic_group03 (h : Assignment) (H : Constraints h)
    (v : Fin 144) (i : Fin 4) (hlo : 96 ≤ v.val) (hhi : v.val < 128) :
    h v i = h 1 i + ((q v i.castSucc : ℝ) / (q v 4 : ℝ)) * (h 3 0 - h 1 0) := by
  have hv_bound := v.isLt
  by_cases h112 : v.val < 112
  ·
    by_cases h104 : v.val < 104
    ·
      by_cases h100 : v.val < 100
      ·
        by_cases h98 : v.val < 98
        ·
          by_cases h97 : v.val < 97
          ·
            have he : (⟨96, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 96 = v.val
              omega
            simpa only [he] using homothetic_vertex096 h H i
          ·
            have he : (⟨97, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 97 = v.val
              omega
            simpa only [he] using homothetic_vertex097 h H i
        ·
          by_cases h99 : v.val < 99
          ·
            have he : (⟨98, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 98 = v.val
              omega
            simpa only [he] using homothetic_vertex098 h H i
          ·
            have he : (⟨99, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 99 = v.val
              omega
            simpa only [he] using homothetic_vertex099 h H i
      ·
        by_cases h102 : v.val < 102
        ·
          by_cases h101 : v.val < 101
          ·
            have he : (⟨100, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 100 = v.val
              omega
            simpa only [he] using homothetic_vertex100 h H i
          ·
            have he : (⟨101, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 101 = v.val
              omega
            simpa only [he] using homothetic_vertex101 h H i
        ·
          by_cases h103 : v.val < 103
          ·
            have he : (⟨102, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 102 = v.val
              omega
            simpa only [he] using homothetic_vertex102 h H i
          ·
            have he : (⟨103, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 103 = v.val
              omega
            simpa only [he] using homothetic_vertex103 h H i
    ·
      by_cases h108 : v.val < 108
      ·
        by_cases h106 : v.val < 106
        ·
          by_cases h105 : v.val < 105
          ·
            have he : (⟨104, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 104 = v.val
              omega
            simpa only [he] using homothetic_vertex104 h H i
          ·
            have he : (⟨105, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 105 = v.val
              omega
            simpa only [he] using homothetic_vertex105 h H i
        ·
          by_cases h107 : v.val < 107
          ·
            have he : (⟨106, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 106 = v.val
              omega
            simpa only [he] using homothetic_vertex106 h H i
          ·
            have he : (⟨107, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 107 = v.val
              omega
            simpa only [he] using homothetic_vertex107 h H i
      ·
        by_cases h110 : v.val < 110
        ·
          by_cases h109 : v.val < 109
          ·
            have he : (⟨108, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 108 = v.val
              omega
            simpa only [he] using homothetic_vertex108 h H i
          ·
            have he : (⟨109, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 109 = v.val
              omega
            simpa only [he] using homothetic_vertex109 h H i
        ·
          by_cases h111 : v.val < 111
          ·
            have he : (⟨110, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 110 = v.val
              omega
            simpa only [he] using homothetic_vertex110 h H i
          ·
            have he : (⟨111, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 111 = v.val
              omega
            simpa only [he] using homothetic_vertex111 h H i
  ·
    by_cases h120 : v.val < 120
    ·
      by_cases h116 : v.val < 116
      ·
        by_cases h114 : v.val < 114
        ·
          by_cases h113 : v.val < 113
          ·
            have he : (⟨112, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 112 = v.val
              omega
            simpa only [he] using homothetic_vertex112 h H i
          ·
            have he : (⟨113, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 113 = v.val
              omega
            simpa only [he] using homothetic_vertex113 h H i
        ·
          by_cases h115 : v.val < 115
          ·
            have he : (⟨114, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 114 = v.val
              omega
            simpa only [he] using homothetic_vertex114 h H i
          ·
            have he : (⟨115, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 115 = v.val
              omega
            simpa only [he] using homothetic_vertex115 h H i
      ·
        by_cases h118 : v.val < 118
        ·
          by_cases h117 : v.val < 117
          ·
            have he : (⟨116, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 116 = v.val
              omega
            simpa only [he] using homothetic_vertex116 h H i
          ·
            have he : (⟨117, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 117 = v.val
              omega
            simpa only [he] using homothetic_vertex117 h H i
        ·
          by_cases h119 : v.val < 119
          ·
            have he : (⟨118, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 118 = v.val
              omega
            simpa only [he] using homothetic_vertex118 h H i
          ·
            have he : (⟨119, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 119 = v.val
              omega
            simpa only [he] using homothetic_vertex119 h H i
    ·
      by_cases h124 : v.val < 124
      ·
        by_cases h122 : v.val < 122
        ·
          by_cases h121 : v.val < 121
          ·
            have he : (⟨120, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 120 = v.val
              omega
            simpa only [he] using homothetic_vertex120 h H i
          ·
            have he : (⟨121, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 121 = v.val
              omega
            simpa only [he] using homothetic_vertex121 h H i
        ·
          by_cases h123 : v.val < 123
          ·
            have he : (⟨122, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 122 = v.val
              omega
            simpa only [he] using homothetic_vertex122 h H i
          ·
            have he : (⟨123, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 123 = v.val
              omega
            simpa only [he] using homothetic_vertex123 h H i
      ·
        by_cases h126 : v.val < 126
        ·
          by_cases h125 : v.val < 125
          ·
            have he : (⟨124, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 124 = v.val
              omega
            simpa only [he] using homothetic_vertex124 h H i
          ·
            have he : (⟨125, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 125 = v.val
              omega
            simpa only [he] using homothetic_vertex125 h H i
        ·
          by_cases h127 : v.val < 127
          ·
            have he : (⟨126, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 126 = v.val
              omega
            simpa only [he] using homothetic_vertex126 h H i
          ·
            have he : (⟨127, by decide⟩ : Fin 144) = v := by
              apply Fin.ext
              change 127 = v.val
              omega
            simpa only [he] using homothetic_vertex127 h H i

private theorem homothetic_group04 (h : Assignment) (H : Constraints h)
    (v : Fin 144) (i : Fin 4) (hlo : 128 ≤ v.val) (hhi : v.val < 144) :
    h v i = h 1 i + ((q v i.castSucc : ℝ) / (q v 4 : ℝ)) * (h 3 0 - h 1 0) := by
  have hv_bound := v.isLt
  by_cases h136 : v.val < 136
  ·
    by_cases h132 : v.val < 132
    ·
      by_cases h130 : v.val < 130
      ·
        by_cases h129 : v.val < 129
        ·
          have he : (⟨128, by decide⟩ : Fin 144) = v := by
            apply Fin.ext
            change 128 = v.val
            omega
          simpa only [he] using homothetic_vertex128 h H i
        ·
          have he : (⟨129, by decide⟩ : Fin 144) = v := by
            apply Fin.ext
            change 129 = v.val
            omega
          simpa only [he] using homothetic_vertex129 h H i
      ·
        by_cases h131 : v.val < 131
        ·
          have he : (⟨130, by decide⟩ : Fin 144) = v := by
            apply Fin.ext
            change 130 = v.val
            omega
          simpa only [he] using homothetic_vertex130 h H i
        ·
          have he : (⟨131, by decide⟩ : Fin 144) = v := by
            apply Fin.ext
            change 131 = v.val
            omega
          simpa only [he] using homothetic_vertex131 h H i
    ·
      by_cases h134 : v.val < 134
      ·
        by_cases h133 : v.val < 133
        ·
          have he : (⟨132, by decide⟩ : Fin 144) = v := by
            apply Fin.ext
            change 132 = v.val
            omega
          simpa only [he] using homothetic_vertex132 h H i
        ·
          have he : (⟨133, by decide⟩ : Fin 144) = v := by
            apply Fin.ext
            change 133 = v.val
            omega
          simpa only [he] using homothetic_vertex133 h H i
      ·
        by_cases h135 : v.val < 135
        ·
          have he : (⟨134, by decide⟩ : Fin 144) = v := by
            apply Fin.ext
            change 134 = v.val
            omega
          simpa only [he] using homothetic_vertex134 h H i
        ·
          have he : (⟨135, by decide⟩ : Fin 144) = v := by
            apply Fin.ext
            change 135 = v.val
            omega
          simpa only [he] using homothetic_vertex135 h H i
  ·
    by_cases h140 : v.val < 140
    ·
      by_cases h138 : v.val < 138
      ·
        by_cases h137 : v.val < 137
        ·
          have he : (⟨136, by decide⟩ : Fin 144) = v := by
            apply Fin.ext
            change 136 = v.val
            omega
          simpa only [he] using homothetic_vertex136 h H i
        ·
          have he : (⟨137, by decide⟩ : Fin 144) = v := by
            apply Fin.ext
            change 137 = v.val
            omega
          simpa only [he] using homothetic_vertex137 h H i
      ·
        by_cases h139 : v.val < 139
        ·
          have he : (⟨138, by decide⟩ : Fin 144) = v := by
            apply Fin.ext
            change 138 = v.val
            omega
          simpa only [he] using homothetic_vertex138 h H i
        ·
          have he : (⟨139, by decide⟩ : Fin 144) = v := by
            apply Fin.ext
            change 139 = v.val
            omega
          simpa only [he] using homothetic_vertex139 h H i
    ·
      by_cases h142 : v.val < 142
      ·
        by_cases h141 : v.val < 141
        ·
          have he : (⟨140, by decide⟩ : Fin 144) = v := by
            apply Fin.ext
            change 140 = v.val
            omega
          simpa only [he] using homothetic_vertex140 h H i
        ·
          have he : (⟨141, by decide⟩ : Fin 144) = v := by
            apply Fin.ext
            change 141 = v.val
            omega
          simpa only [he] using homothetic_vertex141 h H i
      ·
        by_cases h143 : v.val < 143
        ·
          have he : (⟨142, by decide⟩ : Fin 144) = v := by
            apply Fin.ext
            change 142 = v.val
            omega
          simpa only [he] using homothetic_vertex142 h H i
        ·
          have he : (⟨143, by decide⟩ : Fin 144) = v := by
            apply Fin.ext
            change 143 = v.val
            omega
          simpa only [he] using homothetic_vertex143 h H i

/-- Every real solution of every edge equation is a translation and a
single uniform scaling of the actual rational coordinate configuration. -/
theorem constraints_homothetic (h : Assignment) (H : Constraints h)
    (v : Fin 144) (i : Fin 4) :
    h v i = h 1 i + ((q v i.castSucc : ℝ) / (q v 4 : ℝ)) * (h 3 0 - h 1 0) := by
  have hv_bound := v.isLt
  by_cases h64 : v.val < 64
  ·
    by_cases h32 : v.val < 32
    ·
      exact homothetic_group00 h H v i (by omega) (by omega)
    ·
      exact homothetic_group01 h H v i (by omega) (by omega)
  ·
    by_cases h96 : v.val < 96
    ·
      exact homothetic_group02 h H v i (by omega) (by omega)
    ·
      by_cases h128 : v.val < 128
      ·
        exact homothetic_group03 h H v i (by omega) (by omega)
      ·
        exact homothetic_group04 h H v i (by omega) (by omega)

end CubicalIndecomposability.Rigidity
