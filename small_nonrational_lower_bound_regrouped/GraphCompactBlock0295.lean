module
prelude
import GraphInputsRow25Part00005Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0295
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 32
 (.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(25, 7003619459072), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record000_result⟩)
 (.leaf ⟨(25, 7003883700224), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record001_result⟩))
 (.branch 3
 (.leaf ⟨(25, 7048242954496), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record002_result⟩)
 (.leaf ⟨(25, 7050864164864), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(25, 7098039566336), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record004_result⟩)
 (.leaf ⟨(25, 7150227194112), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record005_result⟩))
 (.branch 7
 (.leaf ⟨(25, 7150227259392), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record006_result⟩)
 (.leaf ⟨(25, 7150359379968), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(25, 7150462046464), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record008_result⟩)
 (.leaf ⟨(25, 7154085924880), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record009_result⟩))
 (.branch 11
 (.leaf ⟨(25, 7156800765952), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record010_result⟩)
 (.leaf ⟨(25, 7156901351680), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(25, 7157062926336), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record012_result⟩)
 (.leaf ⟨(25, 7157065007104), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record013_result⟩))
 (.branch 15
 (.leaf ⟨(25, 7158246674448), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record014_result⟩)
 (.leaf ⟨(25, 7165421031680), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(25, 7185774510080), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record016_result⟩)
 (.leaf ⟨(25, 7185778086144), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record017_result⟩))
 (.branch 19
 (.leaf ⟨(25, 7186298177552), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record018_result⟩)
 (.leaf ⟨(25, 7186831016192), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(25, 7186831081472), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record020_result⟩)
 (.leaf ⟨(25, 7187371917313), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record021_result⟩))
 (.branch 23
 (.leaf ⟨(25, 7187371982848), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record022_result⟩)
 (.leaf ⟨(25, 7190333702144), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(25, 7190335197440), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record024_result⟩)
 (.leaf ⟨(25, 7190458927120), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record025_result⟩))
 (.branch 27
 (.leaf ⟨(25, 7191532666881), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record026_result⟩)
 (.leaf ⟨(25, 7203478048768), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(25, 7217986699520), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record028_result⟩)
 (.leaf ⟨(25, 7225825361920), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record029_result⟩))
 (.branch 31
 (.leaf ⟨(25, 7234146861056), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record030_result⟩)
 (.leaf ⟨(25, 7234415263744), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record031_result⟩))))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.branch 34
 (.branch 33
 (.leaf ⟨(25, 7235678273792), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record032_result⟩)
 (.leaf ⟨(25, 7235690303488), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record033_result⟩))
 (.branch 35
 (.leaf ⟨(25, 7276492488704), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record034_result⟩)
 (.leaf ⟨(25, 7286575599872), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record035_result⟩)))
 (.branch 38
 (.branch 37
 (.leaf ⟨(25, 7293417054208), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record036_result⟩)
 (.leaf ⟨(25, 7293468936208), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record037_result⟩))
 (.branch 39
 (.leaf ⟨(25, 7294542675969), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record038_result⟩)
 (.leaf ⟨(25, 7301658314768), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record039_result⟩))))
 (.branch 44
 (.branch 42
 (.branch 41
 (.leaf ⟨(25, 7301790435344), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record040_result⟩)
 (.leaf ⟨(25, 7301856495632), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record041_result⟩))
 (.branch 43
 (.leaf ⟨(25, 7302732054529), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record042_result⟩)
 (.leaf ⟨(25, 7302864175105), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record043_result⟩)))
 (.branch 46
 (.branch 45
 (.leaf ⟨(25, 7304275562496), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record044_result⟩)
 (.leaf ⟨(25, 7340916998144), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record045_result⟩))
 (.branch 47
 (.leaf ⟨(25, 7424142479616), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record046_result⟩)
 (.leaf ⟨(25, 7428963831808), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record047_result⟩)))))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf ⟨(25, 7433124581376), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record048_result⟩)
 (.leaf ⟨(25, 7478343369344), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record049_result⟩))
 (.branch 51
 (.leaf ⟨(25, 7518138925056), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record050_result⟩)
 (.leaf ⟨(25, 7525072437248), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record051_result⟩)))
 (.branch 54
 (.branch 53
 (.leaf ⟨(25, 7533641206016), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record052_result⟩)
 (.leaf ⟨(25, 7533657850624), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record053_result⟩))
 (.branch 55
 (.leaf ⟨(25, 7533938868224), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record054_result⟩)
 (.leaf ⟨(25, 7534178271232), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record055_result⟩))))
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf ⟨(25, 7542768173056), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record056_result⟩)
 (.leaf ⟨(25, 7550552670464), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record057_result⟩))
 (.branch 59
 (.leaf ⟨(25, 7551357813248), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record058_result⟩)
 (.leaf ⟨(25, 7551374589952), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record059_result⟩)))
 (.branch 62
 (.branch 61
 (.leaf ⟨(25, 7560302199040), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record060_result⟩)
 (.leaf ⟨(25, 7560306425856), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record061_result⟩))
 (.branch 63
 (.leaf ⟨(25, 7560417804544), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record062_result⟩)
 (.leaf ⟨(25, 7560430094336), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00005.record063_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (12518 + i))) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

public theorem complete : Block 12518 12582 :=
  block_of_table results 12518 64 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0295
