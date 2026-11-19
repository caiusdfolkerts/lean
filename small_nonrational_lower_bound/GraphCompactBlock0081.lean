module
prelude
import GraphInputsRow23Part00003Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0081
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 39
 (.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(23, 6857598959616), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record000_result⟩)
 (.leaf ⟨(23, 6912018022400), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record001_result⟩))
 (.branch 3
 (.leaf ⟨(23, 6977465942016), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record002_result⟩)
 (.leaf ⟨(23, 6982278905856), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(23, 6982287228928), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record004_result⟩)
 (.leaf ⟨(23, 6983905247232), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record005_result⟩))
 (.branch 7
 (.leaf ⟨(23, 6986447978496), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record006_result⟩)
 (.branch 8
 (.leaf ⟨(23, 6988528353280), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record007_result⟩)
 (.leaf ⟨(23, 6995161677824), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(23, 6999458709504), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record009_result⟩)
 (.leaf ⟨(23, 7003082653696), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record010_result⟩))
 (.branch 12
 (.leaf ⟨(23, 7003355217920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record011_result⟩)
 (.branch 13
 (.leaf ⟨(23, 7003619459072), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record012_result⟩)
 (.leaf ⟨(23, 7003883700224), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(23, 7048242954496), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record014_result⟩)
 (.leaf ⟨(23, 7050864164864), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record015_result⟩))
 (.branch 17
 (.leaf ⟨(23, 7098039566336), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record016_result⟩)
 (.branch 18
 (.leaf ⟨(23, 7150227259392), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record017_result⟩)
 (.leaf ⟨(23, 7150359379968), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record018_result⟩))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf ⟨(23, 7156800765952), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record019_result⟩)
 (.leaf ⟨(23, 7157062926336), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record020_result⟩))
 (.branch 22
 (.leaf ⟨(23, 7157065007104), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record021_result⟩)
 (.branch 23
 (.leaf ⟨(23, 7158246674448), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record022_result⟩)
 (.leaf ⟨(23, 7185770283264), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record023_result⟩))))
 (.branch 26
 (.branch 25
 (.leaf ⟨(23, 7185774510080), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record024_result⟩)
 (.leaf ⟨(23, 7185778086144), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record025_result⟩))
 (.branch 27
 (.leaf ⟨(23, 7186298177552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record026_result⟩)
 (.branch 28
 (.leaf ⟨(23, 7186831081472), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_result⟩)
 (.leaf ⟨(23, 7187371917313), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record028_result⟩)))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf ⟨(23, 7187371982848), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record029_result⟩)
 (.leaf ⟨(23, 7190069460992), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record030_result⟩))
 (.branch 32
 (.leaf ⟨(23, 7190333702144), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record031_result⟩)
 (.branch 33
 (.leaf ⟨(23, 7190458927120), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record032_result⟩)
 (.leaf ⟨(23, 7191532666881), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record033_result⟩))))
 (.branch 36
 (.branch 35
 (.leaf ⟨(23, 7191532732416), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record034_result⟩)
 (.leaf ⟨(23, 7200122634240), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record035_result⟩))
 (.branch 37
 (.leaf ⟨(23, 7203478048768), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record036_result⟩)
 (.branch 38
 (.leaf ⟨(23, 7217986699520), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record037_result⟩)
 (.leaf ⟨(23, 7225825361920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record038_result⟩)))))))
 (.branch 58
 (.branch 48
 (.branch 43
 (.branch 41
 (.branch 40
 (.leaf ⟨(23, 7234146861056), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record039_result⟩)
 (.leaf ⟨(23, 7234415263744), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record040_result⟩))
 (.branch 42
 (.leaf ⟨(23, 7235690303488), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record041_result⟩)
 (.leaf ⟨(23, 7276492488704), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record042_result⟩)))
 (.branch 45
 (.branch 44
 (.leaf ⟨(23, 7286575599872), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record043_result⟩)
 (.leaf ⟨(23, 7286707720448), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record044_result⟩))
 (.branch 46
 (.leaf ⟨(23, 7293417054208), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record045_result⟩)
 (.branch 47
 (.leaf ⟨(23, 7301790435344), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record046_result⟩)
 (.leaf ⟨(23, 7302732120064), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record047_result⟩)))))
 (.branch 53
 (.branch 50
 (.branch 49
 (.leaf ⟨(23, 7304275562496), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record048_result⟩)
 (.leaf ⟨(23, 7340916998144), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record049_result⟩))
 (.branch 51
 (.leaf ⟨(23, 7345201545216), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record050_result⟩)
 (.branch 52
 (.leaf ⟨(23, 7428963831808), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record051_result⟩)
 (.leaf ⟨(23, 7433124581376), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record052_result⟩))))
 (.branch 55
 (.branch 54
 (.leaf ⟨(23, 7435204956160), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record053_result⟩)
 (.leaf ⟨(23, 7518138925056), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record054_result⟩))
 (.branch 56
 (.leaf ⟨(23, 7525072437248), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record055_result⟩)
 (.branch 57
 (.leaf ⟨(23, 7533938868224), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record056_result⟩)
 (.leaf ⟨(23, 7534178271232), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record057_result⟩))))))
 (.branch 68
 (.branch 63
 (.branch 60
 (.branch 59
 (.leaf ⟨(23, 7542768173056), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record058_result⟩)
 (.leaf ⟨(23, 7551357813248), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record059_result⟩))
 (.branch 61
 (.leaf ⟨(23, 7551374589952), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record060_result⟩)
 (.branch 62
 (.leaf ⟨(23, 7560302199040), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record061_result⟩)
 (.leaf ⟨(23, 7560306425856), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record062_result⟩))))
 (.branch 65
 (.branch 64
 (.leaf ⟨(23, 7560430094336), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record063_result⟩)
 (.leaf ⟨(23, 7560562214912), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064_result⟩))
 (.branch 66
 (.leaf ⟨(23, 7563039014912), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record065_result⟩)
 (.branch 67
 (.leaf ⟨(23, 7563047337984), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record066_result⟩)
 (.leaf ⟨(23, 7564846695168), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record067_result⟩)))))
 (.branch 73
 (.branch 70
 (.branch 69
 (.leaf ⟨(23, 7564855148544), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record068_result⟩)
 (.leaf ⟨(23, 7565119389696), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record069_result⟩))
 (.branch 71
 (.leaf ⟨(23, 7565127712768), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record070_result⟩)
 (.branch 72
 (.leaf ⟨(23, 7572607205376), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record071_result⟩)
 (.leaf ⟨(23, 7577465291008), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record072_result⟩))))
 (.branch 75
 (.branch 74
 (.leaf ⟨(23, 7578002161664), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record073_result⟩)
 (.leaf ⟨(23, 7585718616064), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record074_result⟩))
 (.branch 76
 (.leaf ⟨(23, 7593653469440), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record075_result⟩)
 (.branch 77
 (.leaf ⟨(23, 7593657696256), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record076_result⟩)
 (.leaf ⟨(23, 7593665759232), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record077_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (5860 + i))) 0 78 :=
  interval_of_check _ 0 78 (by decide +kernel)

public theorem complete : Block 5860 5938 :=
  block_of_table results 5860 78 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0081
