module
prelude
import GraphInputsSix0Part00013Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0978
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 5892764565512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 5892909041920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record001_result⟩)
 (.leaf ⟨(32, 5893251956992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 5893252022272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 5893309597824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record004_result⟩)
 (.leaf ⟨(32, 5895650050304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 5895660519424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 5899141907712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record007_result⟩)
 (.leaf ⟨(32, 5899141972992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 5899150164996), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 5899406213376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record010_result⟩)
 (.leaf ⟨(32, 5899410276608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 5899414405636), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 5899414536193), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record013_result⟩)
 (.leaf ⟨(32, 5899414601728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 5899674616064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 5899683004416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record016_result⟩)
 (.leaf ⟨(32, 5899687035904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 5899942888192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 5899947147264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record019_result⟩)
 (.leaf ⟨(32, 5899955470336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 5902091436288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record021_result⟩)
 (.leaf ⟨(32, 5903571026176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 5903843655680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record023_result⟩)
 (.leaf ⟨(32, 5904107896832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 5904116219904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 5904240017408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record026_result⟩)
 (.leaf ⟨(32, 5904380461056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 5951088296192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 5951352537344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record029_result⟩)
 (.leaf ⟨(32, 5951360925696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 5951484657920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 5955645407488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record032_result⟩)
 (.leaf ⟨(32, 5955653795840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 5963966906624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 5963975294976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record035_result⟩)
 (.leaf ⟨(32, 5964235309312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 5964245778432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 5964369510656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record038_result⟩)
 (.leaf ⟨(32, 5966515945728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 5972288405760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 5972825276416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record041_result⟩)
 (.leaf ⟨(32, 5972833599488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 5974368780544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 5974509289472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record044_result⟩)
 (.leaf ⟨(32, 5974905651200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 5974913974272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record046_result⟩)
 (.leaf ⟨(32, 5989938036992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 5998527938816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record048_result⟩)
 (.leaf ⟨(32, 5998538407936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 6048447545728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 6048480575872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record051_result⟩)
 (.leaf ⟨(32, 6048950280576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 6049621414272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 6050017776000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record054_result⟩)
 (.leaf ⟨(32, 6050024067264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 6051116187904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 6065049063808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record057_result⟩)
 (.leaf ⟨(32, 6066141233408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 6066147508352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 6066182127632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record060_result⟩)
 (.leaf ⟨(32, 6086245681424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 6086262326032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 6086531318016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record063_result⟩)
 (.leaf ⟨(32, 6087587889408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 6087860355328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 6092021104896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record066_result⟩)
 (.leaf ⟨(32, 6099416170752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 6099416203392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 6099417792528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record069_result⟩)
 (.leaf ⟨(32, 6100342604032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 6100611006720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record071_result⟩)
 (.leaf ⟨(32, 6100611072000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 6100745208064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record073_result⟩)
 (.leaf ⟨(32, 6103966421248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 6164091830528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 6172677570816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record076_result⟩)
 (.leaf ⟨(32, 6172685959168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 6195031113984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 6203220492544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record079_result⟩)
 (.leaf ⟨(32, 6203352613120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 6203621015808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 6203621081088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record082_result⟩)
 (.leaf ⟨(32, 6203623096576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 6204763934976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 6241262829824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record085_result⟩)
 (.leaf ⟨(32, 6275753640192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 6288394486016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 6296984158464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record088_result⟩)
 (.leaf ⟨(32, 6301262348544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 6305557383424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 6305557448704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record091_result⟩)
 (.leaf ⟨(32, 6305569898752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 6305578287104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 6305817624832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record094_result⟩)
 (.leaf ⟨(32, 6309583847680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 6310120718336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record096_result⟩)
 (.leaf ⟨(32, 6318442217472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 6324903575568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record098_result⟩)
 (.leaf ⟨(32, 6329452204288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00013.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (28086 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 28086 28186 :=
  block_of_table results 28086 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0978
