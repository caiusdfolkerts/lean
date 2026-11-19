module
prelude
import GraphInputsSix0Part00016Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0981
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 6791631011840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 6792031535104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record001_result⟩)
 (.leaf ⟨(32, 6816726548736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 6816796778752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 6822095241344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record004_result⟩)
 (.leaf ⟨(32, 6823698661632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 6823702693120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 6823834878208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record007_result⟩)
 (.leaf ⟨(32, 6823843266560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 6824041447424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 6824235401472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record010_result⟩)
 (.leaf ⟨(32, 6824243789824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 6837674279168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 6837680521472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record013_result⟩)
 (.leaf ⟨(32, 6837682405384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 6838144827400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 6838147948552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record016_result⟩)
 (.leaf ⟨(32, 6839874029824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 6839878254600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 6839899062528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record019_result⟩)
 (.leaf ⟨(32, 6840280858632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 6840295424256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record021_result⟩)
 (.leaf ⟨(32, 6840299585792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 6840299651072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record023_result⟩)
 (.leaf ⟨(32, 6840419092736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 6841954404608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 6842177618176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record026_result⟩)
 (.leaf ⟨(32, 6842441859328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 6842446020864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 6842446086144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record029_result⟩)
 (.leaf ⟨(32, 6842499467520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 6844839952640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 6844848340992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record032_result⟩)
 (.leaf ⟨(32, 6848736461056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 6849000702208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 6849009090560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record035_result⟩)
 (.leaf ⟨(32, 6849132822784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 6851081076992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 6851089465344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record038_result⟩)
 (.leaf ⟨(32, 6854837239816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 6854843482120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 6854981716224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record041_result⟩)
 (.leaf ⟨(32, 6855179897088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 6855324631296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 6855324696576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record044_result⟩)
 (.leaf ⟨(32, 6855327817728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 6855330906240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record046_result⟩)
 (.leaf ⟨(32, 6855382272128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 6857598959617), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record048_result⟩)
 (.leaf ⟨(32, 6857722724608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 6857733193728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 6864164110592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record051_result⟩)
 (.leaf ⟨(32, 6865643700480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 6865916329984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 6866180571136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record054_result⟩)
 (.leaf ⟨(32, 6866188894208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 6866312691712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 6866453135360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record057_result⟩)
 (.leaf ⟨(32, 6875275903232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 6875341963520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 6877489438976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record060_result⟩)
 (.leaf ⟨(32, 6877621559552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 6878604132368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 6878736252944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record063_result⟩)
 (.leaf ⟨(32, 6878802313232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 6885244739600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 6890405855360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record066_result⟩)
 (.leaf ⟨(32, 6890407903488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 6890407936128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 6890408976512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record069_result⟩)
 (.leaf ⟨(32, 6890610327584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 6907471380736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record071_result⟩)
 (.leaf ⟨(32, 6907537441024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 6909937647872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record073_result⟩)
 (.leaf ⟨(32, 6909941809408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 6909941874688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 6910210244736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record076_result⟩)
 (.leaf ⟨(32, 6910212325504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 6910758134016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 6910889214208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record079_result⟩)
 (.leaf ⟨(32, 6910890254592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 6911890063616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 6911890128896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record082_result⟩)
 (.leaf ⟨(32, 6912018022656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 6912022184192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 6912022249472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record085_result⟩)
 (.leaf ⟨(32, 6912088244480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 6912088309760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 6912290619520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record088_result⟩)
 (.leaf ⟨(32, 6912292700288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 6919601324288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 6919603953664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record091_result⟩)
 (.leaf ⟨(32, 6919605485824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 6919605551104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 6919772192896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record094_result⟩)
 (.leaf ⟨(32, 6920010211392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 6920335491072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record096_result⟩)
 (.leaf ⟨(32, 6926043807744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 6927113289984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record098_result⟩)
 (.leaf ⟨(32, 6927117516800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00016.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (28386 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 28386 28486 :=
  block_of_table results 28386 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0981
