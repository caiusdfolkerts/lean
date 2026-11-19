module
prelude
import GraphInputsRow19Part00030Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0070
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 31448333551648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 31449440845825), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record001_result⟩)
 (.leaf ⟨(19, 31449449299968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 31449457623040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 31451248787456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record004_result⟩)
 (.leaf ⟨(19, 31464981823744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 31464986050560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 31464993333248), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record007_result⟩)
 (.leaf ⟨(19, 31465035595776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 31465224544256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 31465753026560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record010_result⟩)
 (.leaf ⟨(19, 31465754066944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 31466075652096), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 31466083845120), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record013_result⟩)
 (.leaf ⟨(19, 31466272727296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 31466281115648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 31466282025984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record016_result⟩)
 (.leaf ⟨(19, 31466339697408), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 31466809459232), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 31466876568064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record019_result⟩)
 (.leaf ⟨(19, 31475962560528), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 31476848591104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record021_result⟩)
 (.leaf ⟨(19, 31476852752640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 31476852817920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record023_result⟩)
 (.leaf ⟨(19, 31476914651392), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(19, 31476918878208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record025_result⟩)
 (.branch 27
 (.leaf ⟨(19, 31476921934080), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record026_result⟩)
 (.leaf ⟨(19, 31477425246240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(19, 31478110035984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record028_result⟩)
 (.branch 30
 (.leaf ⟨(19, 31478374277136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record029_result⟩)
 (.leaf ⟨(19, 31479200555008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(19, 31479233585152), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 31479472070688), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record032_result⟩)
 (.leaf ⟨(19, 31481141461248), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(19, 31481149849600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record034_result⟩)
 (.branch 36
 (.leaf ⟨(19, 31481339642112), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record035_result⟩)
 (.leaf ⟨(19, 31481348030464), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(19, 31481381060608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record037_result⟩)
 (.branch 39
 (.leaf ⟨(19, 31481608044800), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record038_result⟩)
 (.leaf ⟨(19, 31481619554304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(19, 31481842376960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 31481876512768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record041_result⟩)
 (.leaf ⟨(19, 31481884835840), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(19, 31482667147280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record043_result⟩)
 (.branch 45
 (.leaf ⟨(19, 31482672865312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record044_result⟩)
 (.leaf ⟨(19, 31483394334720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 31483757601024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record046_result⟩)
 (.leaf ⟨(19, 31487580766464), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 31487589154816), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record048_result⟩)
 (.leaf ⟨(19, 31488050471168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(19, 31488058859520), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record050_result⟩)
 (.branch 52
 (.leaf ⟨(19, 31489132077056), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record051_result⟩)
 (.leaf ⟨(19, 31494024233216), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(19, 31494028460032), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record053_result⟩)
 (.branch 55
 (.leaf ⟨(19, 31494090293504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record054_result⟩)
 (.leaf ⟨(19, 31494094520320), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(19, 31494101803008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record056_result⟩)
 (.branch 58
 (.leaf ⟨(19, 31494358761472), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record057_result⟩)
 (.leaf ⟨(19, 31494367084544), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(19, 31494861496320), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record059_result⟩)
 (.branch 61
 (.leaf ⟨(19, 31494862536704), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record060_result⟩)
 (.leaf ⟨(19, 31496170668288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(19, 31496174895104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record062_result⟩)
 (.branch 64
 (.leaf ⟨(19, 31496182177792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record063_result⟩)
 (.leaf ⟨(19, 31496371970304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(19, 31496380358656), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record065_result⟩)
 (.branch 67
 (.leaf ⟨(19, 31496874762272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record066_result⟩)
 (.leaf ⟨(19, 31496908840960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(19, 31496941871104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record068_result⟩)
 (.branch 70
 (.leaf ⟨(19, 31496942911488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record069_result⟩)
 (.leaf ⟨(19, 31497453576192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(19, 31501102620672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record071_result⟩)
 (.leaf ⟨(19, 31503686312192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record072_result⟩))
 (.branch 74
 (.leaf ⟨(19, 31503687417856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record073_result⟩)
 (.leaf ⟨(19, 31503694700544), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(19, 31504156074016), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record075_result⟩)
 (.branch 77
 (.leaf ⟨(19, 31509044068608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record076_result⟩)
 (.leaf ⟨(19, 31509048230144), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(19, 31509048295424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record078_result⟩)
 (.branch 80
 (.leaf ⟨(19, 31509110128896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record079_result⟩)
 (.leaf ⟨(19, 31509114290432), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(19, 31509114355712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record081_result⟩)
 (.branch 83
 (.leaf ⟨(19, 31509117411584), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record082_result⟩)
 (.leaf ⟨(19, 31509167737088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(19, 31509510717440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record084_result⟩)
 (.branch 86
 (.leaf ⟨(19, 31509516959744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record085_result⟩)
 (.leaf ⟨(19, 31509637498912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(19, 31512469184768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record087_result⟩)
 (.branch 89
 (.leaf ⟨(19, 31512469250048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record088_result⟩)
 (.leaf ⟨(19, 31512486480128), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(19, 31512733491200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record090_result⟩)
 (.branch 92
 (.leaf ⟨(19, 31512758061088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record091_result⟩)
 (.leaf ⟨(19, 31520816431360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(19, 31520824819712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record093_result⟩)
 (.branch 95
 (.leaf ⟨(19, 31521327554560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record094_result⟩)
 (.leaf ⟨(19, 31521906032896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(19, 31521914421248), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record096_result⟩)
 (.leaf ⟨(19, 31522385036288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record097_result⟩))
 (.branch 99
 (.leaf ⟨(19, 31528419786752), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record098_result⟩)
 (.leaf ⟨(19, 31528427979776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00030.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (5015 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 5015 5115 :=
  block_of_table results 5015 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0070
