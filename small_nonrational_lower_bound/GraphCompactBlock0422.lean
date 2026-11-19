module
prelude
import GraphInputsRow28Part00002Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0422
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(28, 6607316459584), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record000_result⟩)
 (.branch 2
 (.leaf ⟨(28, 6671975849984), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record001_result⟩)
 (.leaf ⟨(28, 6676136599552), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(28, 6684446589184), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record003_result⟩)
 (.branch 5
 (.leaf ⟨(28, 6684458098688), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record004_result⟩)
 (.leaf ⟨(28, 6706864128256), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(28, 6707400998912), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record006_result⟩)
 (.branch 8
 (.leaf ⟨(28, 6707409321984), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record007_result⟩)
 (.leaf ⟨(28, 6711561748480), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(28, 6711570071552), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record009_result⟩)
 (.branch 11
 (.leaf ⟨(28, 6713642123264), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record010_result⟩)
 (.leaf ⟨(28, 6743661224000), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(28, 6844307275776), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record012_result⟩)
 (.branch 14
 (.leaf ⟨(28, 6844844081152), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record013_result⟩)
 (.leaf ⟨(28, 6851085205504), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(28, 6857053765632), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record015_result⟩)
 (.branch 17
 (.leaf ⟨(28, 6885235761408), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record016_result⟩)
 (.leaf ⟨(28, 6890610237440), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(28, 6898523316288), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record018_result⟩)
 (.branch 20
 (.leaf ⟨(28, 6919875985408), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record019_result⟩)
 (.leaf ⟨(28, 6962948374528), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(28, 6986175348736), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record021_result⟩)
 (.leaf ⟨(28, 7035962802176), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record022_result⟩))
 (.branch 24
 (.leaf ⟨(28, 7187363594240), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record023_result⟩)
 (.leaf ⟨(28, 7187371917312), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(28, 7190987473152), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record025_result⟩)
 (.branch 27
 (.leaf ⟨(28, 7191260102656), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record026_result⟩)
 (.leaf ⟨(28, 7191524343808), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(28, 7191532666880), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record028_result⟩)
 (.branch 30
 (.leaf ⟨(28, 7194876116992), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record029_result⟩)
 (.leaf ⟨(28, 7276479906304), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(28, 7276488294400), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record031_result⟩)
 (.branch 33
 (.leaf ⟨(28, 7291512881152), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record032_result⟩)
 (.leaf ⟨(28, 7294542675968), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(28, 7295673630720), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record034_result⟩)
 (.branch 36
 (.leaf ⟨(28, 7297754005504), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record035_result⟩)
 (.leaf ⟨(28, 7302587384064), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(28, 7302723731456), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record037_result⟩)
 (.branch 39
 (.leaf ⟨(28, 7302732054528), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record038_result⟩)
 (.leaf ⟨(28, 7302864175104), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(28, 7303627571456), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record040_result⟩)
 (.branch 42
 (.leaf ⟨(28, 7340904415744), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record041_result⟩)
 (.leaf ⟨(28, 7340912803840), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(28, 7373125058560), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record043_result⟩)
 (.branch 45
 (.leaf ⟨(28, 7432844148736), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record044_result⟩)
 (.leaf ⟨(28, 7478347563008), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(28, 7481971507200), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record046_result⟩)
 (.leaf ⟨(28, 7516998074880), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record047_result⟩))
 (.branch 49
 (.leaf ⟨(28, 7533666238464), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record048_result⟩)
 (.leaf ⟨(28, 7550829330432), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(28, 7551357812736), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record050_result⟩)
 (.branch 52
 (.leaf ⟨(28, 7560285421824), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record051_result⟩)
 (.leaf ⟨(28, 7562502144000), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(28, 7562774708224), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record053_result⟩)
 (.branch 55
 (.leaf ⟨(28, 7564855083008), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record054_result⟩)
 (.leaf ⟨(28, 7585717551616), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(28, 7585719648256), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record056_result⟩)
 (.branch 58
 (.leaf ⟨(28, 7597818183680), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record057_result⟩)
 (.leaf ⟨(28, 7598074036224), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(28, 7598090747904), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record059_result⟩)
 (.branch 61
 (.leaf ⟨(28, 7598602715136), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record060_result⟩)
 (.leaf ⟨(28, 7606387277824), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(28, 7606932340736), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record062_result⟩)
 (.branch 64
 (.leaf ⟨(28, 7615253839872), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record063_result⟩)
 (.leaf ⟨(28, 7615782322176), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(28, 7623567081472), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record065_result⟩)
 (.branch 67
 (.leaf ⟨(28, 7624103821312), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record066_result⟩)
 (.leaf ⟨(28, 7736985190400), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(28, 7771277819904), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record068_result⟩)
 (.branch 70
 (.leaf ⟨(28, 7771781136640), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record069_result⟩)
 (.leaf ⟨(28, 7783760068608), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(28, 7821412335616), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record071_result⟩)
 (.leaf ⟨(28, 8027969159168), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record072_result⟩))
 (.branch 74
 (.leaf ⟨(28, 8045891420160), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record073_result⟩)
 (.leaf ⟨(28, 8251743731968), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(28, 8252016361472), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record075_result⟩)
 (.branch 77
 (.leaf ⟨(28, 8252280602624), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record076_result⟩)
 (.leaf ⟨(28, 8252288925696), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(28, 8252511813632), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record078_result⟩)
 (.branch 80
 (.leaf ⟨(28, 8264626503936), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record079_result⟩)
 (.leaf ⟨(28, 8264994062336), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(28, 8265167536128), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record081_result⟩)
 (.branch 83
 (.leaf ⟨(28, 8267846156544), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record082_result⟩)
 (.leaf ⟨(28, 8268617879552), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(28, 8324200857600), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record084_result⟩)
 (.branch 86
 (.leaf ⟨(28, 8324209180672), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record085_result⟩)
 (.leaf ⟨(28, 8325265752064), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(28, 8332253888768), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record087_result⟩)
 (.branch 89
 (.leaf ⟨(28, 8333042126848), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record088_result⟩)
 (.leaf ⟨(28, 8333310460160), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(28, 8333587185664), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record090_result⟩)
 (.branch 92
 (.leaf ⟨(28, 8334115602944), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record091_result⟩)
 (.leaf ⟨(28, 8334123991040), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(28, 8478810701824), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record093_result⟩)
 (.branch 95
 (.leaf ⟨(28, 8525795885056), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record094_result⟩)
 (.leaf ⟨(28, 8538797903872), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(28, 8539607203840), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record096_result⟩)
 (.leaf ⟨(28, 8539871379968), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record097_result⟩))
 (.branch 99
 (.leaf ⟨(28, 8539879768064), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record098_result⟩)
 (.leaf ⟨(28, 8540144009216), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00002.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (19504 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 19504 19604 :=
  block_of_table results 19504 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0422
