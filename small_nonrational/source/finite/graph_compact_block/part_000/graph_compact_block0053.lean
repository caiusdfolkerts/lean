module
prelude
import GraphInputsRow19Part00013Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0053
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 17300405225472), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 17300933575176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record001_result⟩)
 (.leaf ⟨(19, 17320837709824), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 17327277015040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 17329431773184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record004_result⟩)
 (.leaf ⟨(19, 17329522540544), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 17329563893760), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 17332643102720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record007_result⟩)
 (.leaf ⟨(19, 17353033187328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 17356252839936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 17360545710080), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record010_result⟩)
 (.leaf ⟨(19, 17361734206208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 17364838580224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 17364846903296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record013_result⟩)
 (.leaf ⟨(19, 17420677087232), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 17429245856000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 17455906849024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record016_result⟩)
 (.leaf ⟨(19, 17455911075840), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 17456109256704), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 17456166864896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record019_result⟩)
 (.leaf ⟨(19, 17457046126848), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 17457050353664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record021_result⟩)
 (.leaf ⟨(19, 17457058156544), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 17457182474240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record023_result⟩)
 (.leaf ⟨(19, 17457190277120), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(19, 17457207052288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record025_result⟩)
 (.branch 27
 (.leaf ⟨(19, 17461475344384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record026_result⟩)
 (.leaf ⟨(19, 17462012149760), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(19, 17463448176640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record028_result⟩)
 (.branch 30
 (.leaf ⟨(19, 17463893823488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record029_result⟩)
 (.leaf ⟨(19, 17463910598656), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(19, 17466172899328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 17469813227520), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record032_result⟩)
 (.leaf ⟨(19, 17469821550592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(19, 17470316482560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record034_result⟩)
 (.branch 36
 (.leaf ⟨(19, 17489258119424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record035_result⟩)
 (.leaf ⟨(19, 17489262346240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(19, 17489270409216), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record037_result⟩)
 (.branch 39
 (.leaf ⟨(19, 17489402529792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record038_result⟩)
 (.leaf ⟨(19, 17489509746944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(19, 17493670365440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 17493678753792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record041_result⟩)
 (.leaf ⟨(19, 17493687010048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(19, 17494207103496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record043_result⟩)
 (.branch 45
 (.leaf ⟨(19, 17497839503360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record044_result⟩)
 (.leaf ⟨(19, 17498367853064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 17519171600900), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record046_result⟩)
 (.leaf ⟨(19, 17519171732480), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 17523487737856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record048_result⟩)
 (.leaf ⟨(19, 17557843378432), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(19, 17558111846400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record050_result⟩)
 (.branch 52
 (.leaf ⟨(19, 17558120169472), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record051_result⟩)
 (.leaf ⟨(19, 17558631876608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(19, 17566416374016), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record053_result⟩)
 (.branch 55
 (.leaf ⟨(19, 17566953244672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record054_result⟩)
 (.leaf ⟨(19, 17566969889280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(19, 17566970150912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record056_result⟩)
 (.branch 58
 (.leaf ⟨(19, 17583596110340), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record057_result⟩)
 (.leaf ⟨(19, 17583596242944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(19, 17583613018112), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record059_result⟩)
 (.branch 61
 (.leaf ⟨(19, 17716410941440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record060_result⟩)
 (.leaf ⟨(19, 17716415070336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(19, 17716419264512), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record062_result⟩)
 (.branch 64
 (.leaf ⟨(19, 17786744160384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record063_result⟩)
 (.leaf ⟨(19, 17787274690816), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(19, 17787283079168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record065_result⟩)
 (.branch 67
 (.leaf ⟨(19, 17787784347776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record066_result⟩)
 (.leaf ⟨(19, 17843853803776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(19, 17844056195136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record068_result⟩)
 (.branch 70
 (.leaf ⟨(19, 17848351097088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record069_result⟩)
 (.leaf ⟨(19, 17848351162368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(19, 17848479056128), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record071_result⟩)
 (.leaf ⟨(19, 17848487444480), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record072_result⟩))
 (.branch 74
 (.leaf ⟨(19, 17848619565056), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record073_result⟩)
 (.leaf ⟨(19, 17852722610432), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(19, 17852730998784), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record075_result⟩)
 (.branch 77
 (.leaf ⟨(19, 17856402243712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record076_result⟩)
 (.leaf ⟨(19, 17856668434688), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(19, 17856672596224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record078_result⟩)
 (.branch 80
 (.leaf ⟨(19, 17856672661504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record079_result⟩)
 (.leaf ⟨(19, 17856674676992), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(19, 17857068925696), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record081_result⟩)
 (.branch 83
 (.leaf ⟨(19, 17857073119872), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record082_result⟩)
 (.leaf ⟨(19, 17857077313537), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(19, 17857144430656), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record084_result⟩)
 (.branch 86
 (.leaf ⟨(19, 17857201078528), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record085_result⟩)
 (.leaf ⟨(19, 17857205305344), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(19, 17857211547648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record087_result⟩)
 (.branch 89
 (.leaf ⟨(19, 17857213628416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record088_result⟩)
 (.leaf ⟨(19, 17860833345792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(19, 17860833411072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record090_result⟩)
 (.branch 92
 (.leaf ⟨(19, 17860967547136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record091_result⟩)
 (.leaf ⟨(19, 17861231853568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(19, 17861305180224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record093_result⟩)
 (.branch 95
 (.leaf ⟨(19, 17861504417792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record094_result⟩)
 (.leaf ⟨(19, 17861562089728), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(19, 17861564235776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record096_result⟩)
 (.leaf ⟨(19, 17861570478080), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record097_result⟩))
 (.branch 99
 (.leaf ⟨(19, 17863113982208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record098_result⟩)
 (.leaf ⟨(19, 17916633366656), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00013.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (3365 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 3365 3465 :=
  block_of_table results 3365 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0053
