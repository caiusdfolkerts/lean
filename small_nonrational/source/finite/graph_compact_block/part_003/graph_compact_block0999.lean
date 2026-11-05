module
prelude
import GraphInputsSix0Part00034Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0999
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 12927990171664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 12928143069440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record001_result⟩)
 (.leaf ⟨(32, 13104356261888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 13125437260032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 13125437325312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record004_result⟩)
 (.leaf ⟨(32, 13125441161472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 13125441226752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 13125445355648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record007_result⟩)
 (.leaf ⟨(32, 13125449417736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 13125697013768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 13125697143816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record010_result⟩)
 (.leaf ⟨(32, 13125709791232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 13125713920001), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 13125961384968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record013_result⟩)
 (.leaf ⟨(32, 13134278560000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 13134295204608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 13134412972032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record016_result⟩)
 (.leaf ⟨(32, 13136568516608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 13197472006528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 13197538066816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record019_result⟩)
 (.leaf ⟨(32, 13197672268160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 13197940670848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record021_result⟩)
 (.leaf ⟨(32, 13199819743616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 13199852773760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record023_result⟩)
 (.leaf ⟨(32, 13204114710848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 13204147740992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 13204383146176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record026_result⟩)
 (.leaf ⟨(32, 13231863333248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 13231997534592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 13232135831808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record029_result⟩)
 (.leaf ⟨(32, 13232265937280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 13232538484800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 13233088438656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record032_result⟩)
 (.leaf ⟨(32, 13233104953728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 13234211980160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 13234216206592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record035_result⟩)
 (.leaf ⟨(32, 13234685968416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 13237265703296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 13237383405888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record038_result⟩)
 (.leaf ⟨(32, 13237399920960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 13237651841216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 13238506947392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record041_result⟩)
 (.leaf ⟨(32, 13238509076736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 13238708412608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 13238773317888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record044_result⟩)
 (.leaf ⟨(32, 13238779609152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 13238846717984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record046_result⟩)
 (.leaf ⟨(32, 13240950096128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 13240954322944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record048_result⟩)
 (.leaf ⟨(32, 13271743144224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 13271793209632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 13272866685728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record051_result⟩)
 (.leaf ⟨(32, 13272867766528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 13273139347488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 13273940427536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record054_result⟩)
 (.leaf ⟨(32, 13281453506816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 13304479121664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 13304479186944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record057_result⟩)
 (.leaf ⟨(32, 13306103431424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 13306367672576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 13306375012384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record060_result⟩)
 (.leaf ⟨(32, 13308371468544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 13308639871232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 13308639936512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record063_result⟩)
 (.leaf ⟨(32, 13310921548032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 13336167653664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 13338364936976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record066_result⟩)
 (.leaf ⟨(32, 13340378468640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 13341451944736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 13341587226880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record069_result⟩)
 (.leaf ⟨(32, 13341855629568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 13341855678528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record071_result⟩)
 (.leaf ⟨(32, 13341856727072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 13350172967168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record073_result⟩)
 (.leaf ⟨(32, 13350177128704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 13350177177664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 13350178226208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record076_result⟩)
 (.leaf ⟨(32, 13377088848128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 13377292222720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 13377357250816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record079_result⟩)
 (.leaf ⟨(32, 13377357316096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 13379506807040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 13384805269632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record082_result⟩)
 (.leaf ⟨(32, 13385674588416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 13385678749952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 13385678815232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record085_result⟩)
 (.leaf ⟨(32, 13386412721408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 13386945429760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 13422590697504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record088_result⟩)
 (.leaf ⟨(32, 13487611887872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 13507214983296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 13513654288512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record091_result⟩)
 (.leaf ⟨(32, 13514694475904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 13516677325056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 13524115947776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record094_result⟩)
 (.leaf ⟨(32, 13524384383104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 13524652818432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record096_result⟩)
 (.leaf ⟨(32, 13524656979968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 13531397259520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record098_result⟩)
 (.leaf ⟨(32, 13610291052672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00034.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (30186 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 30186 30286 :=
  block_of_table results 30186 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0999
