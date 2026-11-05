module
prelude
import GraphInputsRow27Part00007Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0410
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(27, 17082431373568), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record000_result⟩)
 (.branch 2
 (.leaf ⟨(27, 17082968244224), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record001_result⟩)
 (.leaf ⟨(27, 17082976567296), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(27, 17087128993792), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record003_result⟩)
 (.branch 5
 (.leaf ⟨(27, 17087137316864), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record004_result⟩)
 (.leaf ⟨(27, 17120050348032), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(27, 17120293847296), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record006_result⟩)
 (.branch 8
 (.leaf ⟨(27, 17120305876992), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record007_result⟩)
 (.leaf ⟨(27, 17146855883008), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(27, 17155450011648), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record009_result⟩)
 (.branch 11
 (.leaf ⟨(27, 17155986817024), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record010_result⟩)
 (.leaf ⟨(27, 17171317063680), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(27, 17172085080064), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record012_result⟩)
 (.branch 14
 (.leaf ⟨(27, 17189021679617), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record013_result⟩)
 (.leaf ⟨(27, 17189023256576), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(27, 17189130473728), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record015_result⟩)
 (.branch 17
 (.leaf ⟨(27, 17190078251009), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record016_result⟩)
 (.leaf ⟨(27, 17190147325952), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(27, 17198192034048), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record018_result⟩)
 (.branch 20
 (.leaf ⟨(27, 17198328381440), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record019_result⟩)
 (.leaf ⟨(27, 17198336704512), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(27, 17198468825088), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record021_result⟩)
 (.leaf ⟨(27, 17219874521088), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record022_result⟩))
 (.branch 24
 (.leaf ⟨(27, 17220411326464), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record023_result⟩)
 (.leaf ⟨(27, 17224572076032), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(27, 17228732825600), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record025_result⟩)
 (.branch 27
 (.leaf ⟨(27, 17232621010944), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record026_result⟩)
 (.leaf ⟨(27, 17232893575168), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(27, 17235741573120), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record028_result⟩)
 (.branch 30
 (.leaf ⟨(27, 17236509589504), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record029_result⟩)
 (.leaf ⟨(27, 17237054324736), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(27, 17244335636480), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record031_result⟩)
 (.branch 33
 (.leaf ⟨(27, 17292100370432), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record032_result⟩)
 (.leaf ⟨(27, 17300149305344), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(27, 17300933836800), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record034_result⟩)
 (.branch 36
 (.leaf ⟨(27, 17328448798720), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record035_result⟩)
 (.leaf ⟨(27, 17361742594048), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(27, 17429270888448), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record037_result⟩)
 (.branch 39
 (.leaf ⟨(27, 17455890071808), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record038_result⟩)
 (.leaf ⟨(27, 17458106793984), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(27, 17458379358208), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record040_result⟩)
 (.branch 42
 (.leaf ⟨(27, 17461227356160), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record041_result⟩)
 (.leaf ⟨(27, 17461995372544), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(27, 17464620482560), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record043_result⟩)
 (.branch 45
 (.leaf ⟨(27, 17466156122112), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record044_result⟩)
 (.leaf ⟨(27, 17469821419520), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(27, 17470349901824), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record046_result⟩)
 (.leaf ⟨(27, 17493422833664), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record047_result⟩))
 (.branch 49
 (.leaf ⟨(27, 17493695397888), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record048_result⟩)
 (.leaf ⟨(27, 17494207365120), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(27, 17498368114688), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record050_result⟩)
 (.branch 52
 (.leaf ⟨(27, 17519171731456), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record051_result⟩)
 (.leaf ⟨(27, 17523483640064), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(27, 17523752108032), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record053_result⟩)
 (.branch 55
 (.leaf ⟨(27, 17523760431104), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record054_result⟩)
 (.leaf ⟨(27, 17524272138240), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(27, 17532056635648), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record056_result⟩)
 (.branch 58
 (.leaf ⟨(27, 17532593506304), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record057_result⟩)
 (.leaf ⟨(27, 17532610150912), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(27, 17549236371972), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record059_result⟩)
 (.branch 61
 (.leaf ⟨(27, 17557847343104), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record060_result⟩)
 (.leaf ⟨(27, 17566441406464), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(27, 17566969888768), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record062_result⟩)
 (.branch 64
 (.leaf ⟨(27, 17583596240896), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record063_result⟩)
 (.leaf ⟨(27, 17583612887040), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(27, 17702995460096), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record065_result⟩)
 (.branch 67
 (.leaf ⟨(27, 17703127580672), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record066_result⟩)
 (.leaf ⟨(27, 17703263862784), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(27, 17856395968512), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record068_result⟩)
 (.branch 70
 (.leaf ⟨(27, 17856941031424), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record069_result⟩)
 (.leaf ⟨(27, 17857068990464), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(27, 17857077313536), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record071_result⟩)
 (.leaf ⟨(27, 17994107387904), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record072_result⟩))
 (.branch 74
 (.leaf ⟨(27, 17994111549440), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record073_result⟩)
 (.leaf ⟨(27, 17994571858048), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(27, 17998272299008), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record075_result⟩)
 (.branch 77
 (.leaf ⟨(27, 18180890714496), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record076_result⟩)
 (.leaf ⟨(27, 18246440943624), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(27, 18256975069184), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record078_result⟩)
 (.branch 80
 (.leaf ⟨(27, 18256979035392), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record079_result⟩)
 (.leaf ⟨(27, 18266374275072), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(27, 18271934054400), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record081_result⟩)
 (.branch 83
 (.leaf ⟨(27, 18272078528513), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record082_result⟩)
 (.leaf ⟨(27, 18336503037953), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(27, 18337039908864), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record084_result⟩)
 (.branch 86
 (.leaf ⟨(27, 18384750346248), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record085_result⟩)
 (.leaf ⟨(27, 18402487828480), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(27, 18406086673664), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record087_result⟩)
 (.branch 89
 (.leaf ⟨(27, 18406086738944), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record088_result⟩)
 (.leaf ⟨(27, 18406094930948), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(27, 18406359171588), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record090_result⟩)
 (.branch 92
 (.leaf ⟨(27, 18406359302145), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record091_result⟩)
 (.leaf ⟨(27, 18406900236288), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(27, 18411060985856), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record093_result⟩)
 (.branch 95
 (.leaf ⟨(27, 18411325227008), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record094_result⟩)
 (.leaf ⟨(27, 18481355456512), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(27, 18513567711232), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record096_result⟩)
 (.leaf ⟨(27, 18522606501888), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record097_result⟩))
 (.branch 99
 (.leaf ⟨(27, 18547959037952), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record098_result⟩)
 (.leaf ⟨(27, 18577992220672), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00007.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (18373 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 18373 18473 :=
  block_of_table results 18373 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0410
