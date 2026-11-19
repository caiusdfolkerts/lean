module
prelude
import GraphInputsSix0Part00000Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0965
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 109735674240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 109867794816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record001_result⟩)
 (.leaf ⟨(32, 110205436288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 110339654016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 114426986880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record004_result⟩)
 (.leaf ⟨(32, 114498306432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 114500403584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 122819805568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record007_result⟩)
 (.leaf ⟨(32, 183217783168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 191539282304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 247174627584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record010_result⟩)
 (.leaf ⟨(32, 247306748160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 255764529408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 256028770560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record013_result⟩)
 (.leaf ⟨(32, 256165052672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 256165117952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 256293011712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record016_result⟩)
 (.leaf ⟨(32, 256301400064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 264354431232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 264354496512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record019_result⟩)
 (.leaf ⟨(32, 264482390272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 264486551808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record021_result⟩)
 (.leaf ⟨(32, 264486617088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 265015034112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record023_result⟩)
 (.leaf ⟨(32, 265019260928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 265027584000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 268647301376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record026_result⟩)
 (.leaf ⟨(32, 328974025088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 384741507328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 389036458240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record029_result⟩)
 (.leaf ⟨(32, 476945875200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 587750015360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 589698269568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record032_result⟩)
 (.leaf ⟨(32, 589830390144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 593991139712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 594125341056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record035_result⟩)
 (.leaf ⟨(32, 594389582208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 624460661120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 628753531264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record038_result⟩)
 (.leaf ⟨(32, 637339271552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 656471589120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 660095467776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record041_result⟩)
 (.leaf ⟨(32, 661169144064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 661169209344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 661991293312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record044_result⟩)
 (.leaf ⟨(32, 662844834048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 664256217344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record046_result⟩)
 (.leaf ⟨(32, 665061490944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 665329893632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record048_result⟩)
 (.leaf ⟨(32, 665329958912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 665589973248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 665598361600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record051_result⟩)
 (.leaf ⟨(32, 666537918720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 670574936448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 672846151808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record054_result⟩)
 (.leaf ⟨(32, 679422820416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 679892517120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 679892582400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record057_result⟩)
 (.leaf ⟨(32, 680020476160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 680024637696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 680024702976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record060_result⟩)
 (.leaf ⟨(32, 680553120000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 680557346816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 680565669888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record063_result⟩)
 (.leaf ⟨(32, 697069289856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 697203507520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 697473008000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record066_result⟩)
 (.leaf ⟨(32, 705652949376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 705655030144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 705789247808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record069_result⟩)
 (.leaf ⟨(32, 705790288192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 705794507136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record071_result⟩)
 (.leaf ⟨(32, 706058731904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 725188968704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record073_result⟩)
 (.leaf ⟨(32, 727137222912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 727269343488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 727533584640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record076_result⟩)
 (.leaf ⟨(32, 728309530880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 732973596928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 734047273216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record079_result⟩)
 (.leaf ⟨(32, 735053971712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 735123177728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 735727124736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record082_result⟩)
 (.leaf ⟨(32, 735859245312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 735991365888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 736127648000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record085_result⟩)
 (.leaf ⟨(32, 736127713280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 736255607040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 736263995392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record088_result⟩)
 (.leaf ⟨(32, 737295794432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 737304182784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 739294396800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record091_result⟩)
 (.leaf ⟨(32, 740418437376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 741563531392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 742364610816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record094_result⟩)
 (.leaf ⟨(32, 742368772352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 742368837632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record096_result⟩)
 (.leaf ⟨(32, 742897254656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 742901481472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record098_result⟩)
 (.leaf ⟨(32, 743847329856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00000.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26805 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 26805 26905 :=
  block_of_table results 26805 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0965
