module
prelude
import GraphInputsRow27Part00012Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0415
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(27, 27248905175168), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record000_result⟩)
 (.branch 2
 (.leaf ⟨(27, 27267812196352), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record001_result⟩)
 (.leaf ⟨(27, 27353054462080), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(27, 27618059485184), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record003_result⟩)
 (.branch 5
 (.leaf ⟨(27, 27682351874048), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record004_result⟩)
 (.leaf ⟨(27, 27686644744192), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(27, 27687105085440), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record006_result⟩)
 (.branch 8
 (.leaf ⟨(27, 27689765306368), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record007_result⟩)
 (.leaf ⟨(27, 27690225647616), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(27, 27721977561088), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record009_result⟩)
 (.branch 11
 (.leaf ⟨(27, 27756368887808), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record010_result⟩)
 (.leaf ⟨(27, 27756763168768), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(27, 27783240646656), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record012_result⟩)
 (.branch 14
 (.leaf ⟨(27, 27814379128960), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record013_result⟩)
 (.leaf ⟨(27, 27915251089408), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(27, 27936910491648), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record015_result⟩)
 (.branch 17
 (.leaf ⟨(27, 27939050684416), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record016_result⟩)
 (.leaf ⟨(27, 27939056926720), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(27, 27943269042176), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record018_result⟩)
 (.branch 20
 (.leaf ⟨(27, 27943728586816), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record019_result⟩)
 (.leaf ⟨(27, 28076495437824), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(27, 28152046813184), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record021_result⟩)
 (.leaf ⟨(27, 28247609835520), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record022_result⟩))
 (.branch 24
 (.leaf ⟨(27, 28265985613824), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record023_result⟩)
 (.leaf ⟨(27, 28273804378112), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(27, 28273878761472), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record025_result⟩)
 (.branch 27
 (.leaf ⟨(27, 28274341183488), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record026_result⟩)
 (.leaf ⟨(27, 28308666449920), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(27, 28458564454400), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record028_result⟩)
 (.branch 30
 (.leaf ⟨(27, 28523164139520), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record029_result⟩)
 (.leaf ⟨(27, 28623963259008), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(27, 28636192194688), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record031_result⟩)
 (.branch 33
 (.leaf ⟨(27, 28644513693824), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record032_result⟩)
 (.leaf ⟨(27, 28716202737792), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(27, 28717294452736), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record034_result⟩)
 (.branch 36
 (.leaf ⟨(27, 28796163473536), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record035_result⟩)
 (.leaf ⟨(27, 28865508425856), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(27, 28865572405376), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record037_result⟩)
 (.branch 39
 (.leaf ⟨(27, 28865574486144), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record038_result⟩)
 (.leaf ⟨(27, 28865574518784), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(27, 28869799215232), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record040_result⟩)
 (.branch 42
 (.leaf ⟨(27, 28869803409408), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record041_result⟩)
 (.leaf ⟨(27, 28869999476864), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(27, 28874162339840), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record043_result⟩)
 (.branch 45
 (.leaf ⟨(27, 28901121736832), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record044_result⟩)
 (.leaf ⟨(27, 28901121769472), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(27, 28901122809856), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record046_result⟩)
 (.leaf ⟨(27, 28933333991552), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record047_result⟩))
 (.branch 49
 (.leaf ⟨(27, 28967545505792), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record048_result⟩)
 (.leaf ⟨(27, 28974120961032), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(27, 29038343227520), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record050_result⟩)
 (.branch 52
 (.leaf ⟨(27, 29068423872640), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record051_result⟩)
 (.leaf ⟨(27, 29139361431568), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(27, 29139493552144), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record053_result⟩)
 (.branch 55
 (.leaf ⟨(27, 29171573424144), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record054_result⟩)
 (.leaf ⟨(27, 29274790977552), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(27, 29276783183888), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record056_result⟩)
 (.branch 58
 (.leaf ⟨(27, 29412225736720), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record057_result⟩)
 (.leaf ⟨(27, 29414222104592), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(27, 29549426655360), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record059_result⟩)
 (.branch 61
 (.leaf ⟨(27, 29549426688000), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record060_result⟩)
 (.leaf ⟨(27, 29549428476032), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(27, 29549481953288), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record062_result⟩)
 (.branch 64
 (.leaf ⟨(27, 29550518077568), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record063_result⟩)
 (.leaf ⟨(27, 29550518110208), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(27, 29550522139656), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record065_result⟩)
 (.branch 67
 (.leaf ⟨(27, 29550538915841), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record066_result⟩)
 (.leaf ⟨(27, 29583753775104), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(27, 29583873280008), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record068_result⟩)
 (.branch 70
 (.leaf ⟨(27, 29583873410056), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record069_result⟩)
 (.leaf ⟨(27, 29583890186241), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(27, 29689115119744), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record071_result⟩)
 (.leaf ⟨(27, 29689131894912), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record072_result⟩))
 (.branch 74
 (.leaf ⟨(27, 29765500158208), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record073_result⟩)
 (.leaf ⟨(27, 29838783037440), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(27, 30030464813184), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record075_result⟩)
 (.branch 77
 (.leaf ⟨(27, 30031554414720), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record076_result⟩)
 (.leaf ⟨(27, 30031554447360), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(27, 30236725284880), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record078_result⟩)
 (.branch 80
 (.leaf ⟨(27, 30236725544976), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record079_result⟩)
 (.leaf ⟨(27, 30237782116368), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(27, 30305310410768), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record081_result⟩)
 (.branch 83
 (.leaf ⟨(27, 30309874204672), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record082_result⟩)
 (.leaf ⟨(27, 30448440836096), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(27, 30457802522624), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record084_result⟩)
 (.branch 86
 (.leaf ⟨(27, 30481676500992), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record085_result⟩)
 (.leaf ⟨(27, 30717606495240), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(27, 30717623271425), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record087_result⟩)
 (.branch 89
 (.leaf ⟨(27, 30787555627296), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record088_result⟩)
 (.leaf ⟨(27, 30789685416224), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(27, 30792005812256), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record090_result⟩)
 (.branch 92
 (.leaf ⟨(27, 30793079029792), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record091_result⟩)
 (.leaf ⟨(27, 30796300755008), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(27, 30796564996160), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record093_result⟩)
 (.branch 95
 (.leaf ⟨(27, 30820840837408), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record094_result⟩)
 (.leaf ⟨(27, 30824038662144), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(27, 30841726074880), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record096_result⟩)
 (.leaf ⟨(27, 30841730236416), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record097_result⟩))
 (.branch 99
 (.leaf ⟨(27, 30935115370560), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record098_result⟩)
 (.leaf ⟨(27, 30942222712832), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00012.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (18873 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 18873 18973 :=
  block_of_table results 18873 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0415
