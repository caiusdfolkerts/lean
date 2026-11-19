module
prelude
import GraphInputsSix0Part00026Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0991
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 10087145947392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 10088486043648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record001_result⟩)
 (.leaf ⟨(32, 10088931753984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 10090025321728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 10090165829633), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record004_result⟩)
 (.leaf ⟨(32, 10090558030080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 10115331662080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 10120630124672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record007_result⟩)
 (.leaf ⟨(32, 10122237576448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 10122770284800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 10136215404800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record010_result⟩)
 (.leaf ⟨(32, 10136217288712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 10138413137928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 10138815741960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record013_result⟩)
 (.leaf ⟨(32, 10147667706112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 10153378365448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 10153865789568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record016_result⟩)
 (.leaf ⟨(32, 10156257607936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 10156268077056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 10164178583808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record019_result⟩)
 (.leaf ⟨(32, 10164451213312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 10164715454464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record021_result⟩)
 (.leaf ⟨(32, 10164723777536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 10164847575040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record023_result⟩)
 (.leaf ⟨(32, 10206006264064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 10206072324352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 10208472531200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record026_result⟩)
 (.leaf ⟨(32, 10208476692736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 10208476758016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 10208745128064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record029_result⟩)
 (.leaf ⟨(32, 10208747208832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 10209293017344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 10209424097536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record032_result⟩)
 (.leaf ⟨(32, 10209425137920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 10209427218688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 10210424946944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record035_result⟩)
 (.leaf ⟨(32, 10210425012224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 10210552905984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 10210557067520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record038_result⟩)
 (.leaf ⟨(32, 10210557132800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 10210623127808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 10210623193088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record041_result⟩)
 (.leaf ⟨(32, 10210825502848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 10210827583616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 10211696345344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record044_result⟩)
 (.leaf ⟨(32, 10211696410624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 10211865690240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record046_result⟩)
 (.leaf ⟨(32, 10211867771008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 10214713655552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record048_result⟩)
 (.leaf ⟨(32, 10214717817088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 10214717882368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 10214852083712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record051_result⟩)
 (.leaf ⟨(32, 10214918144000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 10215120453760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 10215991361536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record054_result⟩)
 (.leaf ⟨(32, 10216160641152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 10218136207616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 10218138836992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record057_result⟩)
 (.leaf ⟨(32, 10218307076224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 10225648173312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 10225652400128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record060_result⟩)
 (.leaf ⟨(32, 10225656561664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 10225916608640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 10226185043968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record063_result⟩)
 (.leaf ⟨(32, 10226189205504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 10227728548096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 10227996983424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record066_result⟩)
 (.leaf ⟨(32, 10228265418752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 10228269580288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 10231897686016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record069_result⟩)
 (.leaf ⟨(32, 10232426168320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 10232430329856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record071_result⟩)
 (.leaf ⟨(32, 10235009859840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 10243039838336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record073_result⟩)
 (.leaf ⟨(32, 10249479143552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 10250519330944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 10267222114560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record076_result⟩)
 (.leaf ⟨(32, 10273650163968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 10276275503232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 10282714808448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record079_result⟩)
 (.leaf ⟨(32, 10291300548736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 10301613441280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 10301617668096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record082_result⟩)
 (.leaf ⟨(32, 10301621829632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 10301625861120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 10301757981696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record085_result⟩)
 (.leaf ⟨(32, 10301881713408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 10302016077952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 10302022222848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record088_result⟩)
 (.leaf ⟨(32, 10302150148736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 10331646624000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 10344590246144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record091_result⟩)
 (.leaf ⟨(32, 10345110308992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 10346736681216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 10347133042944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record094_result⟩)
 (.leaf ⟨(32, 10347190683776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 10349130612992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record096_result⟩)
 (.leaf ⟨(32, 10349139001344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 10353423483136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record098_result⟩)
 (.leaf ⟨(32, 10353431871488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00026.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (29386 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 29386 29486 :=
  block_of_table results 29386 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0991
