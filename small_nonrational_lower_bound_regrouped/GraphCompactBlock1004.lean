module
prelude
import GraphInputsSix0Part00039Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1004
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 15575241736192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 15576112103424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record001_result⟩)
 (.leaf ⟨(32, 15578250150144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 15584697843712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 15592142733312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record004_result⟩)
 (.leaf ⟨(32, 15613012484352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 15644556853504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 15644829483008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record007_result⟩)
 (.leaf ⟨(32, 15645093724160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 15645102047232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 15646637228288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record010_result⟩)
 (.leaf ⟨(32, 15647372279808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 15648990232576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 15649527037952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record013_result⟩)
 (.leaf ⟨(32, 15662009286656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 15664089661440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 15671375184000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record016_result⟩)
 (.leaf ⟨(32, 15671573364864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 15679954649344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 15679963037696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record019_result⟩)
 (.leaf ⟨(32, 15688544583808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 15703564386560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record021_result⟩)
 (.leaf ⟨(32, 15703564451840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 15703568580736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record023_result⟩)
 (.leaf ⟨(32, 15703570661504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 15703764713472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 15703768842368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record026_result⟩)
 (.leaf ⟨(32, 15703820208256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 15704033083520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 15711101520000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record029_result⟩)
 (.leaf ⟨(32, 15711277236224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 15711545606272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 15712410140673), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record032_result⟩)
 (.leaf ⟨(32, 15722935910528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 15722940104704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 15723070111872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record035_result⟩)
 (.leaf ⟨(32, 15723076256768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 15723204182656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 15729311236224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record038_result⟩)
 (.leaf ⟨(32, 15729317381120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 15806646730880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 15807719948416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record041_result⟩)
 (.leaf ⟨(32, 15808182370432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 15839927812096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 15839929567488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record044_result⟩)
 (.leaf ⟨(32, 15839931940992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 15839931973632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record046_result⟩)
 (.leaf ⟨(32, 15839933761664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 15840185419784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record048_result⟩)
 (.leaf ⟨(32, 15842125416704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 15842129610880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 15842265793544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record051_result⟩)
 (.leaf ⟨(32, 15842282569729), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 15842530034696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 15842546810881), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record054_result⟩)
 (.leaf ⟨(32, 15848765145344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 15853128056832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 15885340311552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record057_result⟩)
 (.leaf ⟨(32, 15987348930816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 15987357319168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 16021641560320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record060_result⟩)
 (.leaf ⟨(32, 16021649948672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 16090226819328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 16090235207680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record063_result⟩)
 (.leaf ⟨(32, 16090367328256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 16090425000192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 16090631569408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record066_result⟩)
 (.leaf ⟨(32, 16091498217728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 16094048297216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 16098953068544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record069_result⟩)
 (.leaf ⟨(32, 16125593190656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 16128407503616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record071_result⟩)
 (.leaf ⟨(32, 16158812078336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 16159357272064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record073_result⟩)
 (.leaf ⟨(32, 16159547129856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 16176264511488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 16365302906880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record076_result⟩)
 (.leaf ⟨(32, 16398588116992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 16432831201280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 16432880746496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record079_result⟩)
 (.leaf ⟨(32, 16492725559680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 16492726079872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 16492760699152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record082_result⟩)
 (.leaf ⟨(32, 16493799555968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 16493801734400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 16493803815168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record085_result⟩)
 (.leaf ⟨(32, 16493808009344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 16493817530640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 16493834764544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record088_result⟩)
 (.leaf ⟨(32, 16493836845312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 16493841006848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 16493841039488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record091_result⟩)
 (.leaf ⟨(32, 16493842628624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 16494042308864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 16494042890256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record094_result⟩)
 (.leaf ⟨(32, 16494305050640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 16494307131408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record096_result⟩)
 (.leaf ⟨(32, 16494310744192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 16494977683712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record098_result⟩)
 (.leaf ⟨(32, 16494981877888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00039.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (30686 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 30686 30786 :=
  block_of_table results 30686 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1004
