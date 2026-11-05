module
prelude
import GraphInputsSix0Part00018Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0983
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 7048201797888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 7048598159616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record001_result⟩)
 (.leaf ⟨(32, 7048655800448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 7050595729664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 7050604118016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record004_result⟩)
 (.leaf ⟨(32, 7050996252928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 7051006722048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 7054888599808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record007_result⟩)
 (.leaf ⟨(32, 7054896988160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 7055157002496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 7055167471616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record010_result⟩)
 (.leaf ⟨(32, 7055291203840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 7057437638912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 7061138049152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record013_result⟩)
 (.leaf ⟨(32, 7063478501632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 7063482728448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 7063488970752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record016_result⟩)
 (.leaf ⟨(32, 7070322540608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 7071800000768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 7072068468736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record019_result⟩)
 (.leaf ⟨(32, 7072076791808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 7072471072768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record021_result⟩)
 (.leaf ⟨(32, 7072605274112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 7073880375552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record023_result⟩)
 (.leaf ⟨(32, 7074016722944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 7074025046016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 7074148843520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record026_result⟩)
 (.leaf ⟨(32, 7074157166592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 7074617507840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 7080816689280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record029_result⟩)
 (.leaf ⟨(32, 7089181229312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 7089449632000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 7089460101120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record032_result⟩)
 (.leaf ⟨(32, 7147952898432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 7147954979200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 7147985928576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record035_result⟩)
 (.leaf ⟨(32, 7147988009344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 7148189327680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 7148193472896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record038_result⟩)
 (.leaf ⟨(32, 7148193489216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 7149128847744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 7149260968320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record041_result⟩)
 (.leaf ⟨(32, 7149263065408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 7149531468096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 7150227259648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record044_result⟩)
 (.leaf ⟨(32, 7150359380224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 7150623621376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record046_result⟩)
 (.leaf ⟨(32, 7150627815552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 7150730575888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record048_result⟩)
 (.leaf ⟨(32, 7152505815296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 7152770056448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 7152774250624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record051_result⟩)
 (.leaf ⟨(32, 7152810950672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 7155702370624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 7155709710432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record054_result⟩)
 (.leaf ⟨(32, 7155970756992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 7155970773312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 7155973951584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record057_result⟩)
 (.leaf ⟨(32, 7156800766208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 7157062926592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 7157065007360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record060_result⟩)
 (.leaf ⟨(32, 7157066047744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 7157069201536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 7157103820816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record063_result⟩)
 (.leaf ⟨(32, 7165293199376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 7165425319952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 7165491380240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record066_result⟩)
 (.leaf ⟨(32, 7165652861056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 7165654909184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 7165654941824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record069_result⟩)
 (.leaf ⟨(32, 7165655982208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 7185753114896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record071_result⟩)
 (.leaf ⟨(32, 7185757276432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 7185774510336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record073_result⟩)
 (.leaf ⟨(32, 7186042945664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 7186046615568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 7186826724100), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record076_result⟩)
 (.leaf ⟨(32, 7186826854657), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 7187099517056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 7187371950336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record079_result⟩)
 (.leaf ⟨(32, 7187372015616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 7190069461248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 7190337863936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record082_result⟩)
 (.leaf ⟨(32, 7190337896576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 7190339485712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 7191264297216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record085_result⟩)
 (.leaf ⟨(32, 7191394435328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 7191394467968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 7191532699904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record088_result⟩)
 (.leaf ⟨(32, 7191532765184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 7191666901248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 7194888114432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record091_result⟩)
 (.leaf ⟨(32, 7198925226000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 7198927798400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 7207773016128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record094_result⟩)
 (.leaf ⟨(32, 7217986765056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 7218258870288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record096_result⟩)
 (.leaf ⟨(32, 7224429191424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 7224697594112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record098_result⟩)
 (.leaf ⟨(32, 7224697626752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (28586 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 28586 28686 :=
  block_of_table results 28586 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0983
