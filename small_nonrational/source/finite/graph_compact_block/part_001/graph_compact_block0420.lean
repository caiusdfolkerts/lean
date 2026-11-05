module
prelude
import GraphInputsRow28Part00000Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0420
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(28, 3328262528), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record000_result⟩)
 (.branch 2
 (.leaf ⟨(28, 3394322816), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record001_result⟩)
 (.leaf ⟨(28, 39934034816), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(28, 40074576128), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record003_result⟩)
 (.branch 5
 (.leaf ⟨(28, 40343011456), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record004_result⟩)
 (.leaf ⟨(28, 44637962368), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(28, 47824584832), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record006_result⟩)
 (.branch 8
 (.leaf ⟨(28, 110067155072), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record007_result⟩)
 (.leaf ⟨(28, 110339588352), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(28, 110339653632), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record009_result⟩)
 (.branch 11
 (.leaf ⟨(28, 114227741440), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record010_result⟩)
 (.leaf ⟨(28, 114231935232), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(28, 114362105984), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record012_result⟩)
 (.branch 14
 (.leaf ⟨(28, 114500337920), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record013_result⟩)
 (.leaf ⟨(28, 114500403200), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(28, 114634539264), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record015_result⟩)
 (.branch 17
 (.leaf ⟨(28, 123090337792), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record016_result⟩)
 (.leaf ⟨(28, 129666916416), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(28, 144461348992), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record018_result⟩)
 (.branch 20
 (.leaf ⟨(28, 182949314816), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record019_result⟩)
 (.leaf ⟨(28, 183217717504), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(28, 183217782784), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record021_result⟩)
 (.leaf ⟨(28, 183219798272), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record022_result⟩))
 (.branch 24
 (.leaf ⟨(28, 185298092288), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record023_result⟩)
 (.leaf ⟨(28, 191539281920), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(28, 191541297408), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record025_result⟩)
 (.branch 27
 (.leaf ⟨(28, 191943950400), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record026_result⟩)
 (.leaf ⟨(28, 194091425856), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(28, 329246605440), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record028_result⟩)
 (.branch 30
 (.leaf ⟨(28, 661991292928), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record029_result⟩)
 (.leaf ⟨(28, 666537885696), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(28, 697473007616), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record031_result⟩)
 (.branch 33
 (.leaf ⟨(28, 705794506752), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record032_result⟩)
 (.leaf ⟨(28, 705796522240), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(28, 706062942208), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record034_result⟩)
 (.branch 36
 (.leaf ⟨(28, 706266275904), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record035_result⟩)
 (.leaf ⟨(28, 735123144704), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(28, 739298607104), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record037_result⟩)
 (.branch 39
 (.leaf ⟨(28, 743847231489), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record038_result⟩)
 (.leaf ⟨(28, 743847297024), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(28, 769605566720), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record040_result⟩)
 (.branch 42
 (.leaf ⟨(28, 778195468544), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record041_result⟩)
 (.leaf ⟨(28, 778206978048), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(28, 872293662720), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record043_result⟩)
 (.branch 45
 (.leaf ⟨(28, 881286217728), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record044_result⟩)
 (.leaf ⟨(28, 885581168640), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(28, 1187302613056), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record046_result⟩)
 (.leaf ⟨(28, 1247228805120), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record047_result⟩))
 (.branch 49
 (.leaf ⟨(28, 1255814545408), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record048_result⟩)
 (.leaf ⟨(28, 1255820771392), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(28, 1255887872064), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record050_result⟩)
 (.branch 52
 (.leaf ⟨(28, 1289050210304), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record051_result⟩)
 (.leaf ⟨(28, 1325681147904), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(28, 1327817064704), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record053_result⟩)
 (.branch 55
 (.leaf ⟨(28, 1422317846529), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record054_result⟩)
 (.leaf ⟨(28, 1430907813888), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(28, 1431042015232), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record056_result⟩)
 (.branch 58
 (.leaf ⟨(28, 1766045319168), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record057_result⟩)
 (.leaf ⟨(28, 1774631059456), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(28, 1774639382528), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record059_result⟩)
 (.branch 61
 (.leaf ⟨(28, 1843216318464), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record060_result⟩)
 (.leaf ⟨(28, 1873151199232), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(28, 1873172037632), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record062_result⟩)
 (.branch 64
 (.leaf ⟨(28, 1877706015488), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record063_result⟩)
 (.leaf ⟨(28, 1877714468864), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(28, 1882009436160), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record065_result⟩)
 (.branch 67
 (.leaf ⟨(28, 1903215837184), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record066_result⟩)
 (.leaf ⟨(28, 1911537336320), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(28, 1912074141696), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record068_result⟩)
 (.branch 70
 (.leaf ⟨(28, 1920395640832), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record069_result⟩)
 (.leaf ⟨(28, 1943082663936), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(28, 1943216865280), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record071_result⟩)
 (.leaf ⟨(28, 1971801096192), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record072_result⟩))
 (.branch 74
 (.leaf ⟨(28, 1972065337344), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record073_result⟩)
 (.leaf ⟨(28, 1972073660416), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(28, 2015149228032), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record075_result⟩)
 (.branch 77
 (.leaf ⟨(28, 2015157551104), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record076_result⟩)
 (.leaf ⟨(28, 2018703868160), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(28, 2019444195328), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record078_result⟩)
 (.branch 80
 (.leaf ⟨(28, 2019452518400), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record079_result⟩)
 (.leaf ⟨(28, 2040386355200), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(28, 2040923160576), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record081_result⟩)
 (.branch 83
 (.leaf ⟨(28, 2053132845056), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record082_result⟩)
 (.leaf ⟨(28, 2057566158848), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(28, 2058094641152), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record084_result⟩)
 (.branch 86
 (.leaf ⟨(28, 2088161574912), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record085_result⟩)
 (.leaf ⟨(28, 2132589740288), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(28, 2137023119360), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record087_result⟩)
 (.branch 89
 (.leaf ⟨(28, 2137559924736), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record088_result⟩)
 (.leaf ⟨(28, 2143801049088), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(28, 2149769609216), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record090_result⟩)
 (.branch 92
 (.leaf ⟨(28, 2418470355200), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record091_result⟩)
 (.leaf ⟨(28, 2521554812928), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(28, 2637916291136), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record093_result⟩)
 (.branch 95
 (.leaf ⟨(28, 2933873770496), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record094_result⟩)
 (.leaf ⟨(28, 3114660823040), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(28, 3118953693184), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record096_result⟩)
 (.leaf ⟨(28, 3208751611904), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record097_result⟩))
 (.branch 99
 (.leaf ⟨(28, 3240963866624), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record098_result⟩)
 (.leaf ⟨(28, 3415174348800), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00000.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (19304 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 19304 19404 :=
  block_of_table results 19304 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0420
