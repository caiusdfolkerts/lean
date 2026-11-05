module
prelude
import GraphInputsSix0Part00005Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0970
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 2032085860352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 2032337422592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record001_result⟩)
 (.leaf ⟨(32, 2035957334024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 2036091535368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 2036110262528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record004_result⟩)
 (.leaf ⟨(32, 2036374503680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 2036378665216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 2036378730496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record007_result⟩)
 (.leaf ⟨(32, 2036498172160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 2040919032064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 2040927420416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record010_result⟩)
 (.leaf ⟨(32, 2044677275656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 2044819671296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 2044964405504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record013_result⟩)
 (.leaf ⟨(32, 2044964470784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 2044968599680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 2044970680448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record016_result⟩)
 (.leaf ⟨(32, 2045088106624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 2049517289473), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 2053801804032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record019_result⟩)
 (.leaf ⟨(32, 2053812273152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 2057293661440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record021_result⟩)
 (.leaf ⟨(32, 2057293726720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 2057301918724), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record023_result⟩)
 (.leaf ⟨(32, 2057557967104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 2057562030336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 2057566159364), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record026_result⟩)
 (.leaf ⟨(32, 2057566289921), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 2057566355456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 2057826369792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record029_result⟩)
 (.leaf ⟨(32, 2057834758144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 2057838789632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 2058094641920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record032_result⟩)
 (.leaf ⟨(32, 2058098900992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 2058107224064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 2065487134976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record035_result⟩)
 (.leaf ⟨(32, 2067567509760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 2068607697152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 2100803174656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record038_result⟩)
 (.leaf ⟨(32, 2109240049920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 2109504291072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 2109512679424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record041_result⟩)
 (.leaf ⟨(32, 2109636411648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 2113805486208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 2118226313472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record044_result⟩)
 (.leaf ⟨(32, 2118236782592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 2122521264384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record046_result⟩)
 (.leaf ⟨(32, 2126147289344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 2126419918848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record048_result⟩)
 (.leaf ⟨(32, 2126684160000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 2126692483072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 2126816280576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record051_result⟩)
 (.leaf ⟨(32, 2126956724224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 2130390122752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 2130396365056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record054_result⟩)
 (.leaf ⟨(32, 2130398248968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 2130860670984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 2130863792136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record057_result⟩)
 (.leaf ⟨(32, 2132589873408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 2132594098184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 2132614906112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record060_result⟩)
 (.leaf ⟨(32, 2132996702216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 2133011267840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 2133015429376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record063_result⟩)
 (.leaf ⟨(32, 2133015494656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 2133134936320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 2134670248192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record066_result⟩)
 (.leaf ⟨(32, 2137555796224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 2137564184576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 2141452304640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record069_result⟩)
 (.leaf ⟨(32, 2141716545792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 2141724934144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record071_result⟩)
 (.leaf ⟨(32, 2141848666368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 2147553083400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record073_result⟩)
 (.leaf ⟨(32, 2147559325704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 2147697559808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 2148040474880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record076_result⟩)
 (.leaf ⟨(32, 2148040540160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 2148046749824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 2148098115712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record079_result⟩)
 (.leaf ⟨(32, 2150038044928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 2150046433280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 2150314803201), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record082_result⟩)
 (.leaf ⟨(32, 2150438568192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 2150449037312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 2156879954176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record085_result⟩)
 (.leaf ⟨(32, 2308960256256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 2309228691584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 2313253126400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record088_result⟩)
 (.leaf ⟨(32, 2313521561728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 2315399561472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 2315601936512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record091_result⟩)
 (.leaf ⟨(32, 2316403015936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 2382241022080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 2384321396864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record094_result⟩)
 (.leaf ⟨(32, 2384992436480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 2408610627840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record096_result⟩)
 (.leaf ⟨(32, 2408811929856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 2410757062912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record098_result⟩)
 (.leaf ⟨(32, 2410892304640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00005.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (27286 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 27286 27386 :=
  block_of_table results 27286 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0970
