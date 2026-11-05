module
prelude
import GraphInputsSix0Part00012Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0977
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 5270608576768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 5270608642048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record001_result⟩)
 (.leaf ⟨(32, 5275910160512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 5277715793152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 5277847978240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record004_result⟩)
 (.leaf ⟨(32, 5277856366592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 5278116380928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 5278124769280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record007_result⟩)
 (.leaf ⟨(32, 5278248501504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 5283956917504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 5284489625856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record010_result⟩)
 (.leaf ⟨(32, 5378986229888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 5394571510016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 5394573393928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record013_result⟩)
 (.leaf ⟨(32, 5396769243144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 5397171847176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 5397186412800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record016_result⟩)
 (.leaf ⟨(32, 5397190574336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 5397190639616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 5397310081280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record019_result⟩)
 (.leaf ⟨(32, 5406023811328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 5411734470664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record021_result⟩)
 (.leaf ⟨(32, 5412221894784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 5414613713152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record023_result⟩)
 (.leaf ⟨(32, 5414624182272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 5422534689024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 5422807318528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record026_result⟩)
 (.leaf ⟨(32, 5423071559680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 5423079882752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 5423203680256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record029_result⟩)
 (.leaf ⟨(32, 5550786035840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 5572191789440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 5585214996512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record032_result⟩)
 (.leaf ⟨(32, 5602267988224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 5607897760000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 5612058509568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record035_result⟩)
 (.leaf ⟨(32, 5620648411392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 5620648476672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 5620782612736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record038_result⟩)
 (.leaf ⟨(32, 5644149662016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 5645206233408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 5645275316480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record041_result⟩)
 (.leaf ⟨(32, 5653861056768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 5653865267264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 5653932376096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record044_result⟩)
 (.leaf ⟨(32, 5680775889152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 5682787058436), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record046_result⟩)
 (.leaf ⟨(32, 5682856263936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 5687096721664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record048_result⟩)
 (.leaf ⟨(32, 5687100932160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 5689365790976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 5689365856256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record051_result⟩)
 (.leaf ⟨(32, 5689367871744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 5691513274624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 5745332519168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record054_result⟩)
 (.leaf ⟨(32, 5749493268736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 5753654018304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 5758079009024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record057_result⟩)
 (.leaf ⟨(32, 5758087397376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 5758211129600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 5761975517440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record060_result⟩)
 (.leaf ⟨(32, 5762512388096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 5766136267008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 5766673137664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record063_result⟩)
 (.leaf ⟨(32, 5780063420672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 5780162511104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 5790900502656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record066_result⟩)
 (.leaf ⟨(32, 5791102894112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 5791299977472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 5791300026432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record069_result⟩)
 (.leaf ⟨(32, 5793008091392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 5810698617088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record071_result⟩)
 (.leaf ⟨(32, 5812778991872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 5813819179264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record073_result⟩)
 (.leaf ⟨(32, 5820362293504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 5826538389760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 5826941042752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record076_result⟩)
 (.leaf ⟨(32, 5827333357824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 5827878486016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 5828324131072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record079_result⟩)
 (.leaf ⟨(32, 5828357161216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 5829088518208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 5829413732608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record082_result⟩)
 (.leaf ⟨(32, 5829413797888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 5829549949184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 5829558337536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record085_result⟩)
 (.leaf ⟨(32, 5829958860800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 5830086819840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 5830095142912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record088_result⟩)
 (.leaf ⟨(32, 5860569415936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 5875601604864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 5877805580296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record091_result⟩)
 (.leaf ⟨(32, 5877826388224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 5878226911488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 5882767278336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record094_result⟩)
 (.leaf ⟨(32, 5882775666688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 5886663786752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record096_result⟩)
 (.leaf ⟨(32, 5886928027904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 5886936416256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record098_result⟩)
 (.leaf ⟨(32, 5887060148480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00012.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (27986 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 27986 28086 :=
  block_of_table results 27986 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0977
