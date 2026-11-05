module
prelude
import GraphInputsSix0Part00066Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1031
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 24742547439872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 24742648090880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record001_result⟩)
 (.leaf ⟨(32, 24743050743872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 24743415976064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 24746271969296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record004_result⟩)
 (.leaf ⟨(32, 24748889215232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 24748980502784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 24748986745088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record007_result⟩)
 (.leaf ⟨(32, 24748986810368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 24749021335808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 24749087396096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record010_result⟩)
 (.leaf ⟨(32, 24749248905472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 24749248970752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 24749250986240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record013_result⟩)
 (.leaf ⟨(32, 24749251051520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 24749258317888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 24749291868224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record016_result⟩)
 (.leaf ⟨(32, 24750432718864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 24757607076096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 24777956327680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record019_result⟩)
 (.leaf ⟨(32, 24777960489216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 24777960554496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record021_result⟩)
 (.leaf ⟨(32, 24777964130560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 24778484221968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record023_result⟩)
 (.leaf ⟨(32, 24779012899072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 24779017060608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 24779017125888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record026_result⟩)
 (.leaf ⟨(32, 24779146985728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 24779557961729), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 24782255440128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record029_result⟩)
 (.leaf ⟨(32, 24782255505408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 24782257000704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 24782519681280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record032_result⟩)
 (.leaf ⟨(32, 24782519746560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 24782521241856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 24782527533120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record035_result⟩)
 (.leaf ⟨(32, 24782644971536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 24783718711297), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 24786927911168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record038_result⟩)
 (.leaf ⟨(32, 24810172743936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 24813439615232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 24813906198784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record041_result⟩)
 (.leaf ⟨(32, 24814979416320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 24817600364800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 24818066948352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record044_result⟩)
 (.leaf ⟨(32, 24819140165888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 24826388447488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record046_result⟩)
 (.leaf ⟨(32, 24827461665024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 24848805986560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record048_result⟩)
 (.leaf ⟨(32, 24849342857216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 24849351180288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 24853503606784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record051_result⟩)
 (.leaf ⟨(32, 24855583981568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 24867929882880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 24878761644288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record054_result⟩)
 (.leaf ⟨(32, 24878893764864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 24879158006016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 24879164297280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record057_result⟩)
 (.leaf ⟨(32, 24883564675328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 24885597311232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 24885603082304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record060_result⟩)
 (.leaf ⟨(32, 24885603098624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 24885603602496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 24885654980624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record063_result⟩)
 (.leaf ⟨(32, 24886659653696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 24886659670016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 24886685745408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record066_result⟩)
 (.leaf ⟨(32, 24886728720385), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 24893844359184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 24893976479760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record069_result⟩)
 (.leaf ⟨(32, 24894042540048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 24894918098945), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record071_result⟩)
 (.leaf ⟨(32, 24895050219521), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 24903865614336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record073_result⟩)
 (.leaf ⟨(32, 24950610133248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 24967790002176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 24968062566400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record076_result⟩)
 (.leaf ⟨(32, 24968524988416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 24986249134080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 25003428937728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record079_result⟩)
 (.leaf ⟨(32, 25003957420032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 25016328524032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 25020735193344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record082_result⟩)
 (.leaf ⟨(32, 25022767829248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 25022774120512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 25023856263424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record085_result⟩)
 (.leaf ⟨(32, 25092676452352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 25116985950464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 25116986015744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record088_result⟩)
 (.leaf ⟨(32, 25116989851904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 25116989917184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 25116994046080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record091_result⟩)
 (.leaf ⟨(32, 25116998108168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 25117245704200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 25117245834248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record094_result⟩)
 (.leaf ⟨(32, 25117258481664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 25117262610433), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record096_result⟩)
 (.leaf ⟨(32, 25117510075400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 25125827250432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record098_result⟩)
 (.leaf ⟨(32, 25125843895040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00066.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (33239 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 33239 33339 :=
  block_of_table results 33239 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1031
