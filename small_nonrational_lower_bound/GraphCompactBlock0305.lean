module
prelude
import GraphInputsRow25Part00015Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0305
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 46
 (.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(25, 21600196378624), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record000_result⟩)
 (.leaf ⟨(25, 21603721167104), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record001_result⟩))
 (.branch 3
 (.leaf ⟨(25, 21668915315200), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record002_result⟩)
 (.branch 4
 (.leaf ⟨(25, 21672405123328), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record003_result⟩)
 (.leaf ⟨(25, 21728642793472), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(25, 21878563553344), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record005_result⟩)
 (.branch 7
 (.leaf ⟨(25, 21921531986176), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record006_result⟩)
 (.leaf ⟨(25, 21925829083136), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(25, 21926101647360), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record008_result⟩)
 (.branch 10
 (.leaf ⟨(25, 21926613614592), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record009_result⟩)
 (.leaf ⟨(25, 21930121953280), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(25, 21930658758656), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record011_result⟩)
 (.branch 13
 (.leaf ⟨(25, 21930774364160), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record012_result⟩)
 (.leaf ⟨(25, 21934398177280), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(25, 21947283030016), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record014_result⟩)
 (.branch 16
 (.leaf ⟨(25, 21951577980928), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record015_result⟩)
 (.leaf ⟨(25, 21994033741888), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(25, 22000476168256), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record017_result⟩)
 (.branch 19
 (.leaf ⟨(25, 22100572176384), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record018_result⟩)
 (.leaf ⟨(25, 22319212806144), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(25, 22618988150784), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record020_result⟩)
 (.branch 22
 (.leaf ⟨(25, 22627779354624), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record021_result⟩)
 (.leaf ⟨(25, 22635283489024), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record022_result⟩))))))
 (.branch 34
 (.branch 28
 (.branch 25
 (.branch 24
 (.leaf ⟨(25, 22696297512960), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record023_result⟩)
 (.leaf ⟨(25, 22731921883136), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record024_result⟩))
 (.branch 26
 (.leaf ⟨(25, 22870302392320), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record025_result⟩)
 (.branch 27
 (.leaf ⟨(25, 22997545058304), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record026_result⟩)
 (.leaf ⟨(25, 23006130798592), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record027_result⟩))))
 (.branch 31
 (.branch 29
 (.leaf ⟨(25, 23006799724544), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record028_result⟩)
 (.branch 30
 (.leaf ⟨(25, 23014724861952), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record029_result⟩)
 (.leaf ⟨(25, 23108580810816), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record030_result⟩)))
 (.branch 32
 (.leaf ⟨(25, 23177400950784), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record031_result⟩)
 (.branch 33
 (.leaf ⟨(25, 23177523642624), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record032_result⟩)
 (.leaf ⟨(25, 23212834422784), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record033_result⟩)))))
 (.branch 40
 (.branch 37
 (.branch 35
 (.leaf ⟨(25, 23212958220288), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record034_result⟩)
 (.branch 36
 (.leaf ⟨(25, 23218662473984), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record035_result⟩)
 (.leaf ⟨(25, 23419116601344), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record036_result⟩)))
 (.branch 38
 (.leaf ⟨(25, 23421263036416), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record037_result⟩)
 (.branch 39
 (.leaf ⟨(25, 23424820855040), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record038_result⟩)
 (.leaf ⟨(25, 23474957451264), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record039_result⟩))))
 (.branch 43
 (.branch 41
 (.leaf ⟨(25, 23487836061696), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record040_result⟩)
 (.branch 42
 (.leaf ⟨(25, 23493540380672), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record041_result⟩)
 (.leaf ⟨(25, 23495761199104), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record042_result⟩)))
 (.branch 44
 (.leaf ⟨(25, 23496289681408), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record043_result⟩)
 (.branch 45
 (.leaf ⟨(25, 23538704646400), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record044_result⟩)
 (.leaf ⟨(25, 23543005904896), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record045_result⟩)))))))
 (.branch 69
 (.branch 57
 (.branch 51
 (.branch 48
 (.branch 47
 (.leaf ⟨(25, 23543542710272), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record046_result⟩)
 (.leaf ⟨(25, 23555884515328), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record047_result⟩))
 (.branch 49
 (.leaf ⟨(25, 23556421320704), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record048_result⟩)
 (.branch 50
 (.leaf ⟨(25, 23557964890112), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record049_result⟩)
 (.leaf ⟨(25, 23590713950208), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record050_result⟩))))
 (.branch 54
 (.branch 52
 (.leaf ⟨(25, 23692797018112), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record051_result⟩)
 (.branch 53
 (.leaf ⟨(25, 23692920815616), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record052_result⟩)
 (.leaf ⟨(25, 23932845424640), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record053_result⟩)))
 (.branch 55
 (.leaf ⟨(25, 23933437886464), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record054_result⟩)
 (.branch 56
 (.leaf ⟨(25, 23934511104000), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record055_result⟩)
 (.leaf ⟨(25, 23972091527168), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record056_result⟩)))))
 (.branch 63
 (.branch 60
 (.branch 58
 (.leaf ⟨(25, 24035442556928), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record057_result⟩)
 (.branch 59
 (.leaf ⟨(25, 24055180754944), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record058_result⟩)
 (.leaf ⟨(25, 24055717560320), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record059_result⟩)))
 (.branch 61
 (.leaf ⟨(25, 24058838122496), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record060_result⟩)
 (.branch 62
 (.leaf ⟨(25, 24070139740160), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record061_result⟩)
 (.leaf ⟨(25, 24070676545536), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record062_result⟩))))
 (.branch 66
 (.branch 64
 (.leaf ⟨(25, 24091033600000), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record063_result⟩)
 (.branch 65
 (.leaf ⟨(25, 24103375405056), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record064_result⟩)
 (.leaf ⟨(25, 24103912210432), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record065_result⟩)))
 (.branch 67
 (.leaf ⟨(25, 24104027815936), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record066_result⟩)
 (.branch 68
 (.leaf ⟨(25, 24192647987456), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record067_result⟩)
 (.leaf ⟨(25, 24199502504000), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record068_result⟩))))))
 (.branch 80
 (.branch 74
 (.branch 71
 (.branch 70
 (.leaf ⟨(25, 24225916682496), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record069_result⟩)
 (.leaf ⟨(25, 24242081005568), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record070_result⟩))
 (.branch 72
 (.leaf ⟨(25, 24262832824448), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record071_result⟩)
 (.branch 73
 (.leaf ⟨(25, 24276439695360), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record072_result⟩)
 (.leaf ⟨(25, 24276644143104), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record073_result⟩))))
 (.branch 77
 (.branch 75
 (.leaf ⟨(25, 24293610389760), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record074_result⟩)
 (.branch 76
 (.leaf ⟨(25, 24299587043328), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record075_result⟩)
 (.leaf ⟨(25, 24299595366400), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record076_result⟩)))
 (.branch 78
 (.leaf ⟨(25, 24303756115968), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record077_result⟩)
 (.branch 79
 (.leaf ⟨(25, 24437030125568), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record078_result⟩)
 (.leaf ⟨(25, 24449908736000), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record079_result⟩)))))
 (.branch 86
 (.branch 83
 (.branch 81
 (.leaf ⟨(25, 24457833873408), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record080_result⟩)
 (.branch 82
 (.leaf ⟨(25, 24458362355712), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record081_result⟩)
 (.leaf ⟨(25, 24470778052864), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record082_result⟩)))
 (.branch 84
 (.leaf ⟨(25, 24477824458816), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record083_result⟩)
 (.branch 85
 (.leaf ⟨(25, 24482591834112), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record084_result⟩)
 (.leaf ⟨(25, 24504067751936), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record085_result⟩))))
 (.branch 89
 (.branch 87
 (.leaf ⟨(25, 24512184729600), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record086_result⟩)
 (.branch 88
 (.leaf ⟨(25, 24521247555584), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record087_result⟩)
 (.leaf ⟨(25, 24584594423808), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record088_result⟩)))
 (.branch 90
 (.leaf ⟨(25, 24591103819776), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record089_result⟩)
 (.branch 91
 (.leaf ⟨(25, 24642513338368), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record090_result⟩)
 (.leaf ⟨(25, 24642785902592), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00015.record091_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (13316 + i))) 0 92 :=
  interval_of_check _ 0 92 (by decide +kernel)

public theorem complete : Block 13316 13408 :=
  block_of_table results 13316 92 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0305
