module
prelude
import GraphInputsRow23Part00013Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0091
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(23, 22030575501568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record000_result⟩)
 (.branch 2
 (.leaf ⟨(23, 22065974378752), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record001_result⟩)
 (.leaf ⟨(23, 22077820117120), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(23, 22100299645184), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record003_result⟩)
 (.branch 5
 (.leaf ⟨(23, 22100563788032), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record004_result⟩)
 (.leaf ⟨(23, 22100572176384), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(23, 22104724537600), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record006_result⟩)
 (.branch 8
 (.leaf ⟨(23, 22104732925952), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record007_result⟩)
 (.leaf ⟨(23, 22113046036736), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(23, 22113054425088), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record009_result⟩)
 (.branch 11
 (.leaf ⟨(23, 22113457029120), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record010_result⟩)
 (.leaf ⟨(23, 22115604504576), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(23, 22173450305536), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record012_result⟩)
 (.branch 14
 (.leaf ⟨(23, 22181771804672), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record013_result⟩)
 (.leaf ⟨(23, 22182042288128), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(23, 22313027272960), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record015_result⟩)
 (.branch 17
 (.leaf ⟨(23, 22313038782464), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record016_result⟩)
 (.leaf ⟨(23, 22319202337024), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(23, 22319206563840), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record018_result⟩)
 (.branch 20
 (.leaf ⟨(23, 22319212806144), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record019_result⟩)
 (.leaf ⟨(23, 22558822899840), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(23, 22618979762432), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record021_result⟩)
 (.leaf ⟨(23, 22618988150784), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record022_result⟩))
 (.branch 24
 (.leaf ⟨(23, 22626450284672), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record023_result⟩)
 (.leaf ⟨(23, 22627767845120), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(23, 22627779354624), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record025_result⟩)
 (.branch 27
 (.leaf ⟨(23, 22687705530368), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record026_result⟩)
 (.leaf ⟨(23, 22696027029504), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(23, 22696287043840), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record028_result⟩)
 (.branch 30
 (.leaf ⟨(23, 22696291270656), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record029_result⟩)
 (.leaf ⟨(23, 22696297512960), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(23, 22696353104128), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record031_result⟩)
 (.branch 33
 (.leaf ⟨(23, 22696364613632), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record032_result⟩)
 (.leaf ⟨(23, 22731252891904), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(23, 22731921883136), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record034_result⟩)
 (.branch 36
 (.leaf ⟨(23, 22767693005056), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record035_result⟩)
 (.leaf ⟨(23, 22833461788672), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(23, 22833468030976), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record037_result⟩)
 (.branch 39
 (.leaf ⟨(23, 22833523622144), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record038_result⟩)
 (.leaf ⟨(23, 22833535131648), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(23, 22853122588672), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record040_result⟩)
 (.branch 42
 (.leaf ⟨(23, 22862786265088), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record041_result⟩)
 (.leaf ⟨(23, 22870302392320), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(23, 22997545058304), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record043_result⟩)
 (.branch 45
 (.leaf ⟨(23, 23006130798592), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record044_result⟩)
 (.leaf ⟨(23, 23006799724544), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(23, 23014724861952), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record046_result⟩)
 (.leaf ⟨(23, 23015253344256), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record047_result⟩))
 (.branch 49
 (.leaf ⟨(23, 23177389441280), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record048_result⟩)
 (.leaf ⟨(23, 23177400950784), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(23, 23199542739200), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record050_result⟩)
 (.branch 52
 (.leaf ⟨(23, 23200079609856), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record051_result⟩)
 (.leaf ⟨(23, 23204240359424), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(23, 23212289229056), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record053_result⟩)
 (.branch 55
 (.leaf ⟨(23, 23212826099712), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record054_result⟩)
 (.leaf ⟨(23, 23212834422784), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(23, 23212958220288), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record056_result⟩)
 (.branch 58
 (.leaf ⟨(23, 23246042841344), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record057_result⟩)
 (.leaf ⟨(23, 23246051213313), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(23, 23246051229696), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record059_result⟩)
 (.branch 61
 (.leaf ⟨(23, 23246118330368), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record060_result⟩)
 (.leaf ⟨(23, 23281543479296), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(23, 23281551802368), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record062_result⟩)
 (.branch 64
 (.leaf ⟨(23, 23337250127872), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record063_result⟩)
 (.leaf ⟨(23, 23349732376576), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(23, 23350269181952), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record065_result⟩)
 (.branch 67
 (.leaf ⟨(23, 23354429931520), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record066_result⟩)
 (.leaf ⟨(23, 23383288848384), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(23, 23383485988864), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record068_result⟩)
 (.branch 70
 (.leaf ⟨(23, 23418445529344), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record069_result⟩)
 (.leaf ⟨(23, 23418713997312), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(23, 23419116601344), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record071_result⟩)
 (.leaf ⟨(23, 23420525904128), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record072_result⟩))
 (.branch 74
 (.leaf ⟨(23, 23421263036416), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record073_result⟩)
 (.leaf ⟨(23, 23469987266816), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(23, 23474420645888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record075_result⟩)
 (.branch 77
 (.leaf ⟨(23, 23474957451264), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record076_result⟩)
 (.leaf ⟨(23, 23478581395456), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(23, 23479118200832), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record078_result⟩)
 (.branch 80
 (.leaf ⟨(23, 23487167135744), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record079_result⟩)
 (.leaf ⟨(23, 23487836061696), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(23, 23491600449536), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record081_result⟩)
 (.branch 83
 (.leaf ⟨(23, 23492128931840), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record082_result⟩)
 (.leaf ⟨(23, 23493540380672), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(23, 23495761199104), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record084_result⟩)
 (.branch 86
 (.leaf ⟨(23, 23496289681408), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record085_result⟩)
 (.leaf ⟨(23, 23543005904896), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(23, 23543542710272), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record087_result⟩)
 (.branch 89
 (.leaf ⟨(23, 23555884515328), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record088_result⟩)
 (.leaf ⟨(23, 23556421320704), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(23, 23557964890112), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record090_result⟩)
 (.branch 92
 (.leaf ⟨(23, 23590713950208), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record091_result⟩)
 (.leaf ⟨(23, 23679505334528), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(23, 23680042205184), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record093_result⟩)
 (.branch 95
 (.leaf ⟨(23, 23684202954752), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record094_result⟩)
 (.leaf ⟨(23, 23692251824384), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(23, 23692524453888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record096_result⟩)
 (.leaf ⟨(23, 23692788695040), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record097_result⟩))
 (.branch 99
 (.leaf ⟨(23, 23692797018112), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record098_result⟩)
 (.leaf ⟨(23, 23692920815616), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00013.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (6812 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 6812 6912 :=
  block_of_table results 6812 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0091
