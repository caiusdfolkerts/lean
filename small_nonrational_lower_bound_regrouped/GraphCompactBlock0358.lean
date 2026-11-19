module
prelude
import GraphInputsRow26Part00042Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0358
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 30
 (.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 23176206139424), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 23177062269184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record001_result⟩)
 (.leaf ⟨(26, 23211883380992), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(26, 23219736215808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record003_result⟩)
 (.leaf ⟨(26, 23220273086464), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record004_result⟩))
 (.branch 6
 (.leaf ⟨(26, 23220281409536), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record005_result⟩)
 (.leaf ⟨(26, 23234240057600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(26, 23245647593472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record007_result⟩)
 (.leaf ⟨(26, 23246050181184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record008_result⟩))
 (.branch 10
 (.leaf ⟨(26, 23246051221568), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record009_result⟩)
 (.leaf ⟨(26, 23247124959296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(26, 23267526115328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record011_result⟩)
 (.leaf ⟨(26, 23280402579712), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record012_result⟩))
 (.branch 14
 (.leaf ⟨(26, 23280410968064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record013_result⟩)
 (.leaf ⟨(26, 23280468640000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record014_result⟩)))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf ⟨(26, 23282625544192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 23284697595904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record016_result⟩)
 (.leaf ⟨(26, 23284705918976), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record017_result⟩)))
 (.branch 20
 (.branch 19
 (.leaf ⟨(26, 23314769657856), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record018_result⟩)
 (.leaf ⟨(26, 23332974034944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record019_result⟩))
 (.branch 21
 (.leaf ⟨(26, 23347996934400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record020_result⟩)
 (.leaf ⟨(26, 23347999080448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record021_result⟩))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf ⟨(26, 23348005322752), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record022_result⟩)
 (.leaf ⟨(26, 23348056688640), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record023_result⟩))
 (.branch 25
 (.leaf ⟨(26, 23350260794112), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record024_result⟩)
 (.leaf ⟨(26, 23350285959168), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record025_result⟩)))
 (.branch 28
 (.branch 27
 (.leaf ⟨(26, 23354421739520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record026_result⟩)
 (.leaf ⟨(26, 23354430062592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record027_result⟩))
 (.branch 29
 (.leaf ⟨(26, 23404564512768), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record028_result⟩)
 (.leaf ⟨(26, 23404696633344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record029_result⟩))))))
 (.branch 45
 (.branch 37
 (.branch 33
 (.branch 31
 (.leaf ⟨(26, 23404967116800), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record030_result⟩)
 (.branch 32
 (.leaf ⟨(26, 23405156909312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record031_result⟩)
 (.leaf ⟨(26, 23417639158016), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record032_result⟩)))
 (.branch 35
 (.branch 34
 (.leaf ⟨(26, 23417845727232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record033_result⟩)
 (.leaf ⟨(26, 23418041811008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record034_result⟩))
 (.branch 36
 (.leaf ⟨(26, 23419787739136), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record035_result⟩)
 (.leaf ⟨(26, 23419796062208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record036_result⟩))))
 (.branch 41
 (.branch 39
 (.branch 38
 (.leaf ⟨(26, 23420190343168), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record037_result⟩)
 (.leaf ⟨(26, 23420324544512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record038_result⟩))
 (.branch 40
 (.leaf ⟨(26, 23421599645952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record039_result⟩)
 (.leaf ⟨(26, 23421735993344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record040_result⟩)))
 (.branch 43
 (.branch 42
 (.leaf ⟨(26, 23421744316416), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record041_result⟩)
 (.leaf ⟨(26, 23421868113920), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record042_result⟩))
 (.branch 44
 (.leaf ⟨(26, 23421876436992), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record043_result⟩)
 (.leaf ⟨(26, 23422336778240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record044_result⟩)))))
 (.branch 52
 (.branch 48
 (.branch 46
 (.leaf ⟨(26, 23422404919296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record045_result⟩)
 (.branch 47
 (.leaf ⟨(26, 23425894596864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record046_result⟩)
 (.leaf ⟨(26, 23426028863488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record047_result⟩)))
 (.branch 50
 (.branch 49
 (.leaf ⟨(26, 23426037186560), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record048_result⟩)
 (.leaf ⟨(26, 23426431467520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record049_result⟩))
 (.branch 51
 (.leaf ⟨(26, 23426497527808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record050_result⟩)
 (.leaf ⟨(26, 23429081219328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record051_result⟩))))
 (.branch 56
 (.branch 54
 (.branch 53
 (.leaf ⟨(26, 23429149425664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record052_result⟩)
 (.leaf ⟨(26, 23429157748736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record053_result⟩))
 (.branch 55
 (.leaf ⟨(26, 23429618089984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record054_result⟩)
 (.leaf ⟨(26, 23437168902400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record055_result⟩)))
 (.branch 58
 (.branch 57
 (.leaf ⟨(26, 23437179371520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record056_result⟩)
 (.leaf ⟨(26, 23443618676736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record057_result⟩))
 (.branch 59
 (.leaf ⟨(26, 23451940175872), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record058_result⟩)
 (.leaf ⟨(26, 23461361680384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00042.record059_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (16247 + i))) 0 60 :=
  interval_of_check _ 0 60 (by decide +kernel)

public theorem complete : Block 16247 16307 :=
  block_of_table results 16247 60 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0358
