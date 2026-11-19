module
prelude
import GraphInputsRow26Part00056Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0372
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 27122452201472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record000_result⟩)
 (.leaf ⟨(26, 27128710070272), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 27128714231808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record002_result⟩)
 (.branch 4
 (.leaf ⟨(26, 27130373275648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record003_result⟩)
 (.leaf ⟨(26, 27130377437184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(26, 27130381468672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record005_result⟩)
 (.branch 7
 (.leaf ⟨(26, 27130771685504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record006_result⟩)
 (.leaf ⟨(26, 27130777830400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(26, 27137014824960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record008_result⟩)
 (.branch 10
 (.leaf ⟨(26, 27194399129600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record009_result⟩)
 (.leaf ⟨(26, 27208961753088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(26, 27216247275648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record011_result⟩)
 (.leaf ⟨(26, 27216478486656), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record012_result⟩))
 (.branch 14
 (.leaf ⟨(26, 27224826740992), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record013_result⟩)
 (.branch 15
 (.leaf ⟨(26, 27233416675456), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record014_result⟩)
 (.leaf ⟨(26, 27248442753152), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(26, 27248905175168), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record016_result⟩)
 (.branch 18
 (.leaf ⟨(26, 27249978392704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record017_result⟩)
 (.leaf ⟨(26, 27267808002176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(26, 27267812196352), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record019_result⟩)
 (.branch 21
 (.leaf ⟨(26, 27267948348416), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record020_result⟩)
 (.leaf ⟨(26, 27274183327872), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record021_result⟩))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf ⟨(26, 27353054462080), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record022_result⟩)
 (.leaf ⟨(26, 27384804032640), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record023_result⟩))
 (.branch 25
 (.leaf ⟨(26, 27393637236992), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record024_result⟩)
 (.branch 26
 (.leaf ⟨(26, 27430212403200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record025_result⟩)
 (.leaf ⟨(26, 27527865270272), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record026_result⟩))))
 (.branch 30
 (.branch 28
 (.leaf ⟨(26, 27532026019840), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record027_result⟩)
 (.branch 29
 (.leaf ⟨(26, 27532160221184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record028_result⟩)
 (.leaf ⟨(26, 27602290999297), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record029_result⟩)))
 (.branch 31
 (.leaf ⟨(26, 27618051162112), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record030_result⟩)
 (.branch 32
 (.leaf ⟨(26, 27618059485184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record031_result⟩)
 (.leaf ⟨(26, 27636581535808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record032_result⟩)))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf ⟨(26, 27643689910272), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record033_result⟩)
 (.branch 35
 (.leaf ⟨(26, 27663494299648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record034_result⟩)
 (.leaf ⟨(26, 27663618031872), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record035_result⟩)))
 (.branch 37
 (.leaf ⟨(26, 27665172070400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record036_result⟩)
 (.branch 38
 (.leaf ⟨(26, 27665304190976), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record037_result⟩)
 (.leaf ⟨(26, 27665574674432), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record038_result⟩))))
 (.branch 42
 (.branch 40
 (.leaf ⟨(26, 27665764466944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record039_result⟩)
 (.branch 41
 (.leaf ⟨(26, 27669867544576), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record040_result⟩)
 (.leaf ⟨(26, 27672082120704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record041_result⟩)))
 (.branch 43
 (.leaf ⟨(26, 27678649368640), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record042_result⟩)
 (.branch 44
 (.leaf ⟨(26, 27681870061632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record043_result⟩)
 (.leaf ⟨(26, 27682351874048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00056.record044_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (16868 + i))) 0 45 :=
  interval_of_check _ 0 45 (by decide +kernel)

public theorem complete : Block 16868 16913 :=
  block_of_table results 16868 45 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0372
