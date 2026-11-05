module
prelude
import GraphInputsRow24Part00162Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0278
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 33206648700928), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00162.record000_result⟩)
 (.leaf ⟨(24, 33207111122944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00162.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 33228417466368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00162.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 33230448295936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00162.record003_result⟩)
 (.leaf ⟨(24, 33230456619008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00162.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(24, 33230497841152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00162.record005_result⟩)
 (.branch 7
 (.leaf ⟨(24, 33241436389376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00162.record006_result⟩)
 (.leaf ⟨(24, 33261385957504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00162.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(24, 33538634219520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00162.record008_result⟩)
 (.branch 10
 (.leaf ⟨(24, 33540780654592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00162.record009_result⟩)
 (.leaf ⟨(24, 33545073524736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00162.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (12003 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 12003 12014 :=
  block_of_table results 12003 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0278
