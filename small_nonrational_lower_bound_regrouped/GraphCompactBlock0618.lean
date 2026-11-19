module
prelude
import GraphInputsRow29Part00184Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0618
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 26991254339712), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record000_result⟩)
 (.leaf ⟨(29, 26992527818880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 27015638491136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 27015906861184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record003_result⟩)
 (.leaf ⟨(29, 27015910527008), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(29, 27016757838080), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record005_result⟩)
 (.branch 7
 (.leaf ⟨(29, 27016762032640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record006_result⟩)
 (.leaf ⟨(29, 27016766226432), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(29, 27016963432576), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record008_result⟩)
 (.branch 10
 (.leaf ⟨(29, 27017034596353), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record009_result⟩)
 (.leaf ⟨(29, 27080062935296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22896 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 22896 22907 :=
  block_of_table results 22896 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0618
