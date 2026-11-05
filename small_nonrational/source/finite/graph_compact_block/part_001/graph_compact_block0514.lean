module
prelude
import GraphInputsRow29Part00080Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0514
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 13142600059008), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 13151189860868), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record001_result⟩)
 (.leaf ⟨(29, 13197467812096), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 13197533872384), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 13197668073728), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record004_result⟩)
 (.leaf ⟨(29, 13197672235264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 13197673332768), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 13199815549184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record007_result⟩)
 (.leaf ⟨(29, 13199819767840), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(29, 13200888766720), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record009_result⟩)
 (.branch 11
 (.leaf ⟨(29, 13204114718752), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record010_result⟩)
 (.leaf ⟨(29, 13204376879136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21587 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 21587 21599 :=
  block_of_table results 21587 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0514
