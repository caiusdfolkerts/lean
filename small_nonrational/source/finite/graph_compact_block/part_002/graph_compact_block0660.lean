module
prelude
import GraphInputsRow29Part00226Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0660
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 30717606234120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record000_result⟩)
 (.leaf ⟨(29, 30717623011328), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 30717623271424), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 30787485868288), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record003_result⟩)
 (.leaf ⟨(29, 30787555106848), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(29, 30788628844576), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record005_result⟩)
 (.leaf ⟨(29, 30789649597184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record006_result⟩))
 (.branch 8
 (.leaf ⟨(29, 30789657985280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 30789658050560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record008_result⟩)
 (.leaf ⟨(29, 30789685415968), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00226.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23176 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 23176 23186 :=
  block_of_table results 23176 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0660
