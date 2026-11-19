module
prelude
import GraphInputsRow29Part00012Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0446
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 3226195722240), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00012.record000_result⟩)
 (.leaf ⟨(29, 3232254459904), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00012.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 3236530553088), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00012.record002_result⟩)
 (.leaf ⟨(29, 3237067423744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00012.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 3237075746816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00012.record004_result⟩)
 (.leaf ⟨(29, 3238693765120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00012.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 3240691302656), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00012.record006_result⟩)
 (.leaf ⟨(29, 3240955478784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00012.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20688 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 20688 20696 :=
  block_of_table results 20688 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0446
