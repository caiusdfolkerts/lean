module
prelude
import GraphInputsRow31Part00160Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0948
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 31512451940352), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00160.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 31521310244864), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00160.record001_result⟩)
 (.leaf ⟨(31, 31525613601280), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00160.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(31, 31529631744000), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00160.record003_result⟩)
 (.leaf ⟨(31, 31530160226304), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00160.record004_result⟩))
 (.branch 6
 (.leaf ⟨(31, 31533650083840), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00160.record005_result⟩)
 (.leaf ⟨(31, 31568085123072), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00160.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26698 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 26698 26705 :=
  block_of_table results 26698 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0948
