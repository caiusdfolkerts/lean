module
prelude
import GraphInputsRow29Part00141Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0575
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 24103375405056), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00141.record000_result⟩)
 (.leaf ⟨(29, 24103912210432), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00141.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 24104027815936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00141.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 24107651629056), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00141.record003_result⟩)
 (.leaf ⟨(29, 24192647987456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00141.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(29, 24195205439616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00141.record005_result⟩)
 (.leaf ⟨(29, 24199502504000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00141.record006_result⟩))
 (.branch 8
 (.leaf ⟨(29, 24225916682496), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00141.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 24229598756864), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00141.record008_result⟩)
 (.leaf ⟨(29, 24230729646336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00141.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22535 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 22535 22545 :=
  block_of_table results 22535 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0575
