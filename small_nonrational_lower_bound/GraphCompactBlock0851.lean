module
prelude
import GraphInputsRow31Part00063Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0851
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 12850563186944), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00063.record000_result⟩)
 (.leaf ⟨(31, 12876312150016), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00063.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 12920473813248), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00063.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 12932184342528), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00063.record003_result⟩)
 (.leaf ⟨(31, 12932952358912), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00063.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(31, 12937653682176), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00063.record005_result⟩)
 (.leaf ⟨(31, 12937922084864), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00063.record006_result⟩))
 (.branch 8
 (.leaf ⟨(31, 12940774244352), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00063.record007_result⟩)
 (.branch 9
 (.leaf ⟨(31, 12945067114496), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00063.record008_result⟩)
 (.leaf ⟨(31, 12988002107648), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00063.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25969 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 25969 25979 :=
  block_of_table results 25969 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0851
