module
prelude
import GraphInputsRow24Part00108Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0224
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 27128714231808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00108.record000_result⟩)
 (.leaf ⟨(24, 27129569935360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00108.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 27130369048832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00108.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 27130373275648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00108.record003_result⟩)
 (.leaf ⟨(24, 27130377437184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00108.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(24, 27130381468672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00108.record005_result⟩)
 (.leaf ⟨(24, 27130771685504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00108.record006_result⟩))
 (.branch 8
 (.leaf ⟨(24, 27130777830400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00108.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 27130905756288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00108.record008_result⟩)
 (.leaf ⟨(24, 27137014824960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00108.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11128 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 11128 11138 :=
  block_of_table results 11128 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0224
