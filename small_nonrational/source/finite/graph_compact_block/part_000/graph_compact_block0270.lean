module
prelude
import GraphInputsRow24Part00154Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0270
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 32716142739456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00154.record000_result⟩)
 (.leaf ⟨(24, 32717718684176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00154.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 32725001043968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00154.record002_result⟩)
 (.leaf ⟨(24, 32728053714976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00154.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 32729127191072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00154.record004_result⟩)
 (.leaf ⟨(24, 32730200932880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00154.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 32748190367744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00154.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 32780282003712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00154.record007_result⟩)
 (.leaf ⟨(24, 32780352290816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00154.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11934 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 11934 11943 :=
  block_of_table results 11934 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0270
