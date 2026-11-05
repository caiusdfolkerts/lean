module
prelude
import GraphInputsRow24Part00040Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0156
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 17470349901824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record000_result⟩)
 (.leaf ⟨(24, 17489125736704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 17493422833664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 17493695397888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record003_result⟩)
 (.leaf ⟨(24, 17494207365120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(24, 17498368114688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record005_result⟩)
 (.branch 7
 (.leaf ⟨(24, 17501991927808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_result⟩)
 (.leaf ⟨(24, 17519171731456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(24, 17523483640064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record008_result⟩)
 (.branch 10
 (.leaf ⟨(24, 17523752108032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record009_result⟩)
 (.leaf ⟨(24, 17523760431104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9437 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 9437 9448 :=
  block_of_table results 9437 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0156
