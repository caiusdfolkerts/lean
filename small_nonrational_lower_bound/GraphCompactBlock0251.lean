module
prelude
import GraphInputsRow24Part00135Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0251
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 31579552677888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 31585207386368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record001_result⟩)
 (.leaf ⟨(24, 31585744257024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 31585752580096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record003_result⟩)
 (.leaf ⟨(24, 31585793802240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 31587337175296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record005_result⟩)
 (.leaf ⟨(24, 31593797288192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(24, 31594115301376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 31594338320384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record008_result⟩)
 (.leaf ⟨(24, 31594585006080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 31595927077120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record010_result⟩)
 (.leaf ⟨(24, 31596732219904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 31602369503488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record012_result⟩)
 (.leaf ⟨(24, 31604517044224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135.record013_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11706 + i))) 0 14 :=
  interval_of_check _ 0 14 (by decide +kernel)

public theorem complete : Block 11706 11720 :=
  block_of_table results 11706 14 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0251
