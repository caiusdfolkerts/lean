module
prelude
import GraphInputsRow24Part00115Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0231
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 27817565913088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 27868186869760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115.record001_result⟩)
 (.leaf ⟨(24, 27874673574144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 27903536463872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115.record003_result⟩)
 (.leaf ⟨(24, 27903666438400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 27903732498688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115.record005_result⟩)
 (.leaf ⟨(24, 27915242766336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(24, 27915251089408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115.record007_result⟩)
 (.leaf ⟨(24, 27936772128768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115.record008_result⟩))
 (.branch 10
 (.leaf ⟨(24, 27936902103296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115.record009_result⟩)
 (.leaf ⟨(24, 27936910491648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(24, 27937017708800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115.record011_result⟩)
 (.leaf ⟨(24, 27938918563840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115.record012_result⟩))
 (.branch 14
 (.leaf ⟨(24, 27939048538368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115.record013_result⟩)
 (.leaf ⟨(24, 27939050684416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00115.record014_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11268 + i))) 0 15 :=
  interval_of_check _ 0 15 (by decide +kernel)

public theorem complete : Block 11268 11283 :=
  block_of_table results 11268 15 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0231
