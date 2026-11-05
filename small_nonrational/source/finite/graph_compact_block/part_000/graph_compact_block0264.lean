module
prelude
import GraphInputsRow24Part00148Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0264
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 32441544744960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00148.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 32441566265600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00148.record001_result⟩)
 (.leaf ⟨(24, 32441578295296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00148.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 32441767567616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00148.record003_result⟩)
 (.leaf ⟨(24, 32442841305344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00148.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 32454048514304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00148.record005_result⟩)
 (.leaf ⟨(24, 32454060544000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00148.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(24, 32454249816320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00148.record007_result⟩)
 (.leaf ⟨(24, 32454423355392), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00148.record008_result⟩))
 (.branch 10
 (.leaf ⟨(24, 32454456905728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00148.record009_result⟩)
 (.leaf ⟨(24, 32455323554048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00148.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(24, 32457873690656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00148.record011_result⟩)
 (.leaf ⟨(24, 32473312461056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00148.record012_result⟩))
 (.branch 14
 (.leaf ⟨(24, 32474533527808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00148.record013_result⟩)
 (.leaf ⟨(24, 32474541916160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00148.record014_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11867 + i))) 0 15 :=
  interval_of_check _ 0 15 (by decide +kernel)

public theorem complete : Block 11867 11882 :=
  block_of_table results 11867 15 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0264
