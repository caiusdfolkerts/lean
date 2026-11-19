module
prelude
import GraphInputsRow29Part00010Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0444
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 2934146400256), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00010.record000_result⟩)
 (.leaf ⟨(29, 2942860034304), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00010.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 2968439029760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00010.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 2974948556800), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00010.record003_result⟩)
 (.leaf ⟨(29, 2975072289024), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00010.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(29, 3034803343616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00010.record005_result⟩)
 (.leaf ⟨(29, 3080298987648), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00010.record006_result⟩))
 (.branch 8
 (.leaf ⟨(29, 3102382030848), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00010.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 3118952628352), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00010.record008_result⟩)
 (.leaf ⟨(29, 3135617695744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00010.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(29, 3140430659584), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00010.record010_result⟩)
 (.leaf ⟨(29, 3140438982656), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00010.record011_result⟩))
 (.branch 13
 (.leaf ⟨(29, 3149020561408), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00010.record012_result⟩)
 (.branch 14
 (.leaf ⟨(29, 3152644440320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00010.record013_result⟩)
 (.leaf ⟨(29, 3153313431552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00010.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(29, 3157073657856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00010.record015_result⟩)
 (.leaf ⟨(29, 3157610463232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00010.record016_result⟩))
 (.branch 18
 (.leaf ⟨(29, 3164726165504), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00010.record017_result⟩)
 (.branch 19
 (.leaf ⟨(29, 3166806540288), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00010.record018_result⟩)
 (.leaf ⟨(29, 3200042205184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00010.record019_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20660 + i))) 0 20 :=
  interval_of_check _ 0 20 (by decide +kernel)

public theorem complete : Block 20660 20680 :=
  block_of_table results 20660 20 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0444
