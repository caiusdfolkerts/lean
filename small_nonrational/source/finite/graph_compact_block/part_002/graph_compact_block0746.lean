module
prelude
import GraphInputsRow30Part00018Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0746
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 10055202115616), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record000_result⟩)
 (.leaf ⟨(30, 10090165829632), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 10138830307328), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record002_result⟩)
 (.branch 4
 (.leaf ⟨(30, 10138941686016), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record003_result⟩)
 (.leaf ⟨(30, 10138953975808), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(30, 10208472530944), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record005_result⟩)
 (.leaf ⟨(30, 10214713655296), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record006_result⟩))
 (.branch 8
 (.leaf ⟨(30, 10218410868737), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record007_result⟩)
 (.branch 9
 (.leaf ⟨(30, 10276000825344), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record008_result⟩)
 (.leaf ⟨(30, 10293696561152), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(30, 10301617537024), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record010_result⟩)
 (.leaf ⟨(30, 10301890101248), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record011_result⟩))
 (.branch 13
 (.leaf ⟨(30, 10302154342400), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record012_result⟩)
 (.branch 14
 (.leaf ⟨(30, 10349399048192), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record013_result⟩)
 (.leaf ⟨(30, 10396574449664), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(30, 10448894198016), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record015_result⟩)
 (.leaf ⟨(30, 10448894263296), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record016_result⟩))
 (.branch 18
 (.leaf ⟨(30, 10448996929792), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record017_result⟩)
 (.branch 19
 (.leaf ⟨(30, 10455599890432), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record018_result⟩)
 (.leaf ⟨(30, 10456781557776), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018.record019_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24141 + i))) 0 20 :=
  interval_of_check _ 0 20 (by decide +kernel)

public theorem complete : Block 24141 24161 :=
  block_of_table results 24141 20 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0746
