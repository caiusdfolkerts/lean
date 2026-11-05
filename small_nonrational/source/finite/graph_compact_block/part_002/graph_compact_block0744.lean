module
prelude
import GraphInputsRow30Part00016Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0744
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 8247973560320), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record000_result⟩)
 (.leaf ⟨(30, 8250926305536), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 8250926370816), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record002_result⟩)
 (.leaf ⟨(30, 8251190546688), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(30, 8251190611968), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record004_result⟩)
 (.leaf ⟨(30, 8251198410768), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record005_result⟩))
 (.branch 7
 (.leaf ⟨(30, 8251215185936), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record006_result⟩)
 (.branch 8
 (.leaf ⟨(30, 8252288925697), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record007_result⟩)
 (.leaf ⟨(30, 8263697434640), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(30, 8264073383936), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record009_result⟩)
 (.leaf ⟨(30, 8264077021200), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record010_result⟩))
 (.branch 12
 (.leaf ⟨(30, 8264093796368), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record011_result⟩)
 (.branch 13
 (.leaf ⟨(30, 8265167536129), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record012_result⟩)
 (.leaf ⟨(30, 8265171763200), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(30, 8315350552832), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record014_result⟩)
 (.leaf ⟨(30, 8324192012304), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record015_result⟩))
 (.branch 17
 (.leaf ⟨(30, 8324209180673), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record016_result⟩)
 (.branch 18
 (.leaf ⟨(30, 8324209246208), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record017_result⟩)
 (.leaf ⟨(30, 8325265752065), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record018_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24073 + i))) 0 19 :=
  interval_of_check _ 0 19 (by decide +kernel)

public theorem complete : Block 24073 24092 :=
  block_of_table results 24073 19 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0744
