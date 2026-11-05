module
prelude
import GraphInputsRow30Part00008Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0736
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 6065781477632), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record000_result⟩)
 (.leaf ⟨(30, 6066141233152), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 6067324981264), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record002_result⟩)
 (.leaf ⟨(30, 6086531252480), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(30, 6086531317760), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record004_result⟩)
 (.leaf ⟨(30, 6086534893824), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005_result⟩))
 (.branch 7
 (.leaf ⟨(30, 6087587823872), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record006_result⟩)
 (.leaf ⟨(30, 6087587889152), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(30, 6099413504256), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record008_result⟩)
 (.leaf ⟨(30, 6099416170496), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record009_result⟩))
 (.branch 11
 (.leaf ⟨(30, 6099537233936), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record010_result⟩)
 (.leaf ⟨(30, 6100610973697), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(30, 6339585640464), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record012_result⟩)
 (.leaf ⟨(30, 6340659380225), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record013_result⟩))
 (.branch 15
 (.leaf ⟨(30, 6378844323840), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record014_result⟩)
 (.branch 16
 (.leaf ⟨(30, 6379100340480), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record015_result⟩)
 (.leaf ⟨(30, 6379368808448), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record016_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23880 + i))) 0 17 :=
  interval_of_check _ 0 17 (by decide +kernel)

public theorem complete : Block 23880 23897 :=
  block_of_table results 23880 17 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0736
