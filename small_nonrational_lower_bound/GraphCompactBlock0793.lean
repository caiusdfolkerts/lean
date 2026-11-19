module
prelude
import GraphInputsRow31Part00005Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0793
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 743847231489), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record000_result⟩)
 (.leaf ⟨(31, 743847297024), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 769605566720), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record002_result⟩)
 (.leaf ⟨(31, 778195468544), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 778206978048), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record004_result⟩)
 (.leaf ⟨(31, 843501830272), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 843503911040), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record006_result⟩)
 (.branch 8
 (.leaf ⟨(31, 872285274368), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record007_result⟩)
 (.leaf ⟨(31, 872293662720), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(31, 881277829376), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record009_result⟩)
 (.leaf ⟨(31, 881286184961), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record010_result⟩))
 (.branch 12
 (.leaf ⟨(31, 881286217728), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record011_result⟩)
 (.leaf ⟨(31, 885570699520), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(31, 885581168640), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record013_result⟩)
 (.leaf ⟨(31, 1187302613056), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record014_result⟩))
 (.branch 16
 (.leaf ⟨(31, 1247228739840), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record015_result⟩)
 (.branch 17
 (.leaf ⟨(31, 1247228805120), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record016_result⟩)
 (.leaf ⟨(31, 1255814480128), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00005.record017_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25496 + i))) 0 18 :=
  interval_of_check _ 0 18 (by decide +kernel)

public theorem complete : Block 25496 25514 :=
  block_of_table results 25496 18 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0793
