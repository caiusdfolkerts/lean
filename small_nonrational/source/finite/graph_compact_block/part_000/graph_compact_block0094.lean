module
prelude
import GraphInputsRow23Part00016Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0094
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(23, 25154960752640), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record000_result⟩)
 (.leaf ⟨(23, 25155357114368), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001_result⟩))
 (.branch 3
 (.leaf ⟨(23, 25158081314816), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record002_result⟩)
 (.leaf ⟨(23, 25161061433344), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(23, 25161598238720), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record004_result⟩)
 (.leaf ⟨(23, 25169919737856), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005_result⟩))
 (.branch 7
 (.leaf ⟨(23, 25177132908544), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record006_result⟩)
 (.branch 8
 (.leaf ⟨(23, 25178241236992), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record007_result⟩)
 (.leaf ⟨(23, 25178373357568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(23, 25190004228096), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record009_result⟩)
 (.leaf ⟨(23, 25190276792320), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record010_result⟩))
 (.branch 12
 (.leaf ⟨(23, 25190788759552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record011_result⟩)
 (.leaf ⟨(23, 25194297098240), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(23, 25194833903616), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record013_result⟩)
 (.leaf ⟨(23, 25194949509120), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record014_result⟩))
 (.branch 16
 (.leaf ⟨(23, 25198573322240), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record015_result⟩)
 (.branch 17
 (.leaf ⟨(23, 25211458174976), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record016_result⟩)
 (.leaf ⟨(23, 25215753125888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record017_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7073 + i))) 0 18 :=
  interval_of_check _ 0 18 (by decide +kernel)

public theorem complete : Block 7073 7091 :=
  block_of_table results 7073 18 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0094
