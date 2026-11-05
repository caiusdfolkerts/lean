module
prelude
import GraphInputsRow26Part00078Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0394
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 32822693724672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record000_result⟩)
 (.leaf ⟨(26, 32839319945732), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 32916646404352), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record002_result⟩)
 (.branch 4
 (.leaf ⟨(26, 32916713570304), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record003_result⟩)
 (.leaf ⟨(26, 32916721893376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(26, 32917183275008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record005_result⟩)
 (.leaf ⟨(26, 32917233600512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record006_result⟩))
 (.branch 8
 (.leaf ⟨(26, 32918776973568), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record007_result⟩)
 (.branch 9
 (.leaf ⟨(26, 32919313844224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record008_result⟩)
 (.leaf ⟨(26, 32919330488832), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(26, 32933809358880), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record010_result⟩)
 (.leaf ⟨(26, 32935956709892), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record011_result⟩))
 (.branch 13
 (.leaf ⟨(26, 33022146003200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record012_result⟩)
 (.branch 14
 (.leaf ⟨(26, 33025419182080), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record013_result⟩)
 (.leaf ⟨(26, 33058653217024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(26, 33063938621440), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record015_result⟩)
 (.leaf ⟨(26, 33064135696640), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record016_result⟩))
 (.branch 18
 (.leaf ⟨(26, 33098495492096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record017_result⟩)
 (.branch 19
 (.leaf ⟨(26, 33102730625024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record018_result⟩)
 (.leaf ⟨(26, 33126320455680), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078.record019_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17499 + i))) 0 20 :=
  interval_of_check _ 0 20 (by decide +kernel)

public theorem complete : Block 17499 17519 :=
  block_of_table results 17499 20 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0394
