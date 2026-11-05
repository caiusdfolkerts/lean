module
prelude
import GraphInputsRow30Part00001Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0729
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(30, 801695137792), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record000_result⟩)
 (.branch 2
 (.leaf ⟨(30, 805583257856), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record001_result⟩)
 (.leaf ⟨(30, 806120128512), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(30, 810408771840), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record003_result⟩)
 (.leaf ⟨(30, 814168998144), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record004_result⟩))
 (.branch 6
 (.leaf ⟨(30, 814705868800), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record005_result⟩)
 (.leaf ⟨(30, 814714191872), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(30, 818329747712), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record007_result⟩)
 (.branch 9
 (.leaf ⟨(30, 818602377216), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record008_result⟩)
 (.leaf ⟨(30, 818866618368), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(30, 818874941440), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record010_result⟩)
 (.leaf ⟨(30, 819139182592), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record011_result⟩))
 (.branch 13
 (.leaf ⟨(30, 872562130944), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record012_result⟩)
 (.leaf ⟨(30, 881286201472), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(30, 915645931648), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record014_result⟩)
 (.branch 16
 (.leaf ⟨(30, 938857267456), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record015_result⟩)
 (.leaf ⟨(30, 938865655808), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(30, 1003281776896), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record017_result⟩)
 (.leaf ⟨(30, 1003290165248), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record018_result⟩))
 (.branch 20
 (.leaf ⟨(30, 1003682300160), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record019_result⟩)
 (.leaf ⟨(30, 1007583035392), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record020_result⟩))))
 (.branch 24
 (.branch 22
 (.leaf ⟨(30, 1007843049728), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record021_result⟩)
 (.branch 23
 (.leaf ⟨(30, 1016168775680), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record022_result⟩)
 (.leaf ⟨(30, 1026566422784), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record023_result⟩)))
 (.branch 26
 (.branch 25
 (.leaf ⟨(30, 1026702770176), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record024_result⟩)
 (.leaf ⟨(30, 1026711093248), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record025_result⟩))
 (.branch 27
 (.leaf ⟨(30, 1026843213824), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record026_result⟩)
 (.leaf ⟨(30, 1042135679232), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001.record027_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23589 + i))) 0 28 :=
  interval_of_check _ 0 28 (by decide +kernel)

public theorem complete : Block 23589 23617 :=
  block_of_table results 23589 28 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0729
