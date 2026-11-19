module
prelude
import GraphInputsRow24Part00009Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0125
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 6379649631232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 6379918065664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record001_result⟩)
 (.leaf ⟨(24, 6425833472000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 6443268835328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 6447563800576), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record004_result⟩)
 (.leaf ⟨(24, 6451871350784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 6456149540864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 6487088824320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record007_result⟩)
 (.leaf ⟨(24, 6511854094336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(24, 6524592390144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record009_result⟩)
 (.branch 11
 (.leaf ⟨(24, 6524600713216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record010_result⟩)
 (.leaf ⟨(24, 6548361314304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(24, 6559027429376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record012_result⟩)
 (.branch 14
 (.leaf ⟨(24, 6637144342784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record013_result⟩)
 (.leaf ⟨(24, 6638555725840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(24, 6711570169856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record015_result⟩)
 (.branch 17
 (.leaf ⟨(24, 6727061897472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record016_result⟩)
 (.leaf ⟨(24, 6727061962752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(24, 6727206436865), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record018_result⟩)
 (.branch 20
 (.leaf ⟨(24, 6727607025664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record019_result⟩)
 (.leaf ⟨(24, 6790396870656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(24, 6791161192512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record021_result⟩)
 (.leaf ⟨(24, 6791486406912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record022_result⟩))
 (.branch 24
 (.leaf ⟨(24, 6791486472192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record023_result⟩)
 (.leaf ⟨(24, 6791630946305), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009.record024_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (8252 + i))) 0 25 :=
  interval_of_check _ 0 25 (by decide +kernel)

public theorem complete : Block 8252 8277 :=
  block_of_table results 8252 25 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0125
