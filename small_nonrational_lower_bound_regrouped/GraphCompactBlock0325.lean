module
prelude
import GraphInputsRow26Part00009Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0325
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 6701781664000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record000_result⟩)
 (.leaf ⟨(26, 6727061962752), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 6727065928960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record002_result⟩)
 (.branch 4
 (.leaf ⟨(26, 6727206436865), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record003_result⟩)
 (.leaf ⟨(26, 6727607025664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(26, 6790396870656), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record005_result⟩)
 (.branch 7
 (.leaf ⟨(26, 6791486472192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record006_result⟩)
 (.leaf ⟨(26, 6791630946305), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(26, 6791631011840), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record008_result⟩)
 (.branch 10
 (.leaf ⟨(26, 6823698661632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record009_result⟩)
 (.leaf ⟨(26, 6837674279168), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(26, 6837682405384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record011_result⟩)
 (.leaf ⟨(26, 6838144827400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record012_result⟩))
 (.branch 14
 (.leaf ⟨(26, 6839878254600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record013_result⟩)
 (.branch 15
 (.leaf ⟨(26, 6841954404608), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record014_result⟩)
 (.leaf ⟨(26, 6854837239816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(26, 6866188894208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record016_result⟩)
 (.branch 18
 (.leaf ⟨(26, 6866453135360), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record017_result⟩)
 (.leaf ⟨(26, 6877489438976), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(26, 6910890254592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record019_result⟩)
 (.branch 21
 (.leaf ⟨(26, 6912022249472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record020_result⟩)
 (.leaf ⟨(26, 6920335491072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record021_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (14549 + i))) 0 22 :=
  interval_of_check _ 0 22 (by decide +kernel)

public theorem complete : Block 14549 14571 :=
  block_of_table results 14549 22 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0325
