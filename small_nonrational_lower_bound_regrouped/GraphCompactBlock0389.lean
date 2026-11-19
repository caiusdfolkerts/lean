module
prelude
import GraphInputsRow26Part00073Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0389
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 32333118048320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00073.record000_result⟩)
 (.leaf ⟨(26, 32335198292032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00073.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 32335214936640), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00073.record002_result⟩)
 (.branch 4
 (.leaf ⟨(26, 32438994665472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00073.record003_result⟩)
 (.leaf ⟨(26, 32439485890816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00073.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(26, 32439497920512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00073.record005_result⟩)
 (.branch 7
 (.leaf ⟨(26, 32441533235456), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00073.record006_result⟩)
 (.leaf ⟨(26, 32441537462272), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00073.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(26, 32441544744960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00073.record008_result⟩)
 (.branch 10
 (.leaf ⟨(26, 32441578295296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00073.record009_result⟩)
 (.leaf ⟨(26, 32441767567616), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00073.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(26, 32442841305344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00073.record011_result⟩)
 (.branch 13
 (.leaf ⟨(26, 32454060544000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00073.record012_result⟩)
 (.leaf ⟨(26, 32454423355392), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00073.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(26, 32457873690656), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00073.record014_result⟩)
 (.branch 16
 (.leaf ⟨(26, 32474541916160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00073.record015_result⟩)
 (.leaf ⟨(26, 32474806157312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00073.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(26, 32474813960192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00073.record017_result⟩)
 (.branch 19
 (.leaf ⟨(26, 32475053297920), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00073.record018_result⟩)
 (.leaf ⟨(26, 32476126774016), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00073.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(26, 32492232901136), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00073.record020_result⟩)
 (.branch 22
 (.leaf ⟨(26, 32507014185216), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00073.record021_result⟩)
 (.leaf ⟨(26, 32507026214912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00073.record022_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17418 + i))) 0 23 :=
  interval_of_check _ 0 23 (by decide +kernel)

public theorem complete : Block 17418 17441 :=
  block_of_table results 17418 23 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0389
