module
prelude
import GraphInputsRow26Part00075Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0391
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 32676673486848), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00075.record000_result⟩)
 (.leaf ⟨(26, 32693828061184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00075.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 32712769962240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00075.record002_result⟩)
 (.leaf ⟨(26, 32712781991936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00075.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 32713178353664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00075.record004_result⟩)
 (.leaf ⟨(26, 32715051639040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00075.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 32715060547584), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00075.record006_result⟩)
 (.leaf ⟨(26, 32715324788736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00075.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(26, 32716142739456), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00075.record008_result⟩)
 (.leaf ⟨(26, 32717718684176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00075.record009_result⟩))
 (.branch 11
 (.leaf ⟨(26, 32725001043968), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00075.record010_result⟩)
 (.leaf ⟨(26, 32728053714976), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00075.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(26, 32748190367744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00075.record012_result⟩)
 (.leaf ⟨(26, 32780282003712), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00075.record013_result⟩))
 (.branch 15
 (.leaf ⟨(26, 32780352290816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00075.record014_result⟩)
 (.branch 16
 (.leaf ⟨(26, 32780360613888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00075.record015_result⟩)
 (.leaf ⟨(26, 32780550471680), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00075.record016_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17459 + i))) 0 17 :=
  interval_of_check _ 0 17 (by decide +kernel)

public theorem complete : Block 17459 17476 :=
  block_of_table results 17459 17 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0391
