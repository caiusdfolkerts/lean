module
prelude
import GraphInputsRow30Part00049Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0777
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 30241175375872), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record000_result⟩)
 (.leaf ⟨(30, 30241418907776), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 30241435422848), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record002_result⟩)
 (.leaf ⟨(30, 30241670303760), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(30, 30242240463616), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record004_result⟩)
 (.leaf ⟨(30, 30242508898944), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record005_result⟩))
 (.branch 7
 (.leaf ⟨(30, 30242743779856), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record006_result⟩)
 (.branch 8
 (.leaf ⟨(30, 30246537592832), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record007_result⟩)
 (.leaf ⟨(30, 30253917671552), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(30, 30254152552464), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record009_result⟩)
 (.leaf ⟨(30, 30255226028560), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record010_result⟩))
 (.branch 12
 (.leaf ⟨(30, 30305583108096), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record011_result⟩)
 (.leaf ⟨(30, 30314416179216), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(30, 30314432823824), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record013_result⟩)
 (.leaf ⟨(30, 30315363958784), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record014_result⟩))
 (.branch 16
 (.leaf ⟨(30, 30378589487104), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record015_result⟩)
 (.branch 17
 (.leaf ⟨(30, 30382615970048), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record016_result⟩)
 (.leaf ⟨(30, 30511603126272), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record017_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25121 + i))) 0 18 :=
  interval_of_check _ 0 18 (by decide +kernel)

public theorem complete : Block 25121 25139 :=
  block_of_table results 25121 18 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0777
