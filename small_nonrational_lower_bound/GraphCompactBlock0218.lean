module
prelude
import GraphInputsRow24Part00102Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0218
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 25702244040960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record000_result⟩)
 (.leaf ⟨(24, 25702252429312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 25702310101248), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record002_result⟩)
 (.leaf ⟨(24, 25702312247296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 25702318489600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record004_result⟩)
 (.leaf ⟨(24, 25702359646464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 25702369855488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record006_result⟩)
 (.leaf ⟨(24, 25702712754240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(24, 25702714851328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record008_result⟩)
 (.leaf ⟨(24, 25702762299456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record009_result⟩))
 (.branch 11
 (.leaf ⟨(24, 25702829400128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record010_result⟩)
 (.leaf ⟨(24, 25704976613952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(24, 25705480208640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record012_result⟩)
 (.leaf ⟨(24, 25705490417664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record013_result⟩))
 (.branch 15
 (.leaf ⟨(24, 25705531899904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record014_result⟩)
 (.branch 16
 (.leaf ⟨(24, 25705556477952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record015_result⟩)
 (.leaf ⟨(24, 25705933447232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record016_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10977 + i))) 0 17 :=
  interval_of_check _ 0 17 (by decide +kernel)

public theorem complete : Block 10977 10994 :=
  block_of_table results 10977 17 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0218
