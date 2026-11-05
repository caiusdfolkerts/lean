module
prelude
import GraphInputsRow29Part00025Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0459
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 6413204062208), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 6425556615424), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record001_result⟩)
 (.leaf ⟨(29, 6425565003776), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 6425825018112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 6425837307904), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record004_result⟩)
 (.leaf ⟨(29, 6426076645632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 6434398013696), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 6434406402048), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record007_result⟩)
 (.leaf ⟨(29, 6434414658304), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(29, 6442727901184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record009_result⟩)
 (.branch 11
 (.leaf ⟨(29, 6443017175040), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record010_result⟩)
 (.leaf ⟨(29, 6443256250888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20882 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 20882 20894 :=
  block_of_table results 20882 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0459
