module
prelude
import GraphInputsRow29Part00019Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0453
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 4334427308552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00019.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 4342488825856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00019.record001_result⟩)
 (.leaf ⟨(29, 4343025631232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00019.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 4346525810944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00019.record003_result⟩)
 (.leaf ⟨(29, 4346909884416), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00019.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 4347062681600), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00019.record005_result⟩)
 (.leaf ⟨(29, 4347066843136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00019.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(29, 4347178287104), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00019.record007_result⟩)
 (.leaf ⟨(29, 4355235315712), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00019.record008_result⟩))
 (.branch 10
 (.leaf ⟨(29, 4355904241664), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00019.record009_result⟩)
 (.leaf ⟨(29, 4359391805956), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00019.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(29, 4359668629504), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00019.record011_result⟩)
 (.leaf ⟨(29, 4359928807424), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00019.record012_result⟩))
 (.branch 14
 (.leaf ⟨(29, 4438121087232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00019.record013_result⟩)
 (.leaf ⟨(29, 4438385328384), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00019.record014_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20773 + i))) 0 15 :=
  interval_of_check _ 0 15 (by decide +kernel)

public theorem complete : Block 20773 20788 :=
  block_of_table results 20773 15 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0453
