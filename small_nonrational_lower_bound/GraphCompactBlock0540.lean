module
prelude
import GraphInputsRow29Part00106Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0540
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 18297980485888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00106.record000_result⟩)
 (.leaf ⟨(29, 18297980551168), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00106.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 18298316005504), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00106.record002_result⟩)
 (.leaf ⟨(29, 18319314845952), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00106.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 18327300800768), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00106.record004_result⟩)
 (.leaf ⟨(29, 18327309189120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00106.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 18333749510144), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00106.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 18336033275905), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00106.record007_result⟩)
 (.leaf ⟨(29, 18336494714880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00106.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 18336503037952), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00106.record009_result⟩)
 (.leaf ⟨(29, 18370381512960), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00106.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 18370393022464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00106.record011_result⟩)
 (.branch 13
 (.leaf ⟨(29, 18384762765568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00106.record012_result⟩)
 (.leaf ⟨(29, 18384771153920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00106.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(29, 18385278894336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00106.record014_result⟩)
 (.leaf ⟨(29, 18399841517824), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00106.record015_result⟩))
 (.branch 17
 (.leaf ⟨(29, 18402462728192), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00106.record016_result⟩)
 (.branch 18
 (.leaf ⟨(29, 18406082511104), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00106.record017_result⟩)
 (.leaf ⟨(29, 18406350979072), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00106.record018_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22044 + i))) 0 19 :=
  interval_of_check _ 0 19 (by decide +kernel)

public theorem complete : Block 22044 22063 :=
  block_of_table results 22044 19 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0540
