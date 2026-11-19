module
prelude
import GraphInputsRow29Part00182Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0616
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 26466876137728), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record000_result⟩)
 (.leaf ⟨(29, 26467275653248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 26467275685888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 26467276693632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record003_result⟩)
 (.leaf ⟨(29, 26467345899552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(29, 26468315840640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record005_result⟩)
 (.branch 7
 (.leaf ⟨(29, 26468315873280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record006_result⟩)
 (.leaf ⟨(29, 26468316881024), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(29, 26468419637280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record008_result⟩)
 (.branch 10
 (.leaf ⟨(29, 26475667398688), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record009_result⟩)
 (.leaf ⟨(29, 26476741136416), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(29, 26498346156160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record011_result⟩)
 (.leaf ⟨(29, 26498618621953), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record012_result⟩))
 (.branch 14
 (.leaf ⟨(29, 26502779371521), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record013_result⟩)
 (.branch 15
 (.leaf ⟨(29, 26511100870657), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record014_result⟩)
 (.leaf ⟨(29, 26511291744384), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(29, 26532370743552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record016_result⟩)
 (.branch 18
 (.leaf ⟨(29, 26532370808832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record017_result⟩)
 (.leaf ⟨(29, 26532741390464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(29, 26535726694656), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record019_result⟩)
 (.branch 21
 (.leaf ⟨(29, 26544312434944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record020_result⟩)
 (.leaf ⟨(29, 26571228381184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record021_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22865 + i))) 0 22 :=
  interval_of_check _ 0 22 (by decide +kernel)

public theorem complete : Block 22865 22887 :=
  block_of_table results 22865 22 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0616
