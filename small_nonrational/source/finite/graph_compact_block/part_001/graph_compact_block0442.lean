module
prelude
import GraphInputsRow29Part00008Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0442
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 2058094641664), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record000_result⟩)
 (.leaf ⟨(29, 2058103029760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 2067158597888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record002_result⟩)
 (.leaf ⟨(29, 2100394262784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 2100910391552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record004_result⟩)
 (.leaf ⟨(29, 2118094225408), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 2132606517504), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record006_result⟩)
 (.leaf ⟨(29, 2132614905856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(29, 2132854243584), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record008_result⟩)
 (.leaf ⟨(29, 2133007040768), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record009_result⟩))
 (.branch 11
 (.leaf ⟨(29, 2133011267584), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record010_result⟩)
 (.leaf ⟨(29, 2133122646272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(29, 2133134936064), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record012_result⟩)
 (.leaf ⟨(29, 2137551536896), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record013_result⟩))
 (.branch 15
 (.leaf ⟨(29, 2143792661248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record014_result⟩)
 (.branch 16
 (.leaf ⟨(29, 2147685269760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record015_result⟩)
 (.leaf ⟨(29, 2147697559552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00008.record016_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20613 + i))) 0 17 :=
  interval_of_check _ 0 17 (by decide +kernel)

public theorem complete : Block 20613 20630 :=
  block_of_table results 20613 17 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0442
