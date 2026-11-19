module
prelude
import GraphInputsRow31Part00078Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0866
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 14587392950272), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00078.record000_result⟩)
 (.leaf ⟨(31, 14587454849024), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00078.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 14590809743360), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00078.record002_result⟩)
 (.leaf ⟨(31, 14606248509440), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00078.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 14616587403264), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00078.record004_result⟩)
 (.leaf ⟨(31, 14622354636800), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00078.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 14624363806976), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00078.record006_result⟩)
 (.branch 8
 (.leaf ⟨(31, 14625168949760), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00078.record007_result⟩)
 (.leaf ⟨(31, 14628797087744), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00078.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(31, 14629466013696), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00078.record009_result⟩)
 (.leaf ⟨(31, 14663018488064), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00078.record010_result⟩))
 (.branch 12
 (.leaf ⟨(31, 14663089717248), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00078.record011_result⟩)
 (.branch 13
 (.leaf ⟨(31, 14663824703488), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00078.record012_result⟩)
 (.leaf ⟨(31, 15213050986496), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00078.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(31, 15213579468800), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00078.record014_result⟩)
 (.leaf ⟨(31, 15403138949120), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00078.record015_result⟩))
 (.branch 17
 (.leaf ⟨(31, 15472352362496), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00078.record016_result⟩)
 (.branch 18
 (.leaf ⟨(31, 15480207212800), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00078.record017_result⟩)
 (.leaf ⟨(31, 15480942264320), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00078.record018_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26084 + i))) 0 19 :=
  interval_of_check _ 0 19 (by decide +kernel)

public theorem complete : Block 26084 26103 :=
  block_of_table results 26084 19 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0866
