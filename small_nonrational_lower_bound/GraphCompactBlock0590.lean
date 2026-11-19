module
prelude
import GraphInputsRow29Part00156Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0590
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 24896583778304), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00156.record000_result⟩)
 (.leaf ⟨(29, 24902255001856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00156.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 24964497572096), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00156.record002_result⟩)
 (.leaf ⟨(29, 24966716260352), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00156.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 25016188567808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00156.record004_result⟩)
 (.leaf ⟨(29, 25025030193152), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00156.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 25031270994048), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00156.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 25116985819392), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00156.record007_result⟩)
 (.leaf ⟨(29, 25117254287360), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00156.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 25117262610432), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00156.record009_result⟩)
 (.leaf ⟨(29, 25117522690048), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00156.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 25117774317568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00156.record011_result⟩)
 (.branch 13
 (.leaf ⟨(29, 25125558814976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00156.record012_result⟩)
 (.leaf ⟨(29, 25125852282880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00156.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(29, 25126095685632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00156.record014_result⟩)
 (.leaf ⟨(29, 25126112330240), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00156.record015_result⟩))
 (.branch 17
 (.leaf ⟨(29, 25134148749440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00156.record016_result⟩)
 (.branch 18
 (.leaf ⟨(29, 25142738551300), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00156.record017_result⟩)
 (.leaf ⟨(29, 25152471466240), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00156.record018_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22655 + i))) 0 19 :=
  interval_of_check _ 0 19 (by decide +kernel)

public theorem complete : Block 22655 22674 :=
  block_of_table results 22655 19 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0590
