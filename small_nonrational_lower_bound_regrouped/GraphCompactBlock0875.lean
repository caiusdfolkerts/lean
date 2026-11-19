module
prelude
import GraphInputsRow31Part00087Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0875
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 17630180245504), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00087.record000_result⟩)
 (.leaf ⟨(31, 17630182260992), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00087.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 17630584913984), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00087.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 17632128499712), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00087.record003_result⟩)
 (.leaf ⟨(31, 17632260620288), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00087.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(31, 17632262635776), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00087.record005_result⟩)
 (.branch 7
 (.leaf ⟨(31, 17632732389440), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00087.record006_result⟩)
 (.leaf ⟨(31, 17636555505920), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00087.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(31, 17636555571200), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00087.record008_result⟩)
 (.branch 10
 (.leaf ⟨(31, 17636819747072), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00087.record009_result⟩)
 (.leaf ⟨(31, 17636819812352), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00087.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26213 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 26213 26224 :=
  block_of_table results 26213 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0875
