module
prelude
import GraphInputsRow30Part00046Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0774
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 29185108083216), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00046.record000_result⟩)
 (.leaf ⟨(30, 29276808155136), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00046.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 29276940275712), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00046.record002_result⟩)
 (.leaf ⟨(30, 29277198762112), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00046.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(30, 29277204516864), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00046.record004_result⟩)
 (.leaf ⟨(30, 29281744847376), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00046.record005_result⟩))
 (.branch 7
 (.leaf ⟨(30, 29283288617216), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00046.record006_result⟩)
 (.leaf ⟨(30, 29283643822080), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00046.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(30, 29291878551680), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00046.record008_result⟩)
 (.leaf ⟨(30, 29414369280128), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00046.record009_result⟩))
 (.branch 11
 (.leaf ⟨(30, 29414375034880), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00046.record010_result⟩)
 (.leaf ⟨(30, 29420814340096), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00046.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(30, 29515304927232), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00046.record012_result⟩)
 (.leaf ⟨(30, 29523873761280), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00046.record013_result⟩))
 (.branch 15
 (.leaf ⟨(30, 29550466580608), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00046.record014_result⟩)
 (.branch 16
 (.leaf ⟨(30, 29550534754304), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00046.record015_result⟩)
 (.leaf ⟨(30, 29550538915840), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00046.record016_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25071 + i))) 0 17 :=
  interval_of_check _ 0 17 (by decide +kernel)

public theorem complete : Block 25071 25088 :=
  block_of_table results 25071 17 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0774
