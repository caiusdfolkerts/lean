module
prelude
import GraphInputsRow29Part00108Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0542
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 18526614126848), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00108.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 18527150997504), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00108.record001_result⟩)
 (.leaf ⟨(29, 18527159320576), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00108.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 18528777338880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00108.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 18530774876416), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00108.record004_result⟩)
 (.leaf ⟨(29, 18531039052544), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00108.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 18531047505920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00108.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 18531311747072), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00108.record007_result⟩)
 (.leaf ⟨(29, 18531320070144), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00108.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(29, 18539364778240), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00108.record009_result⟩)
 (.branch 11
 (.leaf ⟨(29, 18539901648896), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00108.record010_result⟩)
 (.leaf ⟨(29, 18540033769472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00108.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22070 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 22070 22082 :=
  block_of_table results 22070 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0542
