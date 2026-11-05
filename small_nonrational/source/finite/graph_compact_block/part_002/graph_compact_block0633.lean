module
prelude
import GraphInputsRow29Part00199Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0633
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 28708704387200), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00199.record000_result⟩)
 (.leaf ⟨(29, 28717294321664), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00199.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 28717430603776), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00199.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 28729196159104), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00199.record003_result⟩)
 (.leaf ⟨(29, 28743199391744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00199.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(29, 28770243248128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00199.record005_result⟩)
 (.leaf ⟨(29, 28781855113216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00199.record006_result⟩))
 (.branch 8
 (.leaf ⟨(29, 28797288087552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00199.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 28830123229184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00199.record008_result⟩)
 (.leaf ⟨(29, 28830131552256), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00199.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22994 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 22994 23004 :=
  block_of_table results 22994 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0633
