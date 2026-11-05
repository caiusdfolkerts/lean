module
prelude
import GraphInputsRow30Part00045Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0773
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 28973867221120), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00045.record000_result⟩)
 (.leaf ⟨(30, 28974051000320), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00045.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 28974137737216), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00045.record002_result⟩)
 (.leaf ⟨(30, 29038475509760), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00045.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(30, 29070572158976), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00045.record004_result⟩)
 (.leaf ⟨(30, 29140459749376), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00045.record005_result⟩))
 (.branch 7
 (.leaf ⟨(30, 29140694601728), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00045.record006_result⟩)
 (.branch 8
 (.leaf ⟨(30, 29141085208704), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00045.record007_result⟩)
 (.leaf ⟨(30, 29144306421888), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00045.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(30, 29146935726080), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00045.record009_result⟩)
 (.leaf ⟨(30, 29147027013632), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00045.record010_result⟩))
 (.branch 12
 (.leaf ⟨(30, 29147293302912), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00045.record011_result⟩)
 (.leaf ⟨(30, 29147295416320), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00045.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(30, 29176002838528), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00045.record013_result⟩)
 (.leaf ⟨(30, 29176007000064), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00045.record014_result⟩))
 (.branch 16
 (.leaf ⟨(30, 29176010641408), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00045.record015_result⟩)
 (.branch 17
 (.leaf ⟨(30, 29176518414464), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00045.record016_result⟩)
 (.leaf ⟨(30, 29177591890560), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00045.record017_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25053 + i))) 0 18 :=
  interval_of_check _ 0 18 (by decide +kernel)

public theorem complete : Block 25053 25071 :=
  block_of_table results 25053 18 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0773
