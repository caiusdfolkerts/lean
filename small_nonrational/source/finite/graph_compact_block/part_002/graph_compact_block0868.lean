module
prelude
import GraphInputsRow31Part00080Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0868
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 15680960233728), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00080.record000_result⟩)
 (.leaf ⟨(31, 15681731436544), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00080.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 15686363545728), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00080.record002_result⟩)
 (.leaf ⟨(31, 15686698041344), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00080.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 15689550168192), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00080.record004_result⟩)
 (.leaf ⟨(31, 15693845119104), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00080.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 15721866231808), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00080.record006_result⟩)
 (.leaf ⟨(31, 15723875434624), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00080.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(31, 15762530115712), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00080.record008_result⟩)
 (.leaf ⟨(31, 15851247894528), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00080.record009_result⟩))
 (.branch 11
 (.leaf ⟨(31, 15859305152512), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00080.record010_result⟩)
 (.leaf ⟨(31, 16381005267460), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00080.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(31, 16495931326720), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00080.record012_result⟩)
 (.leaf ⟨(31, 16496067674112), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00080.record013_result⟩))
 (.branch 15
 (.leaf ⟨(31, 16496075997184), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00080.record014_result⟩)
 (.leaf ⟨(31, 16496298885120), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00080.record015_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26108 + i))) 0 16 :=
  interval_of_check _ 0 16 (by decide +kernel)

public theorem complete : Block 26108 26124 :=
  block_of_table results 26108 16 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0868
