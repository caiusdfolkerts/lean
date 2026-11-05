module
prelude
import GraphInputsRow31Part00082Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0870
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 16532679753728), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00082.record000_result⟩)
 (.leaf ⟨(31, 16533208171008), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00082.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 16533216559104), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00082.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 16537377308672), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00082.record003_result⟩)
 (.leaf ⟨(31, 16539919192320), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00082.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(31, 16545426243584), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00082.record005_result⟩)
 (.leaf ⟨(31, 16545698807808), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00082.record006_result⟩))
 (.branch 8
 (.leaf ⟨(31, 16545963048960), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00082.record007_result⟩)
 (.branch 9
 (.leaf ⟨(31, 16548546805760), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00082.record008_result⟩)
 (.leaf ⟨(31, 16549314822144), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00082.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(31, 16604620455936), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00082.record010_result⟩)
 (.leaf ⟨(31, 16621523436036), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00082.record011_result⟩))
 (.branch 13
 (.leaf ⟨(31, 16621800259584), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00082.record012_result⟩)
 (.branch 14
 (.leaf ⟨(31, 16648576696320), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00082.record013_result⟩)
 (.leaf ⟨(31, 16650112335872), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00082.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(31, 16669044965376), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00082.record015_result⟩)
 (.branch 17
 (.leaf ⟨(31, 16677903269888), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00082.record016_result⟩)
 (.leaf ⟨(31, 16686224769024), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00082.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(31, 16686753251328), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00082.record018_result⟩)
 (.branch 20
 (.leaf ⟨(31, 16690385518592), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00082.record019_result⟩)
 (.leaf ⟨(31, 16768695304448), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00082.record020_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26132 + i))) 0 21 :=
  interval_of_check _ 0 21 (by decide +kernel)

public theorem complete : Block 26132 26153 :=
  block_of_table results 26132 21 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0870
