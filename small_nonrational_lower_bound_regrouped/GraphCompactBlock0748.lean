module
prelude
import GraphInputsRow30Part00020Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0748
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(30, 10490067550209), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record000_result⟩)
 (.branch 2
 (.leaf ⟨(30, 10585242603776), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record001_result⟩)
 (.leaf ⟨(30, 10585506844928), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(30, 10601399058433), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record003_result⟩)
 (.leaf ⟨(30, 10639451881472), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record004_result⟩))
 (.branch 6
 (.leaf ⟨(30, 10781852696576), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record005_result⟩)
 (.leaf ⟨(30, 10782116937728), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(30, 10858841309184), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record007_result⟩)
 (.branch 9
 (.leaf ⟨(30, 10859097098240), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record008_result⟩)
 (.leaf ⟨(30, 10892192579584), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(30, 10892439980288), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record010_result⟩)
 (.leaf ⟨(30, 10896600598784), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record011_result⟩))
 (.branch 13
 (.leaf ⟨(30, 10896617243392), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record012_result⟩)
 (.leaf ⟨(30, 10896898260992), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(30, 10901191131136), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record014_result⟩)
 (.branch 16
 (.leaf ⟨(30, 10905735659520), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record015_result⟩)
 (.leaf ⟨(30, 10909619912704), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(30, 10909776871424), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record017_result⟩)
 (.leaf ⟨(30, 10909888315392), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record018_result⟩))
 (.branch 20
 (.leaf ⟨(30, 11040622383360), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record019_result⟩)
 (.leaf ⟨(30, 11238073499648), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record020_result⟩))))
 (.branch 24
 (.branch 22
 (.leaf ⟨(30, 11242894786560), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record021_result⟩)
 (.branch 23
 (.leaf ⟨(30, 11246774518528), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record022_result⟩)
 (.leaf ⟨(30, 11247055536128), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record023_result⟩)))
 (.branch 26
 (.branch 25
 (.leaf ⟨(30, 11283294326816), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record024_result⟩)
 (.leaf ⟨(30, 11380325384192), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record025_result⟩))
 (.branch 27
 (.leaf ⟨(30, 11384226054144), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record026_result⟩)
 (.leaf ⟨(30, 11384618254336), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00020.record027_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24168 + i))) 0 28 :=
  interval_of_check _ 0 28 (by decide +kernel)

public theorem complete : Block 24168 24196 :=
  block_of_table results 24168 28 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0748
