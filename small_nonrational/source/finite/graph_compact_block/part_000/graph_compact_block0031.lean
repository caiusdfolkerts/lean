module
prelude
import GraphInputsRow16Part00031Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0031
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(16, 29392877322240), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record000_result⟩)
 (.branch 2
 (.leaf ⟨(16, 30275515977984), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record001_result⟩)
 (.leaf ⟨(16, 30276606558208), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(16, 30284217585920), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record003_result⟩)
 (.leaf ⟨(16, 30285291388928), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record004_result⟩))
 (.branch 6
 (.leaf ⟨(16, 30285332742144), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record005_result⟩)
 (.leaf ⟨(16, 30307728232704), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(16, 30308818812928), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record007_result⟩)
 (.branch 9
 (.leaf ⟨(16, 30310965248000), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record008_result⟩)
 (.leaf ⟨(16, 30315258118144), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(16, 30317503643648), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record010_result⟩)
 (.leaf ⟨(16, 30317544996864), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record011_result⟩))
 (.branch 13
 (.leaf ⟨(16, 30320624205824), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record012_result⟩)
 (.leaf ⟨(16, 30341014290432), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(16, 30344233943040), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record014_result⟩)
 (.branch 16
 (.leaf ⟨(16, 30348641833216), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record015_result⟩)
 (.leaf ⟨(16, 30349715309312), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(16, 30352819683328), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record017_result⟩)
 (.leaf ⟨(16, 30353876254720), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record018_result⟩))
 (.branch 20
 (.leaf ⟨(16, 30443892178944), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record019_result⟩)
 (.leaf ⟨(16, 30443958239232), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record020_result⟩))))
 (.branch 24
 (.branch 22
 (.leaf ⟨(16, 30445031456768), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record021_result⟩)
 (.branch 23
 (.leaf ⟨(16, 30447310012416), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record022_result⟩)
 (.leaf ⟨(16, 30447358972160), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record023_result⟩)))
 (.branch 26
 (.branch 25
 (.leaf ⟨(16, 30449456447488), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record024_result⟩)
 (.leaf ⟨(16, 30457794330624), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record025_result⟩))
 (.branch 27
 (.leaf ⟨(16, 30457802653696), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record026_result⟩)
 (.leaf ⟨(16, 30458297585664), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00031.record027_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (1766 + i))) 0 28 :=
  interval_of_check _ 0 28 (by decide +kernel)

public theorem complete : Block 1766 1794 :=
  block_of_table results 1766 28 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0031
