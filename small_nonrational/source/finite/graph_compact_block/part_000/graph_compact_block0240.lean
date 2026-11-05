module
prelude
import GraphInputsRow24Part00124Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0240
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 30310930776064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record000_result⟩)
 (.leaf ⟨(24, 30314282094848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 30315355570944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record002_result⟩)
 (.leaf ⟨(24, 30316429901824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 30349723697152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record004_result⟩)
 (.leaf ⟨(24, 30374164173056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 30446360461312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record006_result⟩)
 (.leaf ⟨(24, 30448440836096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(24, 30457802522624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record008_result⟩)
 (.leaf ⟨(24, 30458331004928), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record009_result⟩))
 (.branch 11
 (.leaf ⟨(24, 30481676500992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record010_result⟩)
 (.leaf ⟨(24, 30489973030912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(24, 30792001593600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record012_result⟩)
 (.leaf ⟨(24, 30792035143936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record013_result⟩))
 (.branch 15
 (.leaf ⟨(24, 30796300755008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record014_result⟩)
 (.branch 16
 (.leaf ⟨(24, 30796564996160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record015_result⟩)
 (.leaf ⟨(24, 30825270288640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record016_result⟩))))))
 (.branch 26
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ⟨(24, 30826268033024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record017_result⟩)
 (.leaf ⟨(24, 30826331021568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record018_result⟩))
 (.branch 20
 (.leaf ⟨(24, 30826395926784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record019_result⟩)
 (.leaf ⟨(24, 30826400088320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(24, 30826400153600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record021_result⟩)
 (.leaf ⟨(24, 30826469269760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record022_result⟩))
 (.branch 24
 (.leaf ⟨(24, 30829833691200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record023_result⟩)
 (.branch 25
 (.leaf ⟨(24, 30830693990656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record024_result⟩)
 (.leaf ⟨(24, 30839347880192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record025_result⟩)))))
 (.branch 30
 (.branch 28
 (.branch 27
 (.leaf ⟨(24, 30841726074880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record026_result⟩)
 (.leaf ⟨(24, 30841730236416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record027_result⟩))
 (.branch 29
 (.leaf ⟨(24, 30860754616576), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record028_result⟩)
 (.leaf ⟨(24, 30860758843392), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record029_result⟩)))
 (.branch 32
 (.branch 31
 (.leaf ⟨(24, 30860761899264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record030_result⟩)
 (.leaf ⟨(24, 30862305398816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record031_result⟩))
 (.branch 33
 (.leaf ⟨(24, 30864193429536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record032_result⟩)
 (.branch 34
 (.leaf ⟨(24, 30864915366144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record033_result⟩)
 (.leaf ⟨(24, 30864919527680), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00124.record034_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11500 + i))) 0 35 :=
  interval_of_check _ 0 35 (by decide +kernel)

public theorem complete : Block 11500 11535 :=
  block_of_table results 11500 35 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0240
