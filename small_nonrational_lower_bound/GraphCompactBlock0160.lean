module
prelude
import GraphInputsRow24Part00044Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0160
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 18599769079808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record000_result⟩)
 (.leaf ⟨(24, 18616948883456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 18617477365760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record002_result⟩)
 (.leaf ⟨(24, 18618752467200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 18618888814592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record004_result⟩)
 (.leaf ⟨(24, 18618897137664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 18619020935168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record006_result⟩)
 (.leaf ⟨(24, 18619029258240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(24, 18619489599488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record008_result⟩)
 (.leaf ⟨(24, 18634321723648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record009_result⟩))
 (.branch 11
 (.leaf ⟨(24, 18634332192768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record010_result⟩)
 (.leaf ⟨(24, 18732040667264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(24, 18744522915968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record012_result⟩)
 (.leaf ⟨(24, 18778881605760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record013_result⟩))
 (.branch 15
 (.leaf ⟨(24, 18779083997216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record014_result⟩)
 (.leaf ⟨(24, 18805927510272), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(24, 18814517412096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record016_result⟩)
 (.leaf ⟨(24, 18814517477376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record017_result⟩))
 (.branch 19
 (.leaf ⟨(24, 18817531052288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record018_result⟩)
 (.leaf ⟨(24, 18817939963904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(24, 18847803457568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record020_result⟩)
 (.leaf ⟨(24, 18848000589888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record021_result⟩))
 (.branch 23
 (.leaf ⟨(24, 18883236872448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record022_result⟩)
 (.leaf ⟨(24, 18883236937728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(24, 18939333640448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record024_result⟩)
 (.leaf ⟨(24, 18939342028800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record025_result⟩))
 (.branch 27
 (.leaf ⟨(24, 18943626510592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record026_result⟩)
 (.leaf ⟨(24, 18943634898944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(24, 18947927769088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record028_result⟩)
 (.leaf ⟨(24, 18951956398080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record029_result⟩))
 (.branch 31
 (.leaf ⟨(24, 18952216412416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record030_result⟩)
 (.leaf ⟨(24, 18952226881536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00044.record031_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9567 + i))) 0 32 :=
  interval_of_check _ 0 32 (by decide +kernel)

public theorem complete : Block 9567 9599 :=
  block_of_table results 9567 32 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0160
