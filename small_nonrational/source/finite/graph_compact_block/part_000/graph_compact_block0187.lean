module
prelude
import GraphInputsRow24Part00071Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0187
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 23505888362752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 23505896751104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record001_result⟩)
 (.leaf ⟨(24, 23505954423040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 23508043186176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record003_result⟩)
 (.leaf ⟨(24, 23508713799680), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 23509074985216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record005_result⟩)
 (.leaf ⟨(24, 23509083373568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(24, 23520919699520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 23522060017728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record008_result⟩)
 (.leaf ⟨(24, 23525717983488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 23525786189824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010_result⟩)
 (.leaf ⟨(24, 23525794512896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 23525893603328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record012_result⟩)
 (.leaf ⟨(24, 23526254854144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(24, 23538721423616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record014_result⟩)
 (.branch 16
 (.leaf ⟨(24, 23538729811968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record015_result⟩)
 (.leaf ⟨(24, 23539124027648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(24, 23539132416000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record017_result⟩)
 (.leaf ⟨(24, 23539239633152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record018_result⟩))
 (.branch 20
 (.leaf ⟨(24, 23539249842176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record019_result⟩)
 (.leaf ⟨(24, 23540917403904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record020_result⟩))))
 (.branch 24
 (.branch 22
 (.leaf ⟨(24, 23541270462720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record021_result⟩)
 (.branch 23
 (.leaf ⟨(24, 23541272608768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record022_result⟩)
 (.leaf ⟨(24, 23541278851072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record023_result⟩)))
 (.branch 26
 (.branch 25
 (.leaf ⟨(24, 23541330216960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record024_result⟩)
 (.leaf ⟨(24, 23543534322432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record025_result⟩))
 (.branch 27
 (.leaf ⟨(24, 23553802256640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record026_result⟩)
 (.leaf ⟨(24, 23553812465664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record027_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10371 + i))) 0 28 :=
  interval_of_check _ 0 28 (by decide +kernel)

public theorem complete : Block 10371 10399 :=
  block_of_table results 10371 28 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0187
