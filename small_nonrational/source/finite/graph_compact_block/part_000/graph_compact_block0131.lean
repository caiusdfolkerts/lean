module
prelude
import GraphInputsRow24Part00015Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0131
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 9682536136832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record000_result⟩)
 (.leaf ⟨(24, 9682804572160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 9682808733696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002_result⟩)
 (.leaf ⟨(24, 9762003501184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 9768442806400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record004_result⟩)
 (.leaf ⟨(24, 9786185777408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 9795239166080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record006_result⟩)
 (.leaf ⟨(24, 9801678471296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(24, 9810264211584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record008_result⟩)
 (.leaf ⟨(24, 9820585492480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record009_result⟩))
 (.branch 11
 (.leaf ⟨(24, 9820589523968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record010_result⟩)
 (.leaf ⟨(24, 9820721644544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(24, 9820979740800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record012_result⟩)
 (.leaf ⟨(24, 9820985885696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record013_result⟩))
 (.branch 15
 (.leaf ⟨(24, 9821113811584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record014_result⟩)
 (.leaf ⟨(24, 10025600812288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(24, 10026133520640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record016_result⟩)
 (.leaf ⟨(24, 10041203687424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record017_result⟩))
 (.branch 19
 (.leaf ⟨(24, 10053615649024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record018_result⟩)
 (.leaf ⟨(24, 10122237576448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(24, 10156268077056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record020_result⟩)
 (.leaf ⟨(24, 10164723777536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record021_result⟩))
 (.branch 23
 (.leaf ⟨(24, 10164847575040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record022_result⟩)
 (.leaf ⟨(24, 10208476758016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(24, 10210425012224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record024_result⟩)
 (.leaf ⟨(24, 10210557132800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record025_result⟩))
 (.branch 27
 (.leaf ⟨(24, 10210623193088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record026_result⟩)
 (.leaf ⟨(24, 10210827583616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(24, 10211696410624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record028_result⟩)
 (.leaf ⟨(24, 10211867771008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record029_result⟩))
 (.branch 31
 (.leaf ⟨(24, 10214717882368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record030_result⟩)
 (.branch 32
 (.leaf ⟨(24, 10226185043968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031_result⟩)
 (.leaf ⟨(24, 10226189205504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record032_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (8597 + i))) 0 33 :=
  interval_of_check _ 0 33 (by decide +kernel)

public theorem complete : Block 8597 8630 :=
  block_of_table results 8597 33 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0131
