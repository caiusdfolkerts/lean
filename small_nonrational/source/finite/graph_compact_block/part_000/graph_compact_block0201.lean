module
prelude
import GraphInputsRow24Part00085Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0201
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 24578353005312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00085.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 24584462141568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00085.record001_result⟩)
 (.leaf ⟨(24, 24590835385472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00085.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 24590839579648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00085.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 24591103689220), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00085.record004_result⟩)
 (.leaf ⟨(24, 24604997353728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00085.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 24605001580544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00085.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 24605007822848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00085.record007_result⟩)
 (.leaf ⟨(24, 24605131555072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00085.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(24, 24605139943424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00085.record009_result⟩)
 (.branch 11
 (.leaf ⟨(24, 24605197615360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00085.record010_result⟩)
 (.leaf ⟨(24, 24605404184576), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00085.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(24, 24605600268352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00085.record012_result⟩)
 (.branch 14
 (.leaf ⟨(24, 24607286378496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00085.record013_result⟩)
 (.leaf ⟨(24, 24608221233152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00085.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(24, 24608318177536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00085.record015_result⟩)
 (.branch 17
 (.leaf ⟨(24, 24608326565888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00085.record016_result⟩)
 (.leaf ⟨(24, 24608590807040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00085.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(24, 24608820961344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00085.record018_result⟩)
 (.branch 20
 (.leaf ⟨(24, 24611841392704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00085.record019_result⟩)
 (.leaf ⟨(24, 24612981710912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00085.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(24, 24616639676672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00085.record021_result⟩)
 (.leaf ⟨(24, 24616707883008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00085.record022_result⟩))
 (.branch 24
 (.leaf ⟨(24, 24616716206080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00085.record023_result⟩)
 (.leaf ⟨(24, 24616815296512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00085.record024_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10665 + i))) 0 25 :=
  interval_of_check _ 0 25 (by decide +kernel)

public theorem complete : Block 10665 10690 :=
  block_of_table results 10665 25 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0201
