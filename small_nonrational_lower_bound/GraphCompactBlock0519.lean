module
prelude
import GraphInputsRow29Part00085Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0519
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 14295019110432), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 14298240323616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record001_result⟩)
 (.leaf ⟨(29, 14298504564768), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 14299602886912), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 14303895757056), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record004_result⟩)
 (.leaf ⟨(29, 14311387336736), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 14346870620416), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 14372579713280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record007_result⟩)
 (.leaf ⟨(29, 14372579778560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 14372840734976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record009_result⟩)
 (.leaf ⟨(29, 14381442146304), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 14448834121760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record011_result⟩)
 (.leaf ⟨(29, 14449958191105), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record012_result⟩)))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf ⟨(29, 14449960304640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record013_result⟩)
 (.branch 15
 (.leaf ⟨(29, 14450027405312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record014_result⟩)
 (.leaf ⟨(29, 14450150097152), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record015_result⟩)))
 (.branch 18
 (.branch 17
 (.leaf ⟨(29, 14453370790144), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record016_result⟩)
 (.leaf ⟨(29, 14485584674816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record017_result⟩))
 (.branch 19
 (.leaf ⟨(29, 14487608360960), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record018_result⟩)
 (.leaf ⟨(29, 14522090848256), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record019_result⟩))))
 (.branch 23
 (.branch 21
 (.leaf ⟨(29, 14571853086976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record020_result⟩)
 (.branch 22
 (.leaf ⟨(29, 14573390270496), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record021_result⟩)
 (.leaf ⟨(29, 14577683140640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(29, 14587392950273), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record023_result⟩)
 (.leaf ⟨(29, 14588460941440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record024_result⟩))
 (.branch 26
 (.leaf ⟨(29, 14604048564480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record025_result⟩)
 (.leaf ⟨(29, 14604052791296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00085.record026_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21688 + i))) 0 27 :=
  interval_of_check _ 0 27 (by decide +kernel)

public theorem complete : Block 21688 21715 :=
  block_of_table results 21688 27 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0519
