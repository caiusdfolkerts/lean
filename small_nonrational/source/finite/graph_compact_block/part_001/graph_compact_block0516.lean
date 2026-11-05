module
prelude
import GraphInputsRow29Part00082Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0516
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 13281726070912), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record000_result⟩)
 (.leaf ⟨(29, 13281729192064), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 13281930518560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 13283004256288), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record003_result⟩)
 (.leaf ⟨(29, 13308501590272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(29, 13308501655552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record005_result⟩)
 (.branch 7
 (.leaf ⟨(29, 13308765733120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record006_result⟩)
 (.leaf ⟨(29, 13308774121472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(29, 13314961735808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record008_result⟩)
 (.branch 10
 (.leaf ⟨(29, 13314964856960), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record009_result⟩)
 (.leaf ⟨(29, 13317363990529), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(29, 13338600833280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record011_result⟩)
 (.branch 13
 (.leaf ⟨(29, 13338600898560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record012_result⟩)
 (.leaf ⟨(29, 13338603954432), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(29, 13340731007008), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record014_result⟩)
 (.branch 16
 (.leaf ⟨(29, 13342895849472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record015_result⟩)
 (.leaf ⟨(29, 13342896824576), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(29, 13350442377472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record017_result⟩)
 (.branch 19
 (.leaf ⟨(29, 13350445531264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record018_result⟩)
 (.leaf ⟨(29, 13350445563904), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(29, 13350446571648), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record020_result⟩)
 (.branch 22
 (.leaf ⟨(29, 13350515777568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record021_result⟩)
 (.leaf ⟨(29, 13351589515296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record022_result⟩))))))
 (.branch 35
 (.branch 29
 (.branch 26
 (.branch 24
 (.leaf ⟨(29, 13369765560576), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record023_result⟩)
 (.branch 25
 (.leaf ⟨(29, 13377221115904), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record024_result⟩)
 (.leaf ⟨(29, 13377359380480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record025_result⟩)))
 (.branch 27
 (.leaf ⟨(29, 13377483112704), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record026_result⟩)
 (.branch 28
 (.leaf ⟨(29, 13379629547776), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record027_result⟩)
 (.leaf ⟨(29, 13383678042368), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record028_result⟩))))
 (.branch 32
 (.branch 30
 (.leaf ⟨(29, 13383681196160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record029_result⟩)
 (.branch 31
 (.leaf ⟨(29, 13383681228800), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record030_result⟩)
 (.leaf ⟨(29, 13383682236544), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record031_result⟩)))
 (.branch 33
 (.leaf ⟨(29, 13385680879616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record032_result⟩)
 (.branch 34
 (.leaf ⟨(29, 13385871687936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record033_result⟩)
 (.leaf ⟨(29, 13385949249537), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record034_result⟩)))))
 (.branch 41
 (.branch 38
 (.branch 36
 (.leaf ⟨(29, 13388219449600), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record035_result⟩)
 (.branch 37
 (.leaf ⟨(29, 13388230959104), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record036_result⟩)
 (.leaf ⟨(29, 13426874130688), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record037_result⟩)))
 (.branch 39
 (.leaf ⟨(29, 13476277784608), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record038_result⟩)
 (.branch 40
 (.leaf ⟨(29, 13480438534176), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record039_result⟩)
 (.leaf ⟨(29, 13487686295584), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record040_result⟩))))
 (.branch 44
 (.branch 42
 (.leaf ⟨(29, 13487881330816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record041_result⟩)
 (.branch 43
 (.leaf ⟨(29, 13488760033312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record042_result⟩)
 (.leaf ⟨(29, 13523119767553), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record043_result⟩)))
 (.branch 45
 (.leaf ⟨(29, 13523310641280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record044_result⟩)
 (.branch 46
 (.leaf ⟨(29, 13660749594624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record045_result⟩)
 (.leaf ⟨(29, 13745263312928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00082.record046_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21620 + i))) 0 47 :=
  interval_of_check _ 0 47 (by decide +kernel)

public theorem complete : Block 21620 21667 :=
  block_of_table results 21620 47 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0516
