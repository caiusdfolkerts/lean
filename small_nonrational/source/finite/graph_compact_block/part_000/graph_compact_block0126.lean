module
prelude
import GraphInputsRow24Part00010Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0126
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 6791631011840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record000_result⟩)
 (.leaf ⟨(24, 6840299651072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 6866188894208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 6866453135360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record003_result⟩)
 (.leaf ⟨(24, 6912022249472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(24, 6929069932544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record005_result⟩)
 (.leaf ⟨(24, 6929662361728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record006_result⟩))
 (.branch 8
 (.leaf ⟨(24, 6929730535424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 6929734696960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record008_result⟩)
 (.leaf ⟨(24, 6933362802688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 6936483364864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record010_result⟩)
 (.leaf ⟨(24, 6936545263616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 6936549425152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record012_result⟩)
 (.branch 14
 (.leaf ⟨(24, 6968691458048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record013_result⟩)
 (.leaf ⟨(24, 6968695619584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(24, 6968757518336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record015_result⟩)
 (.leaf ⟨(24, 6968761679872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record016_result⟩))
 (.branch 18
 (.leaf ⟨(24, 6968889638912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record017_result⟩)
 (.branch 19
 (.leaf ⟨(24, 6969155928192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record018_result⟩)
 (.leaf ⟨(24, 6977337983232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record019_result⟩))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf ⟨(24, 6977338048512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record020_result⟩)
 (.leaf ⟨(24, 6977470169088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record021_result⟩))
 (.branch 23
 (.leaf ⟨(24, 6977734410240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record022_result⟩)
 (.branch 24
 (.leaf ⟨(24, 6977858046080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record023_result⟩)
 (.leaf ⟨(24, 6979616604160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record024_result⟩))))
 (.branch 27
 (.branch 26
 (.leaf ⟨(24, 6979669985536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record025_result⟩)
 (.leaf ⟨(24, 6979880845312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record026_result⟩))
 (.branch 28
 (.leaf ⟨(24, 6982287228929), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record027_result⟩)
 (.branch 29
 (.leaf ⟨(24, 6983830735104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record028_result⟩)
 (.leaf ⟨(24, 6984173715456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record029_result⟩)))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf ⟨(24, 6986447978497), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record030_result⟩)
 (.leaf ⟨(24, 6992420669568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record031_result⟩))
 (.branch 33
 (.leaf ⟨(24, 6998930228224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record032_result⟩)
 (.branch 34
 (.leaf ⟨(24, 6999454515840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record033_result⟩)
 (.leaf ⟨(24, 7003078557952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record034_result⟩))))
 (.branch 37
 (.branch 36
 (.leaf ⟨(24, 7003082784768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record035_result⟩)
 (.leaf ⟨(24, 7003086946304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record036_result⟩))
 (.branch 38
 (.leaf ⟨(24, 7003090977792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record037_result⟩)
 (.branch 39
 (.leaf ⟨(24, 7003481194624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record038_result⟩)
 (.leaf ⟨(24, 7003487339520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record039_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (8277 + i))) 0 40 :=
  interval_of_check _ 0 40 (by decide +kernel)

public theorem complete : Block 8277 8317 :=
  block_of_table results 8277 40 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0126
