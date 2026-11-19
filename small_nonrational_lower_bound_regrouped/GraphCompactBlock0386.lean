module
prelude
import GraphInputsRow26Part00070Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0386
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 31785060728832), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record000_result⟩)
 (.leaf ⟨(26, 31785069051904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 31785308454912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record002_result⟩)
 (.branch 4
 (.leaf ⟨(26, 31787070816512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record003_result⟩)
 (.leaf ⟨(26, 31787339284480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(26, 31787347607552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record005_result⟩)
 (.leaf ⟨(26, 31787388829696), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record006_result⟩))
 (.branch 8
 (.leaf ⟨(26, 31787858534400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record007_result⟩)
 (.branch 9
 (.leaf ⟨(26, 31812822900736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record008_result⟩)
 (.leaf ⟨(26, 31812890001408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(26, 31819283071232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record010_result⟩)
 (.leaf ⟨(26, 31819353358336), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record011_result⟩))
 (.branch 13
 (.leaf ⟨(26, 31819361681408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record012_result⟩)
 (.branch 14
 (.leaf ⟨(26, 31819551539200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record013_result⟩)
 (.leaf ⟨(26, 31819559862272), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(26, 31819601084416), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record015_result⟩)
 (.leaf ⟨(26, 31820070789120), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record016_result⟩))
 (.branch 18
 (.leaf ⟨(26, 31825725497600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record017_result⟩)
 (.branch 19
 (.leaf ⟨(26, 31826262368256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record018_result⟩)
 (.leaf ⟨(26, 31826311913472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record019_result⟩))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf ⟨(26, 31827855286528), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record020_result⟩)
 (.leaf ⟨(26, 31828459127296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record021_result⟩))
 (.branch 23
 (.leaf ⟨(26, 31842887671840), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record022_result⟩)
 (.branch 24
 (.leaf ⟨(26, 31887070953504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record023_result⟩)
 (.leaf ⟨(26, 31887205154848), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record024_result⟩))))
 (.branch 27
 (.branch 26
 (.leaf ⟨(26, 31889171693824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record025_result⟩)
 (.leaf ⟨(26, 31890426368032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record026_result⟩))
 (.branch 28
 (.leaf ⟨(26, 31890690609184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record027_result⟩)
 (.branch 29
 (.leaf ⟨(26, 31891386278144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record028_result⟩)
 (.leaf ⟨(26, 31891482939424), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record029_result⟩)))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf ⟨(26, 31891751342112), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record030_result⟩)
 (.leaf ⟨(26, 31904435802176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record031_result⟩))
 (.branch 33
 (.leaf ⟨(26, 31922638569728), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record032_result⟩)
 (.branch 34
 (.leaf ⟨(26, 31922910662720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record033_result⟩)
 (.leaf ⟨(26, 31926237823232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record034_result⟩))))
 (.branch 37
 (.branch 36
 (.leaf ⟨(26, 31929349967936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record035_result⟩)
 (.leaf ⟨(26, 31994901692416), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record036_result⟩))
 (.branch 38
 (.leaf ⟨(26, 31995091550208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record037_result⟩)
 (.branch 39
 (.leaf ⟨(26, 32011536367616), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record038_result⟩)
 (.leaf ⟨(26, 32011808931840), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070.record039_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17334 + i))) 0 40 :=
  interval_of_check _ 0 40 (by decide +kernel)

public theorem complete : Block 17334 17374 :=
  block_of_table results 17334 40 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0386
