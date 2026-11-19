module
prelude
import GraphInputsRow26Part00050Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0366
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 24903865614336), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 24967790002176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record001_result⟩)
 (.leaf ⟨(26, 24968062566400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(26, 24968524988416), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record003_result⟩)
 (.branch 5
 (.leaf ⟨(26, 25003428937728), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record004_result⟩)
 (.leaf ⟨(26, 25003957420032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(26, 25016328524032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 25092676452352), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record007_result⟩)
 (.leaf ⟨(26, 25116989917184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(26, 25117245704200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record009_result⟩)
 (.branch 11
 (.leaf ⟨(26, 25117245834248), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record010_result⟩)
 (.leaf ⟨(26, 25117258481664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(26, 25117262610433), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record012_result⟩)
 (.branch 14
 (.leaf ⟨(26, 25117510075400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record013_result⟩)
 (.leaf ⟨(26, 25125827250432), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(26, 25125961662464), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 25128117207040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record016_result⟩)
 (.leaf ⟨(26, 25152492470272), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(26, 25152498712576), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record018_result⟩)
 (.branch 20
 (.leaf ⟨(26, 25152688505088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record019_result⟩)
 (.leaf ⟨(26, 25152690651136), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(26, 25152696893440), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record021_result⟩)
 (.branch 23
 (.leaf ⟨(26, 25153631748096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record022_result⟩)
 (.leaf ⟨(26, 25153656326144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record023_result⟩))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ⟨(26, 25153763868672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record024_result⟩)
 (.branch 26
 (.leaf ⟨(26, 25153770110976), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record025_result⟩)
 (.leaf ⟨(26, 25156902780928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record026_result⟩)))
 (.branch 28
 (.leaf ⟨(26, 25160019362048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record027_result⟩)
 (.branch 29
 (.leaf ⟨(26, 25160029571072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record028_result⟩)
 (.leaf ⟨(26, 25160128661504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record029_result⟩))))
 (.branch 33
 (.branch 31
 (.leaf ⟨(26, 25160472600640), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record030_result⟩)
 (.branch 32
 (.leaf ⟨(26, 25160473657344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record031_result⟩)
 (.leaf ⟨(26, 25160489115712), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record032_result⟩)))
 (.branch 34
 (.leaf ⟨(26, 25177115598912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record033_result⟩)
 (.branch 35
 (.leaf ⟨(26, 25177149685760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record034_result⟩)
 (.leaf ⟨(26, 25177151766528), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record035_result⟩)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ⟨(26, 25177184796672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record036_result⟩)
 (.branch 38
 (.leaf ⟨(26, 25178239287296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record037_result⟩)
 (.leaf ⟨(26, 25178241368064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(26, 25185843740672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record039_result⟩)
 (.branch 41
 (.leaf ⟨(26, 25185851803648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record040_result⟩)
 (.leaf ⟨(26, 25185982103552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record041_result⟩))))
 (.branch 45
 (.branch 43
 (.leaf ⟨(26, 25186091141376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record042_result⟩)
 (.branch 44
 (.leaf ⟨(26, 25186493794368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record043_result⟩)
 (.leaf ⟨(26, 25190251759872), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record044_result⟩)))
 (.branch 46
 (.leaf ⟨(26, 25190260148224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record045_result⟩)
 (.branch 47
 (.leaf ⟨(26, 25190788497928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record046_result⟩)
 (.leaf ⟨(26, 25194420897792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00050.record047_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (16592 + i))) 0 48 :=
  interval_of_check _ 0 48 (by decide +kernel)

public theorem complete : Block 16592 16640 :=
  block_of_table results 16592 48 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0366
