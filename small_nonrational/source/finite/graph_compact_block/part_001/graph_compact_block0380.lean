module
prelude
import GraphInputsRow26Part00064Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0380
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 30316429901824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record000_result⟩)
 (.leaf ⟨(26, 30374164173056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 30448440836096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record002_result⟩)
 (.branch 4
 (.leaf ⟨(26, 30457802522624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record003_result⟩)
 (.leaf ⟨(26, 30481676500992), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(26, 30511466711056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record005_result⟩)
 (.branch 7
 (.leaf ⟨(26, 30787555627296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record006_result⟩)
 (.leaf ⟨(26, 30789685416224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(26, 30789854118144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record008_result⟩)
 (.branch 10
 (.leaf ⟨(26, 30792001593600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record009_result⟩)
 (.leaf ⟨(26, 30792005812256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(26, 30792035143936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record011_result⟩)
 (.leaf ⟨(26, 30793079029792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record012_result⟩))
 (.branch 14
 (.leaf ⟨(26, 30796300755008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record013_result⟩)
 (.branch 15
 (.leaf ⟨(26, 30796300763168), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record014_result⟩)
 (.leaf ⟨(26, 30796564996160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(26, 30796565004320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record016_result⟩)
 (.branch 18
 (.leaf ⟨(26, 30820840837408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record017_result⟩)
 (.leaf ⟨(26, 30825270288640), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(26, 30826326860032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record019_result⟩)
 (.branch 21
 (.leaf ⟨(26, 30826400153600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record020_result⟩)
 (.leaf ⟨(26, 30829833691200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record021_result⟩))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf ⟨(26, 30841726074880), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record022_result⟩)
 (.leaf ⟨(26, 30841730236416), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record023_result⟩))
 (.branch 25
 (.leaf ⟨(26, 30863929188384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record024_result⟩)
 (.branch 26
 (.leaf ⟨(26, 30864193429536), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record025_result⟩)
 (.leaf ⟨(26, 30864919592960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record026_result⟩))))
 (.branch 30
 (.branch 28
 (.leaf ⟨(26, 30865392410656), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record027_result⟩)
 (.branch 29
 (.leaf ⟨(26, 30866466148384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record028_result⟩)
 (.leaf ⟨(26, 30898271750176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record029_result⟩)))
 (.branch 31
 (.leaf ⟨(26, 30898288394784), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record030_result⟩)
 (.branch 32
 (.leaf ⟨(26, 30900825882625), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record031_result⟩)
 (.leaf ⟨(26, 30935115370560), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record032_result⟩)))))
 (.branch 38
 (.branch 35
 (.branch 34
 (.leaf ⟨(26, 30942222647552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record033_result⟩)
 (.leaf ⟨(26, 30942222712832), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record034_result⟩))
 (.branch 36
 (.leaf ⟨(26, 30961962074112), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record035_result⟩)
 (.branch 37
 (.leaf ⟨(26, 30968401379328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record036_result⟩)
 (.leaf ⟨(26, 30970541572096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record037_result⟩))))
 (.branch 41
 (.branch 39
 (.leaf ⟨(26, 30976722878464), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record038_result⟩)
 (.branch 40
 (.leaf ⟨(26, 30978863071232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record039_result⟩)
 (.leaf ⟨(26, 30979399876608), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record040_result⟩)))
 (.branch 42
 (.leaf ⟨(26, 30986144382976), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record041_result⟩)
 (.branch 43
 (.leaf ⟨(26, 31033894436864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record042_result⟩)
 (.leaf ⟨(26, 31033902759936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064.record043_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17139 + i))) 0 44 :=
  interval_of_check _ 0 44 (by decide +kernel)

public theorem complete : Block 17139 17183 :=
  block_of_table results 17139 44 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0380
