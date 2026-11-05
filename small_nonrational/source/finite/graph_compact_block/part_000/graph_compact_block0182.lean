module
prelude
import GraphInputsRow24Part00066Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0182
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 23332965646592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record000_result⟩)
 (.leaf ⟨(24, 23332974034944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 23333081252096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 23347643875584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record003_result⟩)
 (.leaf ⟨(24, 23347996934400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(24, 23347999080448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record005_result⟩)
 (.branch 7
 (.leaf ⟨(24, 23348005322752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record006_result⟩)
 (.leaf ⟨(24, 23348046479616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(24, 23348056688640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record008_result⟩)
 (.branch 10
 (.leaf ⟨(24, 23350260794112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record009_result⟩)
 (.leaf ⟨(24, 23350285959168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(24, 23353884868864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record011_result⟩)
 (.branch 13
 (.leaf ⟨(24, 23354421739520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record012_result⟩)
 (.leaf ⟨(24, 23354430062592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(24, 23375973978176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record014_result⟩)
 (.branch 16
 (.leaf ⟨(24, 23383080271872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record015_result⟩)
 (.leaf ⟨(24, 23383082287360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(24, 23383082352640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record017_result⟩)
 (.branch 19
 (.leaf ⟨(24, 23383089619008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record018_result⟩)
 (.leaf ⟨(24, 23383220699200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(24, 23383221739584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record020_result⟩)
 (.branch 22
 (.leaf ⟨(24, 23384559718464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record021_result⟩)
 (.leaf ⟨(24, 23402607870208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record022_result⟩))))))
 (.branch 34
 (.branch 28
 (.branch 25
 (.branch 24
 (.leaf ⟨(24, 23402616258560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record023_result⟩)
 (.leaf ⟨(24, 23402886742016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record024_result⟩))
 (.branch 26
 (.leaf ⟨(24, 23403010474240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record025_result⟩)
 (.branch 27
 (.leaf ⟨(24, 23404556124416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record026_result⟩)
 (.leaf ⟨(24, 23404564512768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record027_result⟩))))
 (.branch 31
 (.branch 29
 (.leaf ⟨(24, 23404688244992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record028_result⟩)
 (.branch 30
 (.leaf ⟨(24, 23404696633344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record029_result⟩)
 (.leaf ⟨(24, 23404956647680), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record030_result⟩)))
 (.branch 32
 (.leaf ⟨(24, 23404960874496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record031_result⟩)
 (.branch 33
 (.leaf ⟨(24, 23404967116800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record032_result⟩)
 (.leaf ⟨(24, 23405156909312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record033_result⟩)))))
 (.branch 40
 (.branch 37
 (.branch 35
 (.leaf ⟨(24, 23409251598592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record034_result⟩)
 (.branch 36
 (.leaf ⟨(24, 23409259986944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record035_result⟩)
 (.leaf ⟨(24, 23409317658880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record036_result⟩)))
 (.branch 38
 (.leaf ⟨(24, 23410291785984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record037_result⟩)
 (.branch 39
 (.leaf ⟨(24, 23410300174336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record038_result⟩)
 (.leaf ⟨(24, 23413546614784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record039_result⟩))))
 (.branch 43
 (.branch 41
 (.leaf ⟨(24, 23417639158016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record040_result⟩)
 (.branch 42
 (.leaf ⟨(24, 23417845727232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record041_result⟩)
 (.leaf ⟨(24, 23418041811008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record042_result⟩)))
 (.branch 44
 (.leaf ⟨(24, 23419519271168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record043_result⟩)
 (.branch 45
 (.leaf ⟨(24, 23419787739136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record044_result⟩)
 (.leaf ⟨(24, 23419796062208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00066.record045_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10273 + i))) 0 46 :=
  interval_of_check _ 0 46 (by decide +kernel)

public theorem complete : Block 10273 10319 :=
  block_of_table results 10273 46 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0182
