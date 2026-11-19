module
prelude
import GraphInputsRow25Part00020Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0310
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(25, 29596619637252), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record000_result⟩)
 (.branch 2
 (.leaf ⟨(25, 29690213466112), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record001_result⟩)
 (.leaf ⟨(25, 29692359901184), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(25, 29692756262912), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record003_result⟩)
 (.branch 5
 (.leaf ⟨(25, 29693928018048), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record004_result⟩)
 (.leaf ⟨(25, 29725628596224), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(25, 29726140010624), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record006_result⟩)
 (.branch 8
 (.leaf ⟨(25, 29727213486720), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record007_result⟩)
 (.leaf ⟨(25, 29757832462592), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(25, 29757840850944), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record009_result⟩)
 (.branch 11
 (.leaf ⟨(25, 29760432640128), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record010_result⟩)
 (.leaf ⟨(25, 29765534810112), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(25, 29772914888832), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record012_result⟩)
 (.branch 14
 (.leaf ⟨(25, 29902705328128), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record013_result⟩)
 (.leaf ⟨(25, 30031686696960), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(25, 30237799284736), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record015_result⟩)
 (.branch 17
 (.leaf ⟨(25, 30237803446272), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record016_result⟩)
 (.leaf ⟨(25, 30237807087616), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(25, 30238197694592), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record018_result⟩)
 (.branch 20
 (.leaf ⟨(25, 30238203449344), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record019_result⟩)
 (.leaf ⟨(25, 30241150472448), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(25, 30241158860800), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record021_result⟩)
 (.branch 23
 (.leaf ⟨(25, 30241166987520), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record022_result⟩)
 (.leaf ⟨(25, 30241175375872), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record023_result⟩))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ⟨(25, 30241418907776), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record024_result⟩)
 (.branch 26
 (.leaf ⟨(25, 30241435422848), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record025_result⟩)
 (.leaf ⟨(25, 30241670303760), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record026_result⟩)))
 (.branch 28
 (.leaf ⟨(25, 30242240463616), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record027_result⟩)
 (.branch 29
 (.leaf ⟨(25, 30242508898944), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record028_result⟩)
 (.leaf ⟨(25, 30242743779856), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record029_result⟩))))
 (.branch 33
 (.branch 31
 (.leaf ⟨(25, 30246537592832), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record030_result⟩)
 (.branch 32
 (.leaf ⟨(25, 30253917671552), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record031_result⟩)
 (.leaf ⟨(25, 30254152552464), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record032_result⟩)))
 (.branch 34
 (.leaf ⟨(25, 30255226028560), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record033_result⟩)
 (.branch 35
 (.leaf ⟨(25, 30305583108096), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record034_result⟩)
 (.leaf ⟨(25, 30314416179216), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record035_result⟩)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ⟨(25, 30314432823824), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record036_result⟩)
 (.branch 38
 (.leaf ⟨(25, 30315363958784), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record037_result⟩)
 (.leaf ⟨(25, 30378589487104), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(25, 30382615970048), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record039_result⟩)
 (.branch 41
 (.leaf ⟨(25, 30511603126272), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record040_result⟩)
 (.leaf ⟨(25, 30516027851280), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record041_result⟩))))
 (.branch 45
 (.branch 43
 (.leaf ⟨(25, 30717606234120), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record042_result⟩)
 (.branch 44
 (.leaf ⟨(25, 30717623011328), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record043_result⟩)
 (.leaf ⟨(25, 30717623271424), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record044_result⟩)))
 (.branch 46
 (.leaf ⟨(25, 30787485868288), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record045_result⟩)
 (.branch 47
 (.leaf ⟨(25, 30787555106848), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record046_result⟩)
 (.leaf ⟨(25, 30788628844576), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record047_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (13674 + i))) 0 48 :=
  interval_of_check _ 0 48 (by decide +kernel)

public theorem complete : Block 13674 13722 :=
  block_of_table results 13674 48 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0310
