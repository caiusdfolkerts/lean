module
prelude
import GraphInputsRow23Part00015Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0093
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 33
 (.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(23, 24638216241408), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record000_result⟩)
 (.leaf ⟨(23, 24642513338368), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record001_result⟩))
 (.branch 3
 (.leaf ⟨(23, 24642785902592), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record002_result⟩)
 (.leaf ⟨(23, 24643182264320), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(23, 24646806208512), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record004_result⟩)
 (.leaf ⟨(23, 24647343013888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record005_result⟩))
 (.branch 7
 (.leaf ⟨(23, 24648886583296), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record006_result⟩)
 (.leaf ⟨(23, 24655664513024), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(23, 24661771436032), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record008_result⟩)
 (.leaf ⟨(23, 24663986012160), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record009_result⟩))
 (.branch 11
 (.leaf ⟨(23, 24666066386944), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record010_result⟩)
 (.leaf ⟨(23, 24666198507520), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(23, 24681635643392), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record012_result⟩)
 (.leaf ⟨(23, 24740171907328), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record013_result⟩))
 (.branch 15
 (.leaf ⟨(23, 24740171972608), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record014_result⟩)
 (.leaf ⟨(23, 24741314891776), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(23, 24742813794304), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record016_result⟩)
 (.leaf ⟨(23, 24744960229376), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record017_result⟩))
 (.branch 19
 (.leaf ⟨(23, 24744984871168), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record018_result⟩)
 (.leaf ⟨(23, 24757838839808), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(23, 24759010594944), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record020_result⟩)
 (.leaf ⟨(23, 24777943287824), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record021_result⟩))
 (.branch 23
 (.leaf ⟨(23, 24778220536064), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record022_result⟩)
 (.leaf ⟨(23, 24778228924416), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(23, 24779012768000), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record024_result⟩)
 (.leaf ⟨(23, 24779285495808), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record025_result⟩))
 (.branch 27
 (.leaf ⟨(23, 24779549638656), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record026_result⟩)
 (.leaf ⟨(23, 24779557961728), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(23, 24783173517568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record028_result⟩)
 (.leaf ⟨(23, 24783446147072), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record029_result⟩))
 (.branch 31
 (.leaf ⟨(23, 24783710388224), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record030_result⟩)
 (.branch 32
 (.leaf ⟨(23, 24783718711296), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record031_result⟩)
 (.leaf ⟨(23, 24783842508800), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record032_result⟩)))))))
 (.branch 50
 (.branch 41
 (.branch 37
 (.branch 35
 (.branch 34
 (.leaf ⟨(23, 24786294079744), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record033_result⟩)
 (.leaf ⟨(23, 24787062161408), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record034_result⟩))
 (.branch 36
 (.leaf ⟨(23, 24799947014144), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record035_result⟩)
 (.leaf ⟨(23, 24825515217024), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record036_result⟩)))
 (.branch 39
 (.branch 38
 (.leaf ⟨(23, 24826588693120), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record037_result⟩)
 (.leaf ⟨(23, 24855252631552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record038_result⟩))
 (.branch 40
 (.leaf ⟨(23, 24883698925568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record039_result⟩)
 (.leaf ⟨(23, 24886720397312), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record040_result⟩))))
 (.branch 45
 (.branch 43
 (.branch 42
 (.leaf ⟨(23, 24886728720384), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record041_result⟩)
 (.leaf ⟨(23, 24889940049920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record042_result⟩))
 (.branch 44
 (.leaf ⟨(23, 24894773428480), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record043_result⟩)
 (.leaf ⟨(23, 24894909775872), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record044_result⟩)))
 (.branch 47
 (.branch 46
 (.leaf ⟨(23, 24894918098944), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record045_result⟩)
 (.leaf ⟨(23, 24895041896448), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record046_result⟩))
 (.branch 48
 (.leaf ⟨(23, 24895050219520), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record047_result⟩)
 (.branch 49
 (.leaf ⟨(23, 24895510560768), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record048_result⟩)
 (.leaf ⟨(23, 24895813615872), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record049_result⟩))))))
 (.branch 58
 (.branch 54
 (.branch 52
 (.branch 51
 (.leaf ⟨(23, 24896583778304), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record050_result⟩)
 (.leaf ⟨(23, 24902255001856), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record051_result⟩))
 (.branch 53
 (.leaf ⟨(23, 24964497572096), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record052_result⟩)
 (.leaf ⟨(23, 24966716260352), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record053_result⟩)))
 (.branch 56
 (.branch 55
 (.leaf ⟨(23, 25016188567808), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record054_result⟩)
 (.leaf ⟨(23, 25025030193152), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record055_result⟩))
 (.branch 57
 (.leaf ⟨(23, 25031270994048), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record056_result⟩)
 (.leaf ⟨(23, 25116985819392), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record057_result⟩))))
 (.branch 62
 (.branch 60
 (.branch 59
 (.leaf ⟨(23, 25117254287360), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record058_result⟩)
 (.leaf ⟨(23, 25117262610432), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record059_result⟩))
 (.branch 61
 (.leaf ⟨(23, 25117522690048), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record060_result⟩)
 (.leaf ⟨(23, 25117774317568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record061_result⟩)))
 (.branch 64
 (.branch 63
 (.leaf ⟨(23, 25125852282880), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record062_result⟩)
 (.leaf ⟨(23, 25126095685632), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record063_result⟩))
 (.branch 65
 (.leaf ⟨(23, 25126112330240), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record064_result⟩)
 (.branch 66
 (.leaf ⟨(23, 25152471466240), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record065_result⟩)
 (.leaf ⟨(23, 25154688188416), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record066_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7006 + i))) 0 67 :=
  interval_of_check _ 0 67 (by decide +kernel)

public theorem complete : Block 7006 7073 :=
  block_of_table results 7006 67 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0093
