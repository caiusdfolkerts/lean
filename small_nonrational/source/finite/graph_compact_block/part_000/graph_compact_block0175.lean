module
prelude
import GraphInputsRow24Part00059Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0175
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 29
 (.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 21376338510080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 21376340656128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record001_result⟩)
 (.leaf ⟨(24, 21376346898432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 21376398264320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record003_result⟩)
 (.leaf ⟨(24, 21378602369792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 21379005022784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record005_result⟩)
 (.leaf ⟨(24, 21380548804864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(24, 21380559013888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 21380901912640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record008_result⟩)
 (.leaf ⟨(24, 21380904009728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 21380951457856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record010_result⟩)
 (.leaf ⟨(24, 21381018558528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 21383165772352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record012_result⟩)
 (.leaf ⟨(24, 21401822175296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(24, 21401889292288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record014_result⟩)
 (.branch 16
 (.leaf ⟨(24, 21401891373056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record015_result⟩)
 (.leaf ⟨(24, 21402023363072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(24, 21446153797888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record017_result⟩)
 (.leaf ⟨(24, 21446157959424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record018_result⟩))
 (.branch 20
 (.leaf ⟨(24, 21446158024704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record019_result⟩)
 (.leaf ⟨(24, 21446160040192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record020_result⟩))))
 (.branch 25
 (.branch 23
 (.branch 22
 (.leaf ⟨(24, 21446260691200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record021_result⟩)
 (.leaf ⟨(24, 21450452910336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record022_result⟩))
 (.branch 24
 (.leaf ⟨(24, 21450553561344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record023_result⟩)
 (.leaf ⟨(24, 21450717151488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record024_result⟩)))
 (.branch 27
 (.branch 26
 (.leaf ⟨(24, 21450717216768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record025_result⟩)
 (.leaf ⟨(24, 21450723442752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record026_result⟩))
 (.branch 28
 (.leaf ⟨(24, 21450824093760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record027_result⟩)
 (.leaf ⟨(24, 21454045319184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record028_result⟩))))))
 (.branch 43
 (.branch 36
 (.branch 32
 (.branch 30
 (.leaf ⟨(24, 21459139301632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record029_result⟩)
 (.branch 31
 (.leaf ⟨(24, 21513781182720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record030_result⟩)
 (.leaf ⟨(24, 21513785344256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record031_result⟩)))
 (.branch 34
 (.branch 33
 (.leaf ⟨(24, 21513785409536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record032_result⟩)
 (.leaf ⟨(24, 21513788985600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record033_result⟩))
 (.branch 35
 (.leaf ⟨(24, 21518080295168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record034_result⟩)
 (.leaf ⟨(24, 21518080360448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record035_result⟩))))
 (.branch 39
 (.branch 37
 (.leaf ⟨(24, 21518081855744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record036_result⟩)
 (.branch 38
 (.leaf ⟨(24, 21518344536320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record037_result⟩)
 (.leaf ⟨(24, 21518344601600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record038_result⟩)))
 (.branch 41
 (.branch 40
 (.leaf ⟨(24, 21518346096896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record039_result⟩)
 (.leaf ⟨(24, 21518469826576), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record040_result⟩))
 (.branch 42
 (.leaf ⟨(24, 21519543566337), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record041_result⟩)
 (.leaf ⟨(24, 21522752766208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record042_result⟩)))))
 (.branch 50
 (.branch 46
 (.branch 44
 (.leaf ⟨(24, 21557116207104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record043_result⟩)
 (.branch 45
 (.leaf ⟨(24, 21582506365184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record044_result⟩)
 (.leaf ⟨(24, 21582770606336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(24, 21582776897600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record046_result⟩)
 (.leaf ⟨(24, 21587068207168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record047_result⟩))
 (.branch 49
 (.leaf ⟨(24, 21587069767744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record048_result⟩)
 (.leaf ⟨(24, 21587187206160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record049_result⟩))))
 (.branch 54
 (.branch 52
 (.branch 51
 (.leaf ⟨(24, 21588260945921), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record050_result⟩)
 (.leaf ⟨(24, 21595508705296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record051_result⟩))
 (.branch 53
 (.leaf ⟨(24, 21596582445057), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record052_result⟩)
 (.leaf ⟨(24, 21719941124352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record053_result⟩)))
 (.branch 56
 (.branch 55
 (.leaf ⟨(24, 21724240285760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record054_result⟩)
 (.leaf ⟨(24, 21921664368896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record055_result⟩))
 (.branch 57
 (.leaf ⟨(24, 21921668595712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record056_result⟩)
 (.leaf ⟨(24, 21921676658688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00059.record057_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10019 + i))) 0 58 :=
  interval_of_check _ 0 58 (by decide +kernel)

public theorem complete : Block 10019 10077 :=
  block_of_table results 10019 58 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0175
