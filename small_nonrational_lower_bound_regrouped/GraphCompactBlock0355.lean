module
prelude
import GraphInputsRow26Part00039Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0355
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 30
 (.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 21376346898432), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 21376398264320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record001_result⟩)
 (.leaf ⟨(26, 21378602369792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(26, 21379005022784), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record003_result⟩)
 (.leaf ⟨(26, 21380548804864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record004_result⟩))
 (.branch 6
 (.leaf ⟨(26, 21380559013888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record005_result⟩)
 (.leaf ⟨(26, 21380901912640), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(26, 21380904009728), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record007_result⟩)
 (.leaf ⟨(26, 21380951457856), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record008_result⟩))
 (.branch 10
 (.leaf ⟨(26, 21381018558528), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record009_result⟩)
 (.leaf ⟨(26, 21383165772352), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(26, 21401822175296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record011_result⟩)
 (.leaf ⟨(26, 21401889292288), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record012_result⟩))
 (.branch 14
 (.leaf ⟨(26, 21401891373056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record013_result⟩)
 (.leaf ⟨(26, 21402023363072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record014_result⟩)))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf ⟨(26, 21441710473344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 21444948201600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record016_result⟩)
 (.leaf ⟨(26, 21446021677696), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record017_result⟩)))
 (.branch 20
 (.branch 19
 (.leaf ⟨(26, 21446153797888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record018_result⟩)
 (.leaf ⟨(26, 21446157959424), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record019_result⟩))
 (.branch 21
 (.leaf ⟨(26, 21446158024704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record020_result⟩)
 (.leaf ⟨(26, 21446160040192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record021_result⟩))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf ⟨(26, 21446260691200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record022_result⟩)
 (.leaf ⟨(26, 21446663344192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record023_result⟩))
 (.branch 25
 (.leaf ⟨(26, 21450452910336), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record024_result⟩)
 (.leaf ⟨(26, 21450553561344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record025_result⟩)))
 (.branch 28
 (.branch 27
 (.leaf ⟨(26, 21450717151488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record026_result⟩)
 (.leaf ⟨(26, 21450717216768), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record027_result⟩))
 (.branch 29
 (.leaf ⟨(26, 21450723442752), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record028_result⟩)
 (.leaf ⟨(26, 21450824093760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record029_result⟩))))))
 (.branch 45
 (.branch 37
 (.branch 33
 (.branch 31
 (.leaf ⟨(26, 21454045319184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record030_result⟩)
 (.branch 32
 (.leaf ⟨(26, 21459139301632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record031_result⟩)
 (.leaf ⟨(26, 21513781182720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record032_result⟩)))
 (.branch 35
 (.branch 34
 (.leaf ⟨(26, 21513785344256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record033_result⟩)
 (.leaf ⟨(26, 21513785409536), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record034_result⟩))
 (.branch 36
 (.leaf ⟨(26, 21513788985600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record035_result⟩)
 (.leaf ⟨(26, 21514309077008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record036_result⟩))))
 (.branch 41
 (.branch 39
 (.branch 38
 (.leaf ⟨(26, 21518080295168), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record037_result⟩)
 (.leaf ⟨(26, 21518080360448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record038_result⟩))
 (.branch 40
 (.leaf ⟨(26, 21518081855744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record039_result⟩)
 (.leaf ⟨(26, 21518344601600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record040_result⟩)))
 (.branch 43
 (.branch 42
 (.leaf ⟨(26, 21518469826576), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record041_result⟩)
 (.leaf ⟨(26, 21519543566337), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record042_result⟩))
 (.branch 44
 (.leaf ⟨(26, 21557116207104), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record043_result⟩)
 (.leaf ⟨(26, 21582506365184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record044_result⟩)))))
 (.branch 52
 (.branch 48
 (.branch 46
 (.leaf ⟨(26, 21582770606336), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record045_result⟩)
 (.branch 47
 (.leaf ⟨(26, 21582776897600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record046_result⟩)
 (.leaf ⟨(26, 21587068207168), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record047_result⟩)))
 (.branch 50
 (.branch 49
 (.leaf ⟨(26, 21587069767744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record048_result⟩)
 (.leaf ⟨(26, 21587187206160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record049_result⟩))
 (.branch 51
 (.leaf ⟨(26, 21588260945921), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record050_result⟩)
 (.leaf ⟨(26, 21595508705296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record051_result⟩))))
 (.branch 56
 (.branch 54
 (.branch 53
 (.leaf ⟨(26, 21596582445057), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record052_result⟩)
 (.leaf ⟨(26, 21724240285760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record053_result⟩))
 (.branch 55
 (.leaf ⟨(26, 21921664368896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record054_result⟩)
 (.leaf ⟨(26, 21921668595712), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record055_result⟩)))
 (.branch 58
 (.branch 57
 (.leaf ⟨(26, 21921676658688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record056_result⟩)
 (.leaf ⟨(26, 21921798570240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record057_result⟩))
 (.branch 59
 (.leaf ⟨(26, 21921806958592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record058_result⟩)
 (.leaf ⟨(26, 21921808779264), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00039.record059_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (16071 + i))) 0 60 :=
  interval_of_check _ 0 60 (by decide +kernel)

public theorem complete : Block 16071 16131 :=
  block_of_table results 16071 60 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0355
