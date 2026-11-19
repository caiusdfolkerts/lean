module
prelude
import GraphInputsSix0Part00080Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1045
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 37
 (.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(32, 31484929384704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record000_result⟩)
 (.leaf ⟨(32, 31491976364288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record001_result⟩))
 (.branch 3
 (.leaf ⟨(32, 31491980591104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record002_result⟩)
 (.leaf ⟨(32, 31491987873792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(32, 31492119994368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record004_result⟩)
 (.leaf ⟨(32, 31492177666304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record005_result⟩))
 (.branch 7
 (.leaf ⟨(32, 31493250883840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 31495801020448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record007_result⟩)
 (.leaf ⟨(32, 31511239786752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(32, 31511512416256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record009_result⟩)
 (.leaf ⟨(32, 31511776657408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record010_result⟩))
 (.branch 12
 (.leaf ⟨(32, 31511784980480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record011_result⟩)
 (.leaf ⟨(32, 31513320161536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(32, 31513592791040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record013_result⟩)
 (.leaf ⟨(32, 31513857032192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record014_result⟩))
 (.branch 16
 (.leaf ⟨(32, 31513865355264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 31514055213056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record016_result⟩)
 (.leaf ⟨(32, 31514897219584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record017_result⟩))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf ⟨(32, 31519288591104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record018_result⟩)
 (.leaf ⟨(32, 31520799654144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record019_result⟩))
 (.branch 21
 (.leaf ⟨(32, 31521914290176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record020_result⟩)
 (.leaf ⟨(32, 31522451095552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(32, 31526202933504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record022_result⟩)
 (.leaf ⟨(32, 31526537461760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record023_result⟩))
 (.branch 25
 (.leaf ⟨(32, 31526743965696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record024_result⟩)
 (.branch 26
 (.leaf ⟨(32, 31527610090240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record025_result⟩)
 (.leaf ⟨(32, 31528419655680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record026_result⟩)))))
 (.branch 32
 (.branch 29
 (.branch 28
 (.leaf ⟨(32, 31528692219904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record027_result⟩)
 (.leaf ⟨(32, 31529220702208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record028_result⟩))
 (.branch 30
 (.leaf ⟨(32, 31529389555968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record029_result⟩)
 (.branch 31
 (.leaf ⟨(32, 31530160226848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record030_result⟩)
 (.leaf ⟨(32, 31530160758784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record031_result⟩))))
 (.branch 34
 (.branch 33
 (.leaf ⟨(32, 31530500030464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record032_result⟩)
 (.leaf ⟨(32, 31530772594688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record033_result⟩))
 (.branch 35
 (.leaf ⟨(32, 31531235016704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 31531301076992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record035_result⟩)
 (.leaf ⟨(32, 31537979523072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record036_result⟩)))))))
 (.branch 56
 (.branch 46
 (.branch 41
 (.branch 39
 (.branch 38
 (.leaf ⟨(32, 31538053906432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record037_result⟩)
 (.leaf ⟨(32, 31538516328448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record038_result⟩))
 (.branch 40
 (.leaf ⟨(32, 31545532416256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record039_result⟩)
 (.leaf ⟨(32, 31545805045760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record040_result⟩)))
 (.branch 43
 (.branch 42
 (.leaf ⟨(32, 31546069286912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record041_result⟩)
 (.leaf ⟨(32, 31546077609984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record042_result⟩))
 (.branch 44
 (.leaf ⟨(32, 31546267467776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 31551971721472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record044_result⟩)
 (.leaf ⟨(32, 31552508592128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record045_result⟩)))))
 (.branch 51
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 31552516915200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record046_result⟩)
 (.leaf ⟨(32, 31553011908864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 31560561623296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record048_result⟩)
 (.branch 50
 (.leaf ⟨(32, 31560830091264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record049_result⟩)
 (.leaf ⟨(32, 31560838414336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record050_result⟩))))
 (.branch 53
 (.branch 52
 (.leaf ⟨(32, 31561299795968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record051_result⟩)
 (.leaf ⟨(32, 31561601810688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record052_result⟩))
 (.branch 54
 (.leaf ⟨(32, 31562373013504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 31568044237056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record054_result⟩)
 (.leaf ⟨(32, 31569151590400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record055_result⟩))))))
 (.branch 65
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf ⟨(32, 31569688395776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record056_result⟩)
 (.leaf ⟨(32, 31570191777792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record057_result⟩))
 (.branch 59
 (.leaf ⟨(32, 31570266161152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record058_result⟩)
 (.leaf ⟨(32, 31570728583168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record059_result⟩)))
 (.branch 62
 (.branch 61
 (.leaf ⟨(32, 31578768081152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record060_result⟩)
 (.leaf ⟨(32, 31579040710656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record061_result⟩))
 (.branch 63
 (.leaf ⟨(32, 31579304951808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 31579313274880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record063_result⟩)
 (.leaf ⟨(32, 31579552677888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record064_result⟩)))))
 (.branch 70
 (.branch 67
 (.branch 66
 (.leaf ⟨(32, 31585207386368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record065_result⟩)
 (.leaf ⟨(32, 31585744257024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record066_result⟩))
 (.branch 68
 (.leaf ⟨(32, 31585752580096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record067_result⟩)
 (.branch 69
 (.leaf ⟨(32, 31585793802240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record068_result⟩)
 (.leaf ⟨(32, 31587337175296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record069_result⟩))))
 (.branch 72
 (.branch 71
 (.leaf ⟨(32, 31593797288192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record070_result⟩)
 (.leaf ⟨(32, 31594115301376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record071_result⟩))
 (.branch 73
 (.leaf ⟨(32, 31594338320384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record072_result⟩)
 (.branch 74
 (.leaf ⟨(32, 31594585006080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record073_result⟩)
 (.leaf ⟨(32, 31595927077120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00080.record074_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (34563 + i))) 0 75 :=
  interval_of_check _ 0 75 (by decide +kernel)

public theorem complete : Block 34563 34638 :=
  block_of_table results 34563 75 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1045
