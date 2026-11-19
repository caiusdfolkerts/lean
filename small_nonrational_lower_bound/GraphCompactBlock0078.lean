module
prelude
import GraphInputsRow23Part00000Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0078
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 40
 (.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(23, 664256217088), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record000_result⟩)
 (.leaf ⟨(23, 732973596672), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record001_result⟩))
 (.branch 3
 (.leaf ⟨(23, 741295095808), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record002_result⟩)
 (.branch 4
 (.leaf ⟨(23, 743713112064), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record003_result⟩)
 (.leaf ⟨(23, 743847329792), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(23, 797534388224), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record005_result⟩)
 (.leaf ⟨(23, 801695137792), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record006_result⟩))
 (.branch 8
 (.leaf ⟨(23, 806120128512), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record007_result⟩)
 (.branch 9
 (.leaf ⟨(23, 814705868800), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record008_result⟩)
 (.leaf ⟨(23, 814714191872), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(23, 818602377216), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record010_result⟩)
 (.leaf ⟨(23, 818866618368), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record011_result⟩))
 (.branch 13
 (.leaf ⟨(23, 818874941440), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record012_result⟩)
 (.branch 14
 (.leaf ⟨(23, 819139182592), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record013_result⟩)
 (.leaf ⟨(23, 872562130944), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(23, 938865655808), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record015_result⟩)
 (.leaf ⟨(23, 1003290165248), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record016_result⟩))
 (.branch 18
 (.leaf ⟨(23, 1007583035392), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record017_result⟩)
 (.branch 19
 (.leaf ⟨(23, 1016168775680), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record018_result⟩)
 (.leaf ⟨(23, 1026566422784), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record019_result⟩))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf ⟨(23, 1026702770176), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record020_result⟩)
 (.leaf ⟨(23, 1026711093248), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record021_result⟩))
 (.branch 23
 (.leaf ⟨(23, 1026843213824), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record022_result⟩)
 (.branch 24
 (.leaf ⟨(23, 1042135679232), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record023_result⟩)
 (.leaf ⟨(23, 1364327464960), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record024_result⟩))))
 (.branch 27
 (.branch 26
 (.leaf ⟨(23, 1422317944832), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record025_result⟩)
 (.leaf ⟨(23, 1507739107328), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record026_result⟩))
 (.branch 28
 (.leaf ⟨(23, 1587196002560), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record027_result⟩)
 (.branch 29
 (.leaf ⟨(23, 1689411191040), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record028_result⟩)
 (.leaf ⟨(23, 1689679593728), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record029_result⟩)))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf ⟨(23, 1689679659008), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record030_result⟩)
 (.leaf ⟨(23, 1693972463872), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record031_result⟩))
 (.branch 33
 (.leaf ⟨(23, 1697195757824), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record032_result⟩)
 (.branch 34
 (.leaf ⟨(23, 1702289801472), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record033_result⟩)
 (.leaf ⟨(23, 1702293963008), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record034_result⟩))))
 (.branch 37
 (.branch 36
 (.leaf ⟨(23, 1702294028288), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record035_result⟩)
 (.leaf ⟨(23, 1723972288512), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record036_result⟩))
 (.branch 38
 (.leaf ⟨(23, 1728265158656), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record037_result⟩)
 (.branch 39
 (.leaf ⟨(23, 1736454537216), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record038_result⟩)
 (.leaf ⟨(23, 1736586657792), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record039_result⟩)))))))
 (.branch 60
 (.branch 50
 (.branch 45
 (.branch 42
 (.branch 41
 (.leaf ⟨(23, 1736850898944), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record040_result⟩)
 (.leaf ⟨(23, 1737729511680), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record041_result⟩))
 (.branch 43
 (.leaf ⟨(23, 1859058204928), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record042_result⟩)
 (.branch 44
 (.leaf ⟨(23, 1859322446080), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record043_result⟩)
 (.leaf ⟨(23, 1859330834432), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record044_result⟩))))
 (.branch 47
 (.branch 46
 (.leaf ⟨(23, 1875436961792), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record045_result⟩)
 (.leaf ⟨(23, 1876774879232), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record046_result⟩))
 (.branch 48
 (.leaf ⟨(23, 1877718663168), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record047_result⟩)
 (.branch 49
 (.leaf ⟨(23, 1894646874112), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record048_result⟩)
 (.leaf ⟨(23, 1907649153024), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record049_result⟩)))))
 (.branch 55
 (.branch 52
 (.branch 51
 (.leaf ⟨(23, 1912090918912), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record050_result⟩)
 (.leaf ⟨(23, 1920387448832), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record051_result⟩))
 (.branch 53
 (.leaf ⟨(23, 1920395771904), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record052_result⟩)
 (.branch 54
 (.leaf ⟨(23, 1980663627776), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record053_result⟩)
 (.leaf ⟨(23, 1996492964096), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record054_result⟩))))
 (.branch 57
 (.branch 56
 (.leaf ⟨(23, 1996501352448), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record055_result⟩)
 (.leaf ⟨(23, 1996893487360), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record056_result⟩))
 (.branch 58
 (.leaf ⟨(23, 1998581727232), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record057_result⟩)
 (.branch 59
 (.leaf ⟨(23, 1999621914624), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record058_result⟩)
 (.leaf ⟨(23, 2002874597376), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record059_result⟩))))))
 (.branch 70
 (.branch 65
 (.branch 62
 (.branch 61
 (.leaf ⟨(23, 2002940657664), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record060_result⟩)
 (.leaf ⟨(23, 2004013875200), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record061_result⟩))
 (.branch 63
 (.leaf ⟨(23, 2019452534784), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record062_result⟩)
 (.branch 64
 (.leaf ⟨(23, 2019777609984), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record063_result⟩)
 (.leaf ⟨(23, 2019913957376), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record064_result⟩))))
 (.branch 67
 (.branch 66
 (.leaf ⟨(23, 2019922280448), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record065_result⟩)
 (.leaf ⟨(23, 2020318642176), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record066_result⟩))
 (.branch 68
 (.leaf ⟨(23, 2031817392128), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record067_result⟩)
 (.branch 69
 (.leaf ⟨(23, 2032337422336), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record068_result⟩)
 (.leaf ⟨(23, 2036110262272), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record069_result⟩)))))
 (.branch 75
 (.branch 72
 (.branch 71
 (.leaf ⟨(23, 2036217479424), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record070_result⟩)
 (.leaf ⟨(23, 2036374503424), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record071_result⟩))
 (.branch 73
 (.leaf ⟨(23, 2036485882112), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record072_result⟩)
 (.branch 74
 (.leaf ⟨(23, 2036498171904), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record073_result⟩)
 (.leaf ⟨(23, 2040923226112), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record074_result⟩))))
 (.branch 77
 (.branch 76
 (.leaf ⟨(23, 2049508966400), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record075_result⟩)
 (.leaf ⟨(23, 2049517289472), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record076_result⟩))
 (.branch 78
 (.leaf ⟨(23, 2057557966848), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record077_result⟩)
 (.branch 79
 (.leaf ⟨(23, 2057566224384), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record078_result⟩)
 (.leaf ⟨(23, 2057566289920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record079_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (5580 + i))) 0 80 :=
  interval_of_check _ 0 80 (by decide +kernel)

public theorem complete : Block 5580 5660 :=
  block_of_table results 5580 80 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0078
