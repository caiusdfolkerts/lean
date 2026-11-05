module
prelude
import GraphInputsRow25Part00007Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0297
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 38
 (.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(25, 8332799148032), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record000_result⟩)
 (.leaf ⟨(25, 8334119862272), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record001_result⟩))
 (.branch 3
 (.leaf ⟨(25, 8334128185344), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record002_result⟩)
 (.leaf ⟨(25, 8402713444352), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(25, 8402837241856), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record004_result⟩)
 (.leaf ⟨(25, 8474784169984), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record005_result⟩))
 (.branch 7
 (.leaf ⟨(25, 8526076317696), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record006_result⟩)
 (.branch 8
 (.leaf ⟨(25, 8538533529616), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record007_result⟩)
 (.leaf ⟨(25, 8539066339456), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(25, 8539883962368), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record009_result⟩)
 (.leaf ⟨(25, 8547790766080), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record010_result⟩))
 (.branch 12
 (.leaf ⟨(25, 8727398844416), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record011_result⟩)
 (.branch 13
 (.leaf ⟨(25, 8727910549512), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record012_result⟩)
 (.leaf ⟨(25, 8727927194120), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(25, 8727935844352), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record014_result⟩)
 (.leaf ⟨(25, 8731945402368), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record015_result⟩))
 (.branch 17
 (.leaf ⟨(25, 8736525516800), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record016_result⟩)
 (.branch 18
 (.leaf ⟨(25, 8740803706880), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record017_result⟩)
 (.leaf ⟨(25, 8744574451712), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record018_result⟩))))))
 (.branch 28
 (.branch 23
 (.branch 21
 (.branch 20
 (.leaf ⟨(25, 8745090418688), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record019_result⟩)
 (.leaf ⟨(25, 8745358983168), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record020_result⟩))
 (.branch 22
 (.leaf ⟨(25, 8749125206016), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record021_result⟩)
 (.leaf ⟨(25, 8757975187456), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(25, 8874817044736), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record023_result⟩)
 (.leaf ⟨(25, 8910593425408), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record024_result⟩))
 (.branch 26
 (.leaf ⟨(25, 8918914924544), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record025_result⟩)
 (.branch 27
 (.leaf ⟨(25, 8919183294592), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record026_result⟩)
 (.leaf ⟨(25, 8921464971392), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record027_result⟩)))))
 (.branch 33
 (.branch 30
 (.branch 29
 (.leaf ⟨(25, 8979310804992), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record028_result⟩)
 (.leaf ⟨(25, 8987632304128), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record029_result⟩))
 (.branch 31
 (.leaf ⟨(25, 8990050230400), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record030_result⟩)
 (.branch 32
 (.leaf ⟨(25, 9024544186400), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record031_result⟩)
 (.leaf ⟨(25, 9118899249280), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record032_result⟩))))
 (.branch 35
 (.branch 34
 (.leaf ⟨(25, 9125067063296), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record033_result⟩)
 (.leaf ⟨(25, 9423465548032), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record034_result⟩))
 (.branch 36
 (.leaf ⟨(25, 9441156010016), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record035_result⟩)
 (.branch 37
 (.leaf ⟨(25, 9502225080448), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record036_result⟩)
 (.leaf ⟨(25, 9505580519456), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record037_result⟩)))))))
 (.branch 57
 (.branch 47
 (.branch 42
 (.branch 40
 (.branch 39
 (.leaf ⟨(25, 9530134036480), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record038_result⟩)
 (.leaf ⟨(25, 9530142359552), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record039_result⟩))
 (.branch 41
 (.leaf ⟨(25, 9539940253697), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record040_result⟩)
 (.leaf ⟨(25, 9634429538336), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record041_result⟩)))
 (.branch 44
 (.branch 43
 (.leaf ⟨(25, 9794964488192), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record042_result⟩)
 (.leaf ⟨(25, 9820853764096), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record043_result⟩))
 (.branch 45
 (.leaf ⟨(25, 9821118005248), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record044_result⟩)
 (.branch 46
 (.leaf ⟨(25, 9935679225856), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record045_result⟩)
 (.leaf ⟨(25, 9941114949888), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record046_result⟩)))))
 (.branch 52
 (.branch 49
 (.branch 48
 (.leaf ⟨(25, 9974602366976), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record047_result⟩)
 (.leaf ⟨(25, 10010104954881), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record048_result⟩))
 (.branch 50
 (.leaf ⟨(25, 10055202115616), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record049_result⟩)
 (.branch 51
 (.leaf ⟨(25, 10090165829632), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record050_result⟩)
 (.leaf ⟨(25, 10138830307328), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record051_result⟩))))
 (.branch 54
 (.branch 53
 (.leaf ⟨(25, 10138941686016), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record052_result⟩)
 (.leaf ⟨(25, 10138953975808), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record053_result⟩))
 (.branch 55
 (.leaf ⟨(25, 10208472530944), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record054_result⟩)
 (.branch 56
 (.leaf ⟨(25, 10214713655296), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record055_result⟩)
 (.leaf ⟨(25, 10218410868737), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record056_result⟩))))))
 (.branch 66
 (.branch 61
 (.branch 59
 (.branch 58
 (.leaf ⟨(25, 10276000825344), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record057_result⟩)
 (.leaf ⟨(25, 10293696561152), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record058_result⟩))
 (.branch 60
 (.leaf ⟨(25, 10301617537024), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record059_result⟩)
 (.leaf ⟨(25, 10301890101248), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record060_result⟩)))
 (.branch 63
 (.branch 62
 (.leaf ⟨(25, 10302154342400), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record061_result⟩)
 (.leaf ⟨(25, 10349399048192), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record062_result⟩))
 (.branch 64
 (.leaf ⟨(25, 10396574449664), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record063_result⟩)
 (.branch 65
 (.leaf ⟨(25, 10448894198016), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_result⟩)
 (.leaf ⟨(25, 10448894263296), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record065_result⟩)))))
 (.branch 71
 (.branch 68
 (.branch 67
 (.leaf ⟨(25, 10448996929792), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record066_result⟩)
 (.leaf ⟨(25, 10455599890432), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record067_result⟩))
 (.branch 69
 (.leaf ⟨(25, 10456781557776), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record068_result⟩)
 (.branch 70
 (.leaf ⟨(25, 10484309393408), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record069_result⟩)
 (.leaf ⟨(25, 10484312969472), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_result⟩))))
 (.branch 73
 (.branch 72
 (.leaf ⟨(25, 10488604344320), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record071_result⟩)
 (.leaf ⟨(25, 10488605839616), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record072_result⟩))
 (.branch 74
 (.leaf ⟨(25, 10488868585472), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record073_result⟩)
 (.branch 75
 (.leaf ⟨(25, 10488870080768), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record074_result⟩)
 (.leaf ⟨(25, 10488993810448), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record075_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (12661 + i))) 0 76 :=
  interval_of_check _ 0 76 (by decide +kernel)

public theorem complete : Block 12661 12737 :=
  block_of_table results 12661 76 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0297
