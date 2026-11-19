module
prelude
public import SmallFacetUniverse
public import RawSharedCache
public import PackedRawNatGrowth
public import FiniteChecks
public import RootedSmallCacheBadData000
public import RootedSmallCacheBadData001
public import RootedSmallCacheBadData002
public import RootedSmallCacheBadData003
public import RootedSmallCacheBadData004
public import RootedSmallCacheBadData005
public import RootedSmallCacheBadData006
public import RootedSmallCacheBadData007
public import RootedSmallCacheBadData008
public import RootedSmallCacheBadData009
public import RootedSmallCacheBadData010
public import RootedSmallCacheBadData011
public import RootedSmallCacheBadData012
public import RootedSmallCacheBadData013
public import RootedSmallCacheTableCandidateTable
public import RootedSmallCacheTableCandidateSupportTable
public import RootedSmallCacheTableEdgeTable
public import RootedSmallCacheTableEdgeSupportTable
public import RootedSmallCacheTableVertexTable
public import RootedSmallCacheTableKindTable
public import RootedSmallCacheTableKindSupportTable
public import RootedSmallCacheTableMissingTable

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedSmallCache
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def badTable : Table Nat :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf badBlock000)
 (.branch 2
 (.leaf badBlock001)
 (.leaf badBlock002)))
 (.branch 5
 (.branch 4
 (.leaf badBlock003)
 (.leaf badBlock004))
 (.branch 6
 (.leaf badBlock005)
 (.leaf badBlock006))))
 (.branch 10
 (.branch 8
 (.leaf badBlock007)
 (.branch 9
 (.leaf badBlock008)
 (.leaf badBlock009)))
 (.branch 12
 (.branch 11
 (.leaf badBlock010)
 (.leaf badBlock011))
 (.branch 13
 (.leaf badBlock012)
 (.leaf badBlock013)))))

abbrev cellCount : Nat := 3436
def row (T : Table Nat) (i : Nat) : List Nat :=
  let code := T.get i
  (PackedRawNatGrowth.readList 12 (PackedRawNatGrowth.take 16 code)
    (PackedRawNatGrowth.drop 16 code)).1
def rawCells (i : Nat) : Cell := unpackCell (FacetUniverses.Small.cellTable.get i)
def candidateMasks := candidateTable.get
def candidateSupports := row candidateSupportTable
def edgeMasks := edgeTable.get
def edgeSupports := row edgeSupportTable
def vertexMasks := vertexTable.get
def kindMasks := kindTable.get
def kindSupports := row kindSupportTable
def keys := List.range 5
def fastKind (i : Nat) : Nat := (47657384360898964168130883744600824300887903923165343677144032620359621553112219210370766499328115094609625760493777750263882639007769360222353127447078943806658242256871406462883908542467876564168786945839248879017569474494290291620452184863081316212579409663616418967620273282791574134488260141046627052027227141170336639266098127184608021571361657446894407146507380790316130298492557515589313958174617694886693783536725621599084981993952707585054660416872534009778166125967437675349641462740927355966114030835649606564470066063459822834347502436065513630147910107401608840096176855369072534149007157015302381272389698322506645362670033740952937961262508831526940209924900699864762192642294726186469816683169935489907260081358753668099632669777113999758317731217557583399286504001905902232106830882679593388626774326677030002730723713646972475781003797538800164208120641829229569362531502846676703686363517973407175560558458364529871935450218137442854780424624365171090314151470849910230342956992971245867865908869945402241170620671947391677131631434327680998639780961710836170875016737729427989655368782512938630314938185062755142778159468816289819242353653763133355721021600505065482603863029572750642068041002405172685625833863619336968605121200404084043902359164511206993379672756627984584763360492525159900554037806798081903111915597881446388767822158672680073174275777759940358464904505956655333310090007638665710741340093269247663934268022844390261418960673566601292411925692487217306200491924330344011715510138214323428446013162871368970910432652356241837699718155924899046625265222681364791310827372414056522310740649641400650531914163117429371096095977578493578551653966048946636156967333627943856742162137825343035999175273057575795595536079853144339799545977075981777725813023081700883082812693086737044510232467128516285483357783169199546986595418363421023294230241840213163712274490229315699249102676070875232489279902995918529048496944982675164295539807345111970180996607315699794744698236042965427612482872336286885840410083438349768849379344478721364 >>> (2*i)) % 4
def missing (i : Nat) : List Nat :=
  let code := PackedRawNatGrowth.take 24
    (PackedRawNatGrowth.drop (24*(i%128)) (missingTable.get (i/128)))
  (PackedRawNatGrowth.readList 10 (PackedRawNatGrowth.take 4 code)
    (PackedRawNatGrowth.drop 4 code)).1
def badMasks (i : Nat) : Nat := PackedRawNatGrowth.take 3436
  (PackedRawNatGrowth.drop (3436*(i%256)) (badTable.get (i/256)))
def data : RawSharedCache.Data cellCount :=
  ⟨rawCells,candidateMasks,candidateSupports,edgeMasks,edgeSupports,
    vertexMasks,kindMasks,kindSupports,keys,fastKind,missing,badMasks⟩
def cellTest (i : Nat) : Bool := (RawFacetEmbedding.wellFormedCheck (rawCells i) && ((rawCells i).edges.all (fun e => decide (Nat.land e (rawCells i).vertices = e)) && ((rawCells i).ridgeMasks.all (fun q => (candidateMasks q).testBit i) && ((rawCells i).edges.all (fun e => (edgeMasks e).testBit i) && ((List.finRange 10).all (fun v => decide ((vertexMasks v.val).testBit i = (rawCells i).vertices.testBit v.val)) && (decide (fastKind i = (rawCells i).kind) && (missing i).all (fun e => decide (Nat.land e (rawCells i).vertices = e) && decide (e ∉ (rawCells i).edges))))))))
def ridgeTest (i : Nat) : Bool := (decide (candidateMasks i = RawNatGrowthCheck.mask (candidateSupports i)) && (candidateSupports i).all (fun c => hasNat (rawCells c).ridgeMasks i))
def edgeTest (i : Nat) : Bool := (decide (edgeMasks i = RawNatGrowthCheck.mask (edgeSupports i)) && (edgeSupports i).all (fun c => hasNat (rawCells c).edges i))
def kindTest (i : Nat) : Bool := (decide (kindMasks i = RawNatGrowthCheck.mask (kindSupports i)) && (kindSupports i).all (fun c => decide ((rawCells c).kind = i)))

end Papers.RationalityTen.RootedSmallCache
