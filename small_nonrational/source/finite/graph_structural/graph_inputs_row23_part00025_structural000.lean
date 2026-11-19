module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow23Part00025Data
public import GraphInputsRow23Part00025Frames
public import GraphInputsRow23Part00025Leaves
public import GraphInputsRow23Part00025Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00025.record014
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record014
def vertexColumn : Fields := ⟨10, hexnat% "2745aa6659a56358764b8ae1b85e0fb619c56959695356351d62d4b4ad1b61d1743d98e5354cd31cd8b52cab1ad1b16c3b91d4731e2749ca785c3743c4f99254271624a89a198961588e0b81e98561945292664589465854951548d0b41d50d2318c9314d0b22c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "2492492492492492492492492492492492492249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9de40281fc0f0000000000", hexnat% "1e14000000000000000", hexnat% "1a002200000000000000", 865113340920201216, hexnat% "140000500000000000", hexnat% "2200080000200000000000", hexnat% "14000000002000000000000", 1152921504606846976]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10fe9e1c2040f0000000000", 141863388262170624, hexnat% "16022000000000000000", 865113340920201216, hexnat% "140000500000000000", hexnat% "5000001002000000000000", hexnat% "a000000000200000000000", hexnat% "80000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "155fa767267ff0000000000", 114841790497947648, hexnat% "1818000000000000000", hexnat% "2200080000000000000000", hexnat% "800000400000000000000", 576460752303423488, hexnat% "8004000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1047be1f2061c0000000000", hexnat% "1800000000000000000000", hexnat% "1e0000400000000000", hexnat% "300000040020000000000", hexnat% "6080000000000000000000", 123850089264316416, 865113340920201216, hexnat% "8004000000200000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7e022020000000000000", hexnat% "100040040130000000000", hexnat% "8008004008c0000000000", 115967690404790272, hexnat% "161c000000000000000", hexnat% "15400000002000000000000", hexnat% "a280000000200000000000", 1873778919962836992, hexnat% "180000400000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record014_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record014_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00025.record014

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00025.record035
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record035
def vertexColumn : Fields := ⟨10, hexnat% "26c8f0bc5693a2ea4e53a2e2b86e4789e17b499a5598e5392e6a599635534ad1b61d4749d1759354d3392e2b4acab1ac9b16e4751cc789c6745c5783d0f23cb49322c0f0b25291a0e8a6258361382e078b1925498a5190e645894a5254358344d0b41d50ca344c930cd0b12c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "2492492492492492492492492492492492492449249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1cbdebf90feb380000000000", hexnat% "4000008010000000000000", 1337006139375616, 8070450532247928832, hexnat% "4060000000000000000", hexnat% "30200000000000000000000", hexnat% "10000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1cbd6bf90feb380000000000", hexnat% "4068000000000000000", 5699868278390784, 8070591269736284160, hexnat% "4080000000000000000000", hexnat% "30200000000000000000000", hexnat% "10000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "14ad6ffb1feb380000000000", hexnat% "80000040000000000000000", 6917740133873614848, hexnat% "30280000000000000000000", 5629499534213120, hexnat% "10008000000000000000", hexnat% "5000000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "142c6bf80feb380000000000", 5699868278390784, 8070591269736284160, hexnat% "81000000000000000000000", hexnat% "4080008000000000000000", hexnat% "18300000000000000000000", hexnat% "4070000000000000000", hexnat% "20010000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c5 c0
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1054a1ff8eb7780000000000", hexnat% "50000000000000000000", hexnat% "2200000008800000000000", 8088464930757410816, hexnat% "80008000000000000000000", hexnat% "30000000000000000000000", hexnat% "6000000000000000000", hexnat% "48900000100000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1b83adff92e3380000000000", hexnat% "50000800000000000000", 6917740133873614848, hexnat% "40802000100000000000000", hexnat% "6400000000000000000000", 7881299347898368, hexnat% "1000000400000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ba7adff80ebb80000000000", hexnat% "50000800000000000000", 8070520900992106496, 5629499534213120, hexnat% "40802000100000000000000", hexnat% "5000000400000000000000", 144115188075855872]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "19022dff8083380000000000", hexnat% "50000820000000000000", 7951668092076032, 8088605668245766144, hexnat% "6480000000000000000000", hexnat% "48902000100000000000000", hexnat% "20000000200000000000000", hexnat% "1000000400000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7af8a3717fff80000000000", 6917529027641081856, hexnat% "14008000000000000000", hexnat% "1c80000000000000000", hexnat% "181000000000000000000000", hexnat% "60000800000000000000", hexnat% "4000000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7af8e7775e8f80000000000", hexnat% "10000a00000000000000", hexnat% "181000080000000000000000", 6473924464345088, hexnat% "1800000000000000000", hexnat% "60000000000000000000", hexnat% "4000008000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17afefff8debf80000000000", hexnat% "81000000000000000000000", 5629499534213120, 8070450532247928832, hexnat% "10000200000000000000", hexnat% "4000000000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7afa67ff1e8f80000000000", hexnat% "50000800000000000000", 6473924464345088, hexnat% "1800000000000000000", hexnat% "80008000000000000000000", hexnat% "105000000000000000000000", 432345564227567616]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3a7822771e8f00000000000", 6482720557367296, hexnat% "50008800000000000000", hexnat% "1d80000000000000000", hexnat% "c000600000000000000", hexnat% "c1800000000000000000000", hexnat% "100020000000000000000000", hexnat% "4000000000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c19 c14
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c20 c13
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "522fdc0fb3300000000000", hexnat% "50208000000000000000", hexnat% "180400000000000000000000", 3597602046083072, 8088464930757410816, hexnat% "30080000000000000000000", hexnat% "2000020000000000000000", hexnat% "48900010000000000000000"]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "226902effedf80000000000", hexnat% "60000000000000000000", hexnat% "5000000012000000000000", hexnat% "1d00000000000000000", hexnat% "10004000000000000000000", hexnat% "180000000000000000000000", hexnat% "a000000000000000000", hexnat% "48900010000000000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "242d43ffcf0f80000000000", hexnat% "2000000008000000000000", 1970324836974592, hexnat% "1c00000000000000000", hexnat% "10000000200000000000000", hexnat% "28000000000000000000", hexnat% "181400000000000000000000", hexnat% "48902000100000000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "cbf9e3f85fff80000000000", hexnat% "1c00000000000000000", hexnat% "60000800000000000000", 8070450532247928832, hexnat% "104000000000000000000000", hexnat% "30000000200000000000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f9fd637bfe3780000000000", 4611826755915743232, 7881299347898368, hexnat% "1c80000000000000000", hexnat% "28000000000000000000", hexnat% "6000000000000000000000", hexnat% "100000000000000000000000"]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c9f93df85c3380000000000", 7951668092076032, hexnat% "104000000000000000000000", 8079598468991025152, hexnat% "c000200000000000000", hexnat% "60200800000000000000", hexnat% "30000000000000000000000", hexnat% "2000000000000000000000"]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c28 c25
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "78bde37bfe3780000000000", 4611826755915743232, 7881299347898368, hexnat% "1c80000000000000000", hexnat% "100420000000000000000000", hexnat% "6000000000000000000000", hexnat% "81000000000000000000000"]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17ffde7fbff2780000000000", hexnat% "80000000000000000000000", 4611826755915743232, hexnat% "1800001000000000000", hexnat% "20000000000000000000", 3377699720527872]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7cbde77bfe0780000000000", 4611826755915743232, hexnat% "2000000008000000000000", hexnat% "1880003000000000000", hexnat% "181400000000000000000000", 5629499534213120, hexnat% "20000000000000000000"]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "16ffd67ffff2f80000000000", hexnat% "10000000000000000000000", hexnat% "80008000000000000000000", 3659174697238528, hexnat% "1800000000000000000", hexnat% "20000000000000000000"]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1edfd67ffff2f80000000000", hexnat% "28000000000000000000", hexnat% "2000000008000000000000", hexnat% "10000000000000000000000", 1407374883553280, hexnat% "1800000000000000000"]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6dbd67fffe0f80000000000", hexnat% "10000000000000000000000", hexnat% "80008000000000000000000", hexnat% "2000000008000000000000", hexnat% "1800003000000000000", 5629499534213120, hexnat% "100420000000000000000000"]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c36 c35
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c37 c34
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20ad627ffe0f00000000000", hexnat% "2000000008000000000000", hexnat% "18100000000000000000000", hexnat% "28080000000000000000", 6482720557367296, hexnat% "1d00000000000000000", hexnat% "105400000000000000000000", hexnat% "c0000000000000000000000"]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c39 c38
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c40 c33
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c41 c30
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a702c8c80300000000000", 8097683236244684800, hexnat% "1d00003000000000000", 7890095440920576, hexnat% "30000000200000000000000", hexnat% "181400000000000000000000", hexnat% "e020000000000000000", hexnat% "6080000000000000000000", hexnat% "48100010100000000000000"]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c43 c42
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c44 c29
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c45 c24
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c46 c23
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c47 c22
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c48 c21
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c49 c12
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c50 c7
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c51 c6
  c52
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record035_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record035_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record035_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record035_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record035_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record035_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record035_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record035_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record035_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00025.record035

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00025.record047
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record047
def vertexColumn : Fields := ⟨10, hexnat% "bc2eb4699a362d98e938ce8b92e2b86e4785e2e745996352d58d934cd8b52d2b46d4745dd0e638ccb362e4b32e2b4acab1ad1b16f07a1d8731d2729c6785d1715e0f5309c0f14a2683a91946898960d90e2384e0b81e524990e64551625254354348d1342d0764350e2324c3342c8b12c2b06e0741c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "92492492492492492492492492492492492492489249249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000400200124800000000000", hexnat% "100040020040400000000000", hexnat% "40010008001a000000000000", hexnat% "800200100080000000000000", hexnat% "1fe00000000000000", hexnat% "3fc00000000000000000", hexnat% "6208880040000000000000000", hexnat% "f7000000000000000000000", 281474976710656]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record047_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record047_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record047_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record047_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record047_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record047_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record047_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record047_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record047_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00025.record047

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00025.record050
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record050
def vertexColumn : Fields := ⟨10, hexnat% "9723c2f15a4e8ba9394e2b86e8791e2785ed2719965598e5392e695956355362d2b46d4749d1759354d3392d2b2ac6b86c9b16e4751cc719e1745c5783d0f23cb49321c0f0b25291a0e8a6258361382e078b192549865190e64529615254358344d0b41d50ca344c930cd0b12c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "12492492492492492492492492492492492492449249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e9f7e53fff1f80000000000", hexnat% "1800000000000000000", hexnat% "80240000000000000000", hexnat% "12000080000000000000000", hexnat% "4000000008000000000000", 1688849860263936]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e9f1c03fff1f80000000000", hexnat% "e0000000000000000000", hexnat% "4000200008000000000000", hexnat% "12002080000000000000000", 1688849860263936, hexnat% "1c00000000000000000", hexnat% "140000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3a9f01c38c91600000000000", 4107775441371136, 8097472130012151808, hexnat% "80240100000000000000", hexnat% "12002080200000000000000", hexnat% "44000000000000000000000", hexnat% "7c000000000000000000", hexnat% "100000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "209921ff8db7f80000000000", hexnat% "d0000000000000000000", hexnat% "4400000008000000000000", 8088464930757410816, hexnat% "60000000000000000000000", hexnat% "100008000000000000000000", hexnat% "92202000200000000000000", hexnat% "4000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9ffb23f9f7ab80000000000", 1477743627730944, hexnat% "4c000080000000000000", 6917529027641081856, hexnat% "1c00000000000000000", hexnat% "60000000000000000000000", hexnat% "300000000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "bfeb23f9b7ab80000000000", 1477743627730944, hexnat% "4c000080000000000000", hexnat% "40000002400000000000000", 4611686018427387904, hexnat% "1c00000000000000000", hexnat% "300100000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9ffb27f8b7ab80000000000", 1477743627730944, hexnat% "1800000000000000000", hexnat% "4c000080000000000000", hexnat% "300000000000000000000000", 8070450532247928832, hexnat% "60000000400000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ccb03e8b3ff80000000000", hexnat% "1c10000000000000000", hexnat% "3300000000000000000000", 8088464930757410816, hexnat% "4e000080000000000000", hexnat% "240000000000000000000000", hexnat% "180000000000000000000000", hexnat% "20000000400000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "264db0a4ad20700000000000", 5819072931027746816, hexnat% "1430000000000000000", 8453045394341888, hexnat% "9000000000000000000000", hexnat% "100008100000000000000000", hexnat% "46000000000000000000", hexnat% "92200080200000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1408fe7789e0200000000000", hexnat% "1800001400000000000", 8070591269736284160, hexnat% "208100000000000000000000", hexnat% "20000000400000000000000", hexnat% "92200080200080000000000", 8444249301319680, hexnat% "5400000000100000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "144cff7789e9b00000000000", 8070520900992106496, 6201245580656640, hexnat% "200100800000000000000000", hexnat% "9000000000000000000000", hexnat% "20000000400000000000000", hexnat% "92200080200000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "375ffcb2f8e9f00000000000", hexnat% "1410000000000000000", hexnat% "8000040010000000000000", 1697645953286144, 504403158265495552, hexnat% "82002080000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17dfa83f89fff80000000000", hexnat% "46000000000000000000", hexnat% "82000000200000000000000", 8070450532247928832, hexnat% "1c00000000000000000", hexnat% "200010000000000000000000", 288230376151711744]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "375ffca6fce9f00000000000", hexnat% "8000000010000000000000", 216744528160227328, hexnat% "1410000000000000000", 1125899906842624, hexnat% "180000000000000000", hexnat% "82002000000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f7f7e2f97eab80000000000", 5981343255101440, 6917529027641081856, hexnat% "80000800000000000000", hexnat% "d00000000000000000", hexnat% "1000000000000000000", hexnat% "208000000000000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f7f7eff96e8b80000000000", 6917599396385259520, hexnat% "1000001000000000000", hexnat% "80000900000000000000", hexnat% "8000000010000000000000", 1688849860263936]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "375f3dff82e9f80000000000", hexnat% "c0000000000000000000", hexnat% "82002000000000000000000", hexnat% "8000000810000000000000", 1688849860263936, 360287970189639680, 8070450532247928832]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "175f383672e8f00000000000", hexnat% "80000900000000000000", 6482720557367296, hexnat% "46010000000000000000", hexnat% "208000008000000000000000", 288230376151711744, hexnat% "1c00000000000000000", hexnat% "82000080000000000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c24 c19
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c25 c18
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c26 c17
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c27 c16
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "45d1836ffeff80000000000", hexnat% "e0000000000000000000", hexnat% "8000000010000000000000", hexnat% "1c10000000000000000", hexnat% "20004000000000000000000", hexnat% "300000000000000000000000", hexnat% "92202080000000000000000"]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4ccb8268dbff80000000000", hexnat% "46010040000000000000", 8070450532247928832, hexnat% "1c00000000000000000", hexnat% "3300000000000000000000", hexnat% "30000000000000000000000", hexnat% "300000100000000000000000", hexnat% "80000080200000000000000"]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40c0822081e780000000000", hexnat% "1c18001000000000000", hexnat% "f0000020000000000000", hexnat% "d100000000000000000000", 8088605668245766144, hexnat% "300000100000000000000000", hexnat% "20004000480000000000000", hexnat% "40100000000000000", hexnat% "92202080200000000000000"]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c31 c30
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c32 c29
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c33 c28
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c34 c15
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c35 c14
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c36 c13
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c37 c12
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c38 c5
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c39 c4
  c40
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record050_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record050_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record050_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record050_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record050_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record050_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record050_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record050_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record050_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00025.record050
