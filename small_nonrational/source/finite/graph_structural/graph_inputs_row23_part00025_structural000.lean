module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow23Part00025Data
public import GraphInputsRow23Part00025Frames
public import GraphInputsRow23Part00025Leaves
public import GraphInputsRow23Part00025Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

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

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00025.record045
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2f0bad1a66659568d9362da4e538ce8b8ae1b91e178b9d1665655558d5352d64d534cd8b4ad1b51d1774398d9354e334ccb392d4b32e2b2ac6b46c5bc1e8761cc749ca719e1715e0f43c9c0f09a0ea4651a26458960d88e1382e078990e64551625454950d48d1342d0764350e2344c930cc8b12c2b06e0741c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "12492492492492492492492492492492492492492492449249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 45), (facetIndex 46), (facetIndex 51), (facetIndex 66), (facetIndex 81), (facetIndex 97)]))
 (.leaf ([(facetIndex 49), (facetIndex 63), (facetIndex 78), (facetIndex 94)])))
 (.branch 3
 (.leaf ([(facetIndex 44), (facetIndex 47), (facetIndex 52), (facetIndex 53), (facetIndex 67), (facetIndex 82), (facetIndex 98)]))
 (.branch 4
 (.leaf ([(facetIndex 43), (facetIndex 54), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 59), (facetIndex 60)]))
 (.leaf ([(facetIndex 50), (facetIndex 68), (facetIndex 83), (facetIndex 99)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 48), (facetIndex 62), (facetIndex 72), (facetIndex 77), (facetIndex 84), (facetIndex 88), (facetIndex 93), (facetIndex 100), (facetIndex 101)]))
 (.branch 7
 (.leaf ([(facetIndex 64), (facetIndex 79), (facetIndex 95)]))
 (.leaf ([(facetIndex 85), (facetIndex 86), (facetIndex 87), (facetIndex 90), (facetIndex 91)]))))
 (.branch 9
 (.leaf ([(facetIndex 58), (facetIndex 61), (facetIndex 73), (facetIndex 76), (facetIndex 89), (facetIndex 92)]))
 (.branch 10
 (.leaf ([(facetIndex 65), (facetIndex 69), (facetIndex 80), (facetIndex 96)]))
 (.leaf ([(facetIndex 70), (facetIndex 71), (facetIndex 74), (facetIndex 75)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "55420961587785777542096158aa85aa942096158338333322041520023z2b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3, 4]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [3, 4]
def grouped2_0007 : List Nat := [4]
def grouped2_0008 : List Nat := [5, 6, 7]
def grouped2_0009 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped2_0010 : List Nat := [8]
def grouped2_0011 : List Nat := [8, 9, 10]
def grouped2_0012 : List Nat := [9]
def grouped2_0013 : List Nat := [9, 10]
def grouped2_0014 : List Nat := [10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00025.record045" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group\",\"kind\":2,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":6,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00025.record045" 52

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00025.record045" "{\"ridges\":[[9,67],[9,73],[9,74],[15,67],[16,67],[16,577],[19,73],[25,321],[26,577],[31,74],[31,76],[37,322],[38,578],[38,580],[50,67],[54,67],[54,73],[54,74],[56,67],[56,73],[56,74],[59,67],[59,73],[59,74],[60,73],[65,67],[67,67],[67,577],[69,73],[71,73],[71,76],[74,73],[74,76],[75,73],[75,321],[76,73],[76,577],[80,321],[82,577],[83,321],[83,577],[85,74],[85,76],[87,74],[87,76],[90,74],[90,76],[91,74],[91,76],[91,322],[92,74],[92,76],[92,578],[92,580],[96,322],[96,324],[98,578],[98,580],[99,322],[99,578],[99,580]],\"owners\":[[9,73,[19,69,71,74,75,76],[54,56,59,60,61]],[19,73,[9,54,56,59,60,61],[69,71,74,75,76]],[54,73,[19,71,74,75,76],[9,56,59,60,61,69]],[56,73,[19,69,74,75,76],[9,54,59,60,61,71]],[59,73,[19,69,71,75,76],[9,54,56,60,61,74]],[60,73,[19,69,71,74,76],[9,54,56,59,61,75]],[69,73,[9,56,59,60,61],[19,54,71,74,75,76]],[71,73,[9,54,59,60,61],[19,56,69,74,75,76]],[74,73,[9,54,56,60,61],[19,59,69,71,75,76]],[75,73,[9,54,56,59,61],[19,60,69,71,74,76]],[76,73,[9,54,56,59,60],[19,61,69,71,74,75]],[9,74,[31,85,87,90,91,92],[54,56,59,60,61]],[31,74,[9,54,56,59,60,61],[85,87,90,91,92]],[54,74,[31,87,90,91,92],[9,56,59,60,61,85]],[56,74,[31,85,90,91,92],[9,54,59,60,61,87]],[59,74,[31,85,87,91,92],[9,54,56,60,61,90]],[85,74,[9,56,59,60,61],[31,54,87,90,91,92]],[87,74,[9,54,59,60,61],[31,56,85,90,91,92]],[90,74,[9,54,56,60,61],[31,59,85,87,91,92]],[91,74,[9,54,56,59,61],[31,60,85,87,90,92]],[92,74,[9,54,56,59,60],[31,61,85,87,90,91]],[25,321,[15,60,65,68],[75,80,83]],[75,321,[15,65,68],[25,60,80,83]],[80,321,[15,60,68],[25,65,75,83]],[83,321,[15,60,65],[25,68,75,80]],[37,322,[15,60,65,68],[91,96,99]],[91,322,[15,65,68],[37,60,96,99]],[96,322,[15,60,68],[37,65,91,99]],[99,322,[15,60,65],[37,68,91,96]],[16,577,[26,76,82,83],[61,67,68]],[26,577,[16,61,67,68],[76,82,83]],[67,577,[26,76,83],[16,61,68,82]],[76,577,[16,67,68],[26,61,82,83]],[82,577,[16,61,68],[26,67,76,83]],[83,577,[16,61,67],[26,68,76,82]],[38,578,[16,61,67,68],[92,98,99]],[92,578,[16,67,68],[38,61,98,99]],[98,578,[16,61,68],[38,67,92,99]],[99,578,[16,61,67],[38,68,92,98]],[31,76,[19,69,71,74,75,76],[85,87,90,91,92]],[71,76,[31,85,90,91,92],[19,69,74,75,76,87]],[74,76,[31,85,87,91,92],[19,69,71,75,76,90]],[85,76,[19,71,74,75,76],[31,69,87,90,91,92]],[87,76,[19,69,74,75,76],[31,71,85,90,91,92]],[90,76,[19,69,71,75,76],[31,74,85,87,91,92]],[91,76,[19,69,71,74,76],[31,75,85,87,90,92]],[92,76,[19,69,71,74,75],[31,76,85,87,90,91]],[96,324,[25,75,83],[37,80,91,99]],[38,580,[26,76,82,83],[92,98,99]],[92,580,[26,82,83],[38,76,98,99]],[98,580,[26,76,83],[38,82,92,99]],[99,580,[26,76,82],[38,83,92,98]]],\"edges\":[[26,[9,19,31,54,56,59,60,61,69,71,74,75,76,85,87,90,91,92]],[40,[15,25,37,60,65,68,75,80,83,91,96,99]],[41,[16,26,38,61,67,68,76,82,83,92,98,99]]],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00025.record045" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00025.record045\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-15,-1],[-16,-1],[-16,-11],[-16,-14],[-17,-3],[-17,-11],[-17,-16],[-18,-2],[-18,-17],[-19,-10],[-19,-12],[-19,-13],[-19,-17],[-19,-18],[-20,-14],[-20,-17],[-21,-1],[-21,-12],[-21,-14],[-21,-16],[-21,-17],[-21,-18],[-21,-19],[-21,-20],[-22,-12],[-23,-22],[-24,-22],[-25,-11],[-26,-4],[-26,-6],[-26,-22],[-27,-5],[-27,-26],[-28,-12],[-28,-23],[-28,-26],[-28,-27],[-29,-14],[-29,-26],[-30,-4],[-30,-22],[-30,-24],[-30,-25],[-30,-26],[-30,-27],[-30,-28],[-33,-16],[-36,-12],[-37,-14],[-38,-7],[-38,-11],[-38,-31],[-38,-32],[-38,-33],[-38,-34],[-38,-35],[-38,-36],[-1,-2,-3],[-1,-2,-20],[-1,-3,-19],[-1,-11,-19],[-1,-19,-20],[-2,-3,-14],[-2,-3,-16],[-2,-11,-12],[-2,-11,-20],[-2,-16,-20],[-3,-14,-19],[-3,-16,-19],[-11,-14,-19],[-16,-19,-20],[-1,4,22,24,25,26,27],[-4,1,12,14,16,17,18],[-12,4,24,25,26,27],[-14,4,22,25,26,27],[-16,4,22,24,26,27],[-17,4,22,24,25,27],[-22,1,14,16,17,18],[-24,1,12,16,17,18],[-25,1,12,14,17,18],[-26,1,12,14,16,18],[-27,1,12,14,16,17],[-1,7,31,32,33,34,35],[-7,1,12,14,16,17,18],[-12,7,32,33,34,35],[-14,7,31,33,34,35],[-16,7,31,32,34,35],[-31,1,14,16,17,18],[-32,1,12,16,17,18],[-33,1,12,14,17,18],[-34,1,12,14,16,18],[-35,1,12,14,16,17],[-5,2,17,19,21],[-26,2,19,21],[-28,2,17,21],[-30,2,17,19],[-8,2,17,19,21],[-34,2,19,21],[-36,2,17,21],[-38,2,17,19],[-3,6,27,29,30],[-6,3,18,20,21],[-20,6,27,30],[-27,3,20,21],[-29,3,18,21],[-30,3,18,20],[-9,3,18,20,21],[-35,3,20,21],[-37,3,18,21],[-38,3,18,20],[-7,4,22,24,25,26,27],[-24,7,31,33,34,35],[-25,7,31,32,34,35],[-31,4,24,25,26,27],[-32,4,22,25,26,27],[-33,4,22,24,26,27],[-34,4,22,24,25,27],[-35,4,22,24,25,26],[-36,5,26,30],[-9,6,27,29,30],[-35,6,29,30],[-37,6,27,30],[-38,6,27,29],[-39,10,12,13,14,15,16,17],[-40,11,21,30,38],[-30,40],[-38,40],[-41,19,22,28,36],[-42,23,24,25,26],[-43,39,40],[-44,40],[-45,43],[-46,44],[-47,45],[-48,46],[-49,41],[-49,42],[-50,49],[-51,50],[-52,47],[-52,48,51],[52],[1,4,7,12,14,16,17,18,22,24,25,26,27,31,32,33,34,35],[2,5,8,17,19,21,26,28,30,34,36,38],[3,6,9,18,20,21,27,29,30,35,37,38]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group\",\"index\":10,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":57,\"b\":9},{\"tag\":\"incompatible\",\"a\":59,\"b\":9},{\"tag\":\"incompatible\",\"a\":59,\"b\":50},{\"tag\":\"incompatible\",\"a\":59,\"b\":56},{\"tag\":\"incompatible\",\"a\":60,\"b\":16},{\"tag\":\"incompatible\",\"a\":60,\"b\":50},{\"tag\":\"incompatible\",\"a\":60,\"b\":59},{\"tag\":\"incompatible\",\"a\":61,\"b\":15},{\"tag\":\"incompatible\",\"a\":61,\"b\":60},{\"tag\":\"incompatible\",\"a\":65,\"b\":43},{\"tag\":\"incompatible\",\"a\":65,\"b\":54},{\"tag\":\"incompatible\",\"a\":65,\"b\":55},{\"tag\":\"incompatible\",\"a\":65,\"b\":60},{\"tag\":\"incompatible\",\"a\":65,\"b\":61},{\"tag\":\"incompatible\",\"a\":67,\"b\":56},{\"tag\":\"incompatible\",\"a\":67,\"b\":60},{\"tag\":\"incompatible\",\"a\":68,\"b\":9},{\"tag\":\"incompatible\",\"a\":68,\"b\":54},{\"tag\":\"incompatible\",\"a\":68,\"b\":56},{\"tag\":\"incompatible\",\"a\":68,\"b\":59},{\"tag\":\"incompatible\",\"a\":68,\"b\":60},{\"tag\":\"incompatible\",\"a\":68,\"b\":61},{\"tag\":\"incompatible\",\"a\":68,\"b\":65},{\"tag\":\"incompatible\",\"a\":68,\"b\":67},{\"tag\":\"incompatible\",\"a\":69,\"b\":54},{\"tag\":\"incompatible\",\"a\":70,\"b\":69},{\"tag\":\"incompatible\",\"a\":71,\"b\":69},{\"tag\":\"incompatible\",\"a\":74,\"b\":50},{\"tag\":\"incompatible\",\"a\":75,\"b\":19},{\"tag\":\"incompatible\",\"a\":75,\"b\":26},{\"tag\":\"incompatible\",\"a\":75,\"b\":69},{\"tag\":\"incompatible\",\"a\":76,\"b\":25},{\"tag\":\"incompatible\",\"a\":76,\"b\":75},{\"tag\":\"incompatible\",\"a\":80,\"b\":54},{\"tag\":\"incompatible\",\"a\":80,\"b\":70},{\"tag\":\"incompatible\",\"a\":80,\"b\":75},{\"tag\":\"incompatible\",\"a\":80,\"b\":76},{\"tag\":\"incompatible\",\"a\":82,\"b\":56},{\"tag\":\"incompatible\",\"a\":82,\"b\":75},{\"tag\":\"incompatible\",\"a\":83,\"b\":19},{\"tag\":\"incompatible\",\"a\":83,\"b\":69},{\"tag\":\"incompatible\",\"a\":83,\"b\":71},{\"tag\":\"incompatible\",\"a\":83,\"b\":74},{\"tag\":\"incompatible\",\"a\":83,\"b\":75},{\"tag\":\"incompatible\",\"a\":83,\"b\":76},{\"tag\":\"incompatible\",\"a\":83,\"b\":80},{\"tag\":\"incompatible\",\"a\":90,\"b\":59},{\"tag\":\"incompatible\",\"a\":96,\"b\":54},{\"tag\":\"incompatible\",\"a\":98,\"b\":56},{\"tag\":\"incompatible\",\"a\":99,\"b\":31},{\"tag\":\"incompatible\",\"a\":99,\"b\":50},{\"tag\":\"incompatible\",\"a\":99,\"b\":85},{\"tag\":\"incompatible\",\"a\":99,\"b\":87},{\"tag\":\"incompatible\",\"a\":99,\"b\":90},{\"tag\":\"incompatible\",\"a\":99,\"b\":91},{\"tag\":\"incompatible\",\"a\":99,\"b\":92},{\"tag\":\"incompatible\",\"a\":99,\"b\":96},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[9,15,16]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[9,15,67]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[9,16,65]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[9,50,65]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[9,65,67]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[15,16,56]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[15,16,59]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[15,50,54]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[15,50,67]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[15,59,67]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[16,56,65]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[16,59,65]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[50,56,65]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[59,65,67]},{\"tag\":\"mate\",\"ridge\":73,\"a\":9,\"owners\":[19,69,71,74,75,76]},{\"tag\":\"mate\",\"ridge\":73,\"a\":19,\"owners\":[9,54,56,59,60,61]},{\"tag\":\"mate\",\"ridge\":73,\"a\":54,\"owners\":[19,71,74,75,76]},{\"tag\":\"mate\",\"ridge\":73,\"a\":56,\"owners\":[19,69,74,75,76]},{\"tag\":\"mate\",\"ridge\":73,\"a\":59,\"owners\":[19,69,71,75,76]},{\"tag\":\"mate\",\"ridge\":73,\"a\":60,\"owners\":[19,69,71,74,76]},{\"tag\":\"mate\",\"ridge\":73,\"a\":69,\"owners\":[9,56,59,60,61]},{\"tag\":\"mate\",\"ridge\":73,\"a\":71,\"owners\":[9,54,59,60,61]},{\"tag\":\"mate\",\"ridge\":73,\"a\":74,\"owners\":[9,54,56,60,61]},{\"tag\":\"mate\",\"ridge\":73,\"a\":75,\"owners\":[9,54,56,59,61]},{\"tag\":\"mate\",\"ridge\":73,\"a\":76,\"owners\":[9,54,56,59,60]},{\"tag\":\"mate\",\"ridge\":74,\"a\":9,\"owners\":[31,85,87,90,91,92]},{\"tag\":\"mate\",\"ridge\":74,\"a\":31,\"owners\":[9,54,56,59,60,61]},{\"tag\":\"mate\",\"ridge\":74,\"a\":54,\"owners\":[31,87,90,91,92]},{\"tag\":\"mate\",\"ridge\":74,\"a\":56,\"owners\":[31,85,90,91,92]},{\"tag\":\"mate\",\"ridge\":74,\"a\":59,\"owners\":[31,85,87,91,92]},{\"tag\":\"mate\",\"ridge\":74,\"a\":85,\"owners\":[9,56,59,60,61]},{\"tag\":\"mate\",\"ridge\":74,\"a\":87,\"owners\":[9,54,59,60,61]},{\"tag\":\"mate\",\"ridge\":74,\"a\":90,\"owners\":[9,54,56,60,61]},{\"tag\":\"mate\",\"ridge\":74,\"a\":91,\"owners\":[9,54,56,59,61]},{\"tag\":\"mate\",\"ridge\":74,\"a\":92,\"owners\":[9,54,56,59,60]},{\"tag\":\"mate\",\"ridge\":321,\"a\":25,\"owners\":[15,60,65,68]},{\"tag\":\"mate\",\"ridge\":321,\"a\":75,\"owners\":[15,65,68]},{\"tag\":\"mate\",\"ridge\":321,\"a\":80,\"owners\":[15,60,68]},{\"tag\":\"mate\",\"ridge\":321,\"a\":83,\"owners\":[15,60,65]},{\"tag\":\"mate\",\"ridge\":322,\"a\":37,\"owners\":[15,60,65,68]},{\"tag\":\"mate\",\"ridge\":322,\"a\":91,\"owners\":[15,65,68]},{\"tag\":\"mate\",\"ridge\":322,\"a\":96,\"owners\":[15,60,68]},{\"tag\":\"mate\",\"ridge\":322,\"a\":99,\"owners\":[15,60,65]},{\"tag\":\"mate\",\"ridge\":577,\"a\":16,\"owners\":[26,76,82,83]},{\"tag\":\"mate\",\"ridge\":577,\"a\":26,\"owners\":[16,61,67,68]},{\"tag\":\"mate\",\"ridge\":577,\"a\":67,\"owners\":[26,76,83]},{\"tag\":\"mate\",\"ridge\":577,\"a\":76,\"owners\":[16,67,68]},{\"tag\":\"mate\",\"ridge\":577,\"a\":82,\"owners\":[16,61,68]},{\"tag\":\"mate\",\"ridge\":577,\"a\":83,\"owners\":[16,61,67]},{\"tag\":\"mate\",\"ridge\":578,\"a\":38,\"owners\":[16,61,67,68]},{\"tag\":\"mate\",\"ridge\":578,\"a\":92,\"owners\":[16,67,68]},{\"tag\":\"mate\",\"ridge\":578,\"a\":98,\"owners\":[16,61,68]},{\"tag\":\"mate\",\"ridge\":578,\"a\":99,\"owners\":[16,61,67]},{\"tag\":\"mate\",\"ridge\":76,\"a\":31,\"owners\":[19,69,71,74,75,76]},{\"tag\":\"mate\",\"ridge\":76,\"a\":71,\"owners\":[31,85,90,91,92]},{\"tag\":\"mate\",\"ridge\":76,\"a\":74,\"owners\":[31,85,87,91,92]},{\"tag\":\"mate\",\"ridge\":76,\"a\":85,\"owners\":[19,71,74,75,76]},{\"tag\":\"mate\",\"ridge\":76,\"a\":87,\"owners\":[19,69,74,75,76]},{\"tag\":\"mate\",\"ridge\":76,\"a\":90,\"owners\":[19,69,71,75,76]},{\"tag\":\"mate\",\"ridge\":76,\"a\":91,\"owners\":[19,69,71,74,76]},{\"tag\":\"mate\",\"ridge\":76,\"a\":92,\"owners\":[19,69,71,74,75]},{\"tag\":\"mate\",\"ridge\":324,\"a\":96,\"owners\":[25,75,83]},{\"tag\":\"mate\",\"ridge\":580,\"a\":38,\"owners\":[26,76,82,83]},{\"tag\":\"mate\",\"ridge\":580,\"a\":92,\"owners\":[26,82,83]},{\"tag\":\"mate\",\"ridge\":580,\"a\":98,\"owners\":[26,76,83]},{\"tag\":\"mate\",\"ridge\":580,\"a\":99,\"owners\":[26,76,82]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[43,54,55,56,57,59,60],\"full_literals\":[-39,10,12,13,14,15,16,17]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[50,68,83,99],\"full_literals\":[-40,11,21,30,38]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":83,\"full_literals\":[-30,40]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":99,\"full_literals\":[-38,40]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[65,69,80,96],\"full_literals\":[-41,19,22,28,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":10,\"members\":[70,71,74,75],\"full_literals\":[-42,23,24,25,26]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-43,39,40],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-44,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-45,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-46,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-47,false,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-48,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-49,41,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-49,false,42],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-50,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":3,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-51,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":6,\"direction\":\"backward\",\"full_literals\":[-52,47,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-52,48,51],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true},{\"tag\":\"edge\",\"edge\":26,\"owners\":[9,19,31,54,56,59,60,61,69,71,74,75,76,85,87,90,91,92]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[15,25,37,60,65,68,75,80,83,91,96,99]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[16,26,38,61,67,68,76,82,83,92,98,99]}]}"
  "p cnf 52 145\n-15 -1 0\n-16 -1 0\n-16 -11 0\n-16 -14 0\n-17 -3 0\n-17 -11 0\n-17 -16 0\n-18 -2 0\n-18 -17 0\n-19 -10 0\n-19 -12 0\n-19 -13 0\n-19 -17 0\n-19 -18 0\n-20 -14 0\n-20 -17 0\n-21 -1 0\n-21 -12 0\n-21 -14 0\n-21 -16 0\n-21 -17 0\n-21 -18 0\n-21 -19 0\n-21 -20 0\n-22 -12 0\n-23 -22 0\n-24 -22 0\n-25 -11 0\n-26 -4 0\n-26 -6 0\n-26 -22 0\n-27 -5 0\n-27 -26 0\n-28 -12 0\n-28 -23 0\n-28 -26 0\n-28 -27 0\n-29 -14 0\n-29 -26 0\n-30 -4 0\n-30 -22 0\n-30 -24 0\n-30 -25 0\n-30 -26 0\n-30 -27 0\n-30 -28 0\n-33 -16 0\n-36 -12 0\n-37 -14 0\n-38 -7 0\n-38 -11 0\n-38 -31 0\n-38 -32 0\n-38 -33 0\n-38 -34 0\n-38 -35 0\n-38 -36 0\n-1 -2 -3 0\n-1 -2 -20 0\n-1 -3 -19 0\n-1 -11 -19 0\n-1 -19 -20 0\n-2 -3 -14 0\n-2 -3 -16 0\n-2 -11 -12 0\n-2 -11 -20 0\n-2 -16 -20 0\n-3 -14 -19 0\n-3 -16 -19 0\n-11 -14 -19 0\n-16 -19 -20 0\n-1 4 22 24 25 26 27 0\n-4 1 12 14 16 17 18 0\n-12 4 24 25 26 27 0\n-14 4 22 25 26 27 0\n-16 4 22 24 26 27 0\n-17 4 22 24 25 27 0\n-22 1 14 16 17 18 0\n-24 1 12 16 17 18 0\n-25 1 12 14 17 18 0\n-26 1 12 14 16 18 0\n-27 1 12 14 16 17 0\n-1 7 31 32 33 34 35 0\n-7 1 12 14 16 17 18 0\n-12 7 32 33 34 35 0\n-14 7 31 33 34 35 0\n-16 7 31 32 34 35 0\n-31 1 14 16 17 18 0\n-32 1 12 16 17 18 0\n-33 1 12 14 17 18 0\n-34 1 12 14 16 18 0\n-35 1 12 14 16 17 0\n-5 2 17 19 21 0\n-26 2 19 21 0\n-28 2 17 21 0\n-30 2 17 19 0\n-8 2 17 19 21 0\n-34 2 19 21 0\n-36 2 17 21 0\n-38 2 17 19 0\n-3 6 27 29 30 0\n-6 3 18 20 21 0\n-20 6 27 30 0\n-27 3 20 21 0\n-29 3 18 21 0\n-30 3 18 20 0\n-9 3 18 20 21 0\n-35 3 20 21 0\n-37 3 18 21 0\n-38 3 18 20 0\n-7 4 22 24 25 26 27 0\n-24 7 31 33 34 35 0\n-25 7 31 32 34 35 0\n-31 4 24 25 26 27 0\n-32 4 22 25 26 27 0\n-33 4 22 24 26 27 0\n-34 4 22 24 25 27 0\n-35 4 22 24 25 26 0\n-36 5 26 30 0\n-9 6 27 29 30 0\n-35 6 29 30 0\n-37 6 27 30 0\n-38 6 27 29 0\n-39 10 12 13 14 15 16 17 0\n-40 11 21 30 38 0\n-30 40 0\n-38 40 0\n-41 19 22 28 36 0\n-42 23 24 25 26 0\n-43 39 40 0\n-44 40 0\n-45 43 0\n-46 44 0\n-47 45 0\n-48 46 0\n-49 41 0\n-49 42 0\n-50 49 0\n-51 50 0\n-52 47 0\n-52 48 51 0\n52 0\n1 4 7 12 14 16 17 18 22 24 25 26 27 31 32 33 34 35 0\n2 5 8 17 19 21 26 28 30 34 36 38 0\n3 6 9 18 20 21 27 29 30 35 37 38 0\n"
  "146 47 0 142 140 0\n147 45 0 146 134 0\n148 43 0 147 132 0\n149 -17 3 -40 0 6 9 16 21 106 110 125 0\n150 -21 18 14 25 17 1 4 0 18 20 82 81 90 79 89 84 92 78 91 88 143 0\n151 -21 17 18 0 17 18 19 20 73 80 150 0\n152 16 12 25 1 14 17 18 0 90 92 91 78 88 82 81 79 89 84 73 143 0\n153 27 24 22 4 -16 21 18 0 76 30 39 44 101 120 103 122 121 123 145 0\n154 -27 22 19 -41 0 32 33 37 45 119 128 0\n155 -24 33 21 11 -40 0 42 125 50 52 55 56 112 0\n156 22 4 24 -16 21 19 18 -41 0 154 153 0\n157 -22 24 25 -42 0 26 31 129 0\n158 12 25 1 14 17 19 18 11 -40 -49 0 151 137 136 90 152 155 157 156 29 40 129 125 35 57 128 0\n159 -12 19 -41 0 25 34 48 128 0\n160 1 14 17 19 18 11 -40 -49 0 136 159 80 158 0\n161 -28 25 21 11 -40 -42 0 35 36 46 129 125 155 54 0\n162 25 36 21 19 11 -40 -49 0 137 136 161 128 27 157 0\n163 -17 -40 0 5 149 0\n164 20 3 18 11 -40 0 163 151 110 106 125 0\n165 2 19 38 34 30 26 21 17 0 95 99 93 97 144 0\n166 -11 -19 0 14 13 11 3 28 70 61 152 0\n167 1 14 16 -19 0 14 13 11 80 152 0\n168 14 16 -19 0 148 166 14 13 12 11 10 167 1 60 62 124 164 130 0\n169 -14 -19 0 23 14 15 38 49 68 104 108 110 102 107 106 145 0\n170 -19 0 14 23 169 168 69 71 105 109 104 108 110 102 107 106 145 0\n171 20 3 38 30 21 18 0 109 105 104 108 102 107 145 0\n172 2 38 30 21 17 0 170 94 98 165 0\n173 -16 18 -49 0 170 2 3 4 7 20 160 126 127 172 64 67 171 0\n174 38 30 21 20 16 18 12 0 171 5 172 63 58 80 152 0\n175 -38 21 -49 0 170 50 51 52 53 55 56 57 127 113 162 0\n176 26 7 1 4 31 34 14 18 12 22 25 24 27 35 32 16 33 0 143 77 0\n177 -30 16 18 12 0 40 41 42 43 44 45 117 118 115 111 114 75 116 72 176 0\n178 -17 20 30 18 0 5 21 110 171 0\n179 20 18 -49 0 170 136 159 173 177 178 151 175 174 0\n180 18 -49 0 170 136 159 173 177 179 15 16 24 175 172 59 80 152 0\n181 -18 0 170 8 9 22 100 96 172 0\n182 -49 0 181 180 0\n183 -50 0 182 138 0\n184 -51 0 183 139 0\n185 48 0 184 142 141 0\n186 46 0 185 135 0\n187 44 0 186 133 0\n188 40 0 187 131 0\n189 -17 0 188 163 0\n190 -21 0 189 181 151 0\n191 -38 12 16 0 181 189 50 52 53 54 55 56 113 86 83 152 0\n192 38 12 16 30 0 188 190 189 181 174 172 125 66 0\n193 12 16 0 181 177 191 192 0\n194 38 30 -12 0 189 190 188 172 125 65 0\n195 -38 -12 0 50 53 54 55 56 85 0\n196 38 -12 0 194 40 42 43 44 45 74 0\n197 -12 0 195 196 0\n198 16 0 197 193 0\n199 -11 0 198 3 0\n200 -33 0 198 47 0\n201 -24 0 200 190 199 188 155 0\n202 -30 0 181 190 198 201 40 41 45 153 0\n203 38 0 202 188 199 190 125 0\n204 -7 0 203 50 0\n205 -31 0 203 52 0\n206 -32 0 203 53 0\n207 -34 0 203 55 0\n208 -35 0 203 56 0\n209 0 204 207 206 205 198 208 87 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00025.record045
