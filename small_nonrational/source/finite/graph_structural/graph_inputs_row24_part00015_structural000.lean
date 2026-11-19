module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00015Data
public import GraphInputsRow24Part00015Frames
public import GraphInputsRow24Part00015Leaves
public import GraphInputsRow24Part00015Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record013
def vertexColumn : Fields := ⟨10, hexnat% "34c2f1ca6a99a2eb462d94e2b86e2785e0fb49725a9667452d70d9354d2b46d2745de0dc368d9362d4b32d2b2ac6b46c9b16c3bc1d4789ca719e1725c5743c8f13c2f07cb80f3422ca460db412c589524a926439914351342d0770360e4350ca324c3381c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "d36d24db6d24924d249249249b4da69249249b491249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "228208f0c94fce0000000", hexnat% "113000010000000000", hexnat% "e0000000000000000", hexnat% "10000000020000000000", 67553994410557440]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "202688fc9740e0000000", hexnat% "181000000000000000", hexnat% "208000200000800000000", hexnat% "10010000000000000000", 2666130979403333632, 773094113280]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "202682fc9708e0000000", hexnat% "181000000000000000", hexnat% "208000800004000000000", hexnat% "10010000000000000000", 2666130979403333632, 773094113280]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "208068ff8944860000000", hexnat% "20200004000080000000", hexnat% "10011000030000000000", hexnat% "180000000000000000", 773094113280, 2305843009213693952]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e0a08900060000000", hexnat% "10011000030000000000", 2666130981550817280, 67553994410557440, hexnat% "228208000040000000000", hexnat% "100004000000000000", 1082331758592]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c5 c3
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c6 c2
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c7 c1
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c8 c0
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record013_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record013

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record017
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record017
def vertexColumn : Fields := ⟨10, hexnat% "31c66a6639b1695a36338ae47bc1e86e1c65993971595635c34cd2b61d4774370f2368e63c4d9394e3332cab26f0791cc789ca785d1715c3743c8f13c2f990e26291a1981e984e1c458946645894658541d60cc328c6344d0b22c1b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "34936db4da49249b6934d249b493492492492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "808d060c20fb0000000", hexnat% "12001000000000000", 864691815649902592, hexnat% "6000000000000000000", 2828288577765376]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "201200b0cd770000000", hexnat% "4000000802800000000", 2035627031571464192, hexnat% "8080000020080000000", 13835128424026341376, 9007199254740992]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "201200b0c7770000000", hexnat% "4000000808800000000", 2035627031571464192, hexnat% "8080000020080000000", 13835128424026341376, 9007199254740992]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4012c0180ff30000000", hexnat% "2000000000040000000", 10403315139225845760, hexnat% "8080000020080000000", 2898312650817536, 4611686018427387904]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "201200b0ed7f0000000", hexnat% "8080000000000000000", 13835269161514696704, hexnat% "4000000002800000000", 2035627031571464192, 9007199254740992]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1200100d440000000", hexnat% "6000000000000000000", 2900511674073088, hexnat% "8080000000080000000", 2035627065931202560, 13844205992025260032, 151129161728]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record017_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record017_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record017_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record017_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record017_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record017_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record017_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record017_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record017_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record017

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record021
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record021
def vertexColumn : Fields := ⟨10, hexnat% "dcf0b4a72b2a9a99a36a66358b6638ce1b89e17bc1d25c9ca669664d9994d52d58d3346d2745de0f43b0dc3c8e6364cd38ccb3c2d8b92d4b32e2b4ac6b46c9b16d8791e2729c6715d0f23c3c0e8c6258361382e07839314950d44d0b41dc0d8390cc388c930cd0b12c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6d26924db6db693492492492492492492492492449249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5000a7ffffff80000000", 576460752303423488, hexnat% "20004000000000000000", hexnat% "100020000000000000000", hexnat% "208041000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7000e17d7fc780000000", hexnat% "100020000000800000000", 901282875427520512, hexnat% "208041000000000000000", 206158430208, 144255925564211200]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "378049ff7ffff80000000", 2251799813685248, 6917529027641081856, hexnat% "20000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24806fff7ffff80000000", 2251799813685248, hexnat% "30000000000000000000", hexnat% "100000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "48009fffffbf80000000", hexnat% "200040000004000000000", hexnat% "20004000000000000000", hexnat% "100020000000000000000", hexnat% "10002000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37804f7d0e7bf80000000", hexnat% "20004000000000000", 2278188092751872, 586312651366203392]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "480087d8ffbe80000000", hexnat% "20004000000100000000", hexnat% "100020004000000000000", 586312651366203392, hexnat% "200041000000000000000", hexnat% "10002000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "300060b37216f80000000", hexnat% "5000a000000000000000", 244641337180160, 5764607523034234880, hexnat% "28000000000000000000", 344525440213319680]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5000aff3efe780000000", hexnat% "20004000000000000000", 3395394985787392, hexnat% "61000000000000000", hexnat% "308000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100020004216a00000000", hexnat% "20004040040400000000", 326528633889882112, 806144333299318784, hexnat% "5000a001000080000000", hexnat% "208041000008000000000", 785055597199360]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c17 c2
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record021_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record021_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record021_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record021_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record021_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record021_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record021_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record021_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record021_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record021

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record032
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record032
def vertexColumn : Fields := ⟨10, hexnat% "3c26c8ea3693a2eb2639b16359362da4e1b85e0fbc16c4e9365392e72539715355352d64d1b45d0f783d0ec370f2338f1334d332ce4b32d2b2ac6b46c9b16c3bc1cc789d2729c6785d1725c570de0f689929184e0b81e685919144d0b41dc0d8390cc348ca344c9312c2b06e0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "d36db6db6924d36db6db692492492492492492492492492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [323836685559267328, hexnat% "20002000000000000000", hexnat% "2000a000800000000000000", 252624066475720704, 5764607523034234880, hexnat% "50000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100017fffffff0000000", 7493989779944505344, hexnat% "68000000000000000000", hexnat% "20002000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [71634831548612608, 216594994578849792, 8646911284551352320, hexnat% "2000a000000000000000000", hexnat% "70000000000000000000", 288230925907525632]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000a007807ff19b0000000", hexnat% "70000000000000000000", 490892359383384064, 714038312960, 83316867984261120]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "70007129f3fff0000000", 492018259290226688, hexnat% "2000a000802000000000000", 13194139533312]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200020007ffff5c80000000", 701958717440, 8646911284551352320, hexnat% "78000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [359865482578231296, hexnat% "2000a000800000000000000", 216595269456756736, hexnat% "10001000000000000000", 6917529027641081856, hexnat% "60000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "78007cdf5f5ff0000000", hexnat% "20002000000000000000000", 144115875270623232, 9183121115185152, 72057594037927936]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2004a007cdf5f5ff0000000", hexnat% "30000000000000000000", 144115875270623232, 9183121115185152, 72057594037927936]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400044de7f3fe0000000", hexnat% "2000a000800000000000000", hexnat% "10001000000010000000", 216454806846308352, hexnat% "20002020000000000000", 141012366262272]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200020007fefffff0000000", hexnat% "40004001000000000000", 4035225266123964416, hexnat% "38000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "78007cbf0f7ff0000000", hexnat% "20002000000000000000000", 162130136341151744, 123145302310912, 72198331526283264]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400007ffbffff0000000", 70368744177664, 8646911284551352320, hexnat% "2000a000000000000000000", hexnat% "30000000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400004feef7ff0000000", hexnat% "2000a000800000000000000", hexnat% "10001000000000000000", 216454806846308352, 6917529027641081856, hexnat% "20000000100000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c18 c13
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400043afbf7ff0000000", 4035225266123964416, hexnat% "38000000000000000000", 310748924044378112, 70368744177664, hexnat% "20002000000000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "500057dd8ffff0000000", hexnat% "20002020100000000000", 668503069687808, hexnat% "2000a000800000000000000"]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "300035abff5dd0000000", hexnat% "40004000000000000000", 167759635875364864, hexnat% "2000a000800000020000000", 146028888064]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000a000ef66dfff0000000", 8070450532247928832, hexnat% "70000000000000000000", 72499597712293888, 2251799813685248]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [189162179197403136, 8646911284551352320, hexnat% "2000a000006000000000000", hexnat% "70000000000000000000", 310818743032741888, 200111116255232, 74590868828323840]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c25 c22
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c26 c21
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c27 c20
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c28 c19
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c29 c12
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c30 c7
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c31 c6
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c32 c5
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c33 c4
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c34 c3
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c35 c0
  c36
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record032_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record032_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record032_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record032_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record032_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record032_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record032_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record032_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record032_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record032

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record002
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2f1d26a8bad1b2659a562d8ae2785e0f9d16a4b9d1725596552d4ad2745d0f78370f2358d9394d5334cb362d2b16c3bc1d4789d2729c6785c970de0f23c4fd09a22a89a918560b81ed05a12a499914550b41dc0d8390d4348ca324c5322c2b06e0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b49369a49349369a492492492492492492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002.data.quota

def groupMembers1 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 0)]))
 (.leaf ([(facetIndex 1)])))
 (.branch 3
 (.leaf ([(facetIndex 2)]))
 (.leaf ([(facetIndex 3)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 4)]))
 (.leaf ([(facetIndex 5)])))
 (.branch 7
 (.leaf ([(facetIndex 6)]))
 (.leaf ([(facetIndex 7)])))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ([(facetIndex 8)]))
 (.leaf ([(facetIndex 9)])))
 (.branch 11
 (.leaf ([(facetIndex 10)]))
 (.leaf ([(facetIndex 11)]))))
 (.branch 14
 (.branch 13
 (.leaf ([(facetIndex 12)]))
 (.leaf ([(facetIndex 13)])))
 (.branch 15
 (.leaf ([(facetIndex 14)]))
 (.leaf ([(facetIndex 15)]))))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ([(facetIndex 16)]))
 (.leaf ([(facetIndex 17)])))
 (.branch 19
 (.leaf ([(facetIndex 18)]))
 (.leaf ([(facetIndex 19)]))))
 (.branch 22
 (.branch 21
 (.leaf ([(facetIndex 20)]))
 (.leaf ([(facetIndex 21)])))
 (.branch 23
 (.leaf ([(facetIndex 22)]))
 (.leaf ([(facetIndex 23)])))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ([(facetIndex 24)]))
 (.leaf ([(facetIndex 25)])))
 (.branch 27
 (.leaf ([(facetIndex 26)]))
 (.leaf ([(facetIndex 27)]))))
 (.branch 30
 (.branch 29
 (.leaf ([(facetIndex 28)]))
 (.leaf ([(facetIndex 29)])))
 (.branch 31
 (.leaf ([(facetIndex 30)]))
 (.leaf ([(facetIndex 31)])))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨5, sparse_nat% "ffbbcdeb38bdab49ca307b9ac5a928398a418820"⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 32
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 40), (facetIndex 42), (facetIndex 43), (facetIndex 65), (facetIndex 77)]))
 (.leaf ([(facetIndex 39), (facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 67), (facetIndex 79)])))
 (.branch 3
 (.leaf ([(facetIndex 32), (facetIndex 37), (facetIndex 38), (facetIndex 51), (facetIndex 62), (facetIndex 74)]))
 (.leaf ([(facetIndex 35), (facetIndex 36), (facetIndex 45), (facetIndex 58), (facetIndex 70)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 50), (facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 56)]))
 (.leaf ([(facetIndex 33), (facetIndex 44), (facetIndex 59), (facetIndex 60), (facetIndex 71), (facetIndex 72)])))
 (.branch 7
 (.leaf ([(facetIndex 49)]))
 (.branch 8
 (.leaf ([(facetIndex 34), (facetIndex 41)]))
 (.leaf ([(facetIndex 57), (facetIndex 66), (facetIndex 69), (facetIndex 78)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "180002055380180002055384444424611135007012233752z20;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 61)]))
 (.branch 2
 (.leaf ([(facetIndex 68)]))
 (.leaf ([(facetIndex 73)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 80)]))
 (.leaf ([(facetIndex 81)])))
 (.branch 6
 (.leaf ([(facetIndex 63), (facetIndex 64)]))
 (.leaf ([(facetIndex 75), (facetIndex 76)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "23006c10001005az2f;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped1_0000 : List Nat := [6]
def grouped1_0001 : List Nat := [6, 7]
def grouped1_0002 : List Nat := [7]
def grouped2_0003 : List Nat := [0]
def grouped2_0004 : List Nat := [0, 1]
def grouped2_0005 : List Nat := [0, 1, 2, 3]
def grouped2_0007 : List Nat := [1]
def grouped2_0008 : List Nat := [2]
def grouped2_0009 : List Nat := [2, 3]
def grouped2_0010 : List Nat := [3]
def grouped2_0011 : List Nat := [4]
def grouped2_0012 : List Nat := [4, 5]
def grouped2_0013 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0014 : List Nat := [5]
def grouped2_0015 : List Nat := [6]
def grouped2_0016 : List Nat := [6, 7, 8]
def grouped2_0017 : List Nat := [7]
def grouped2_0018 : List Nat := [7, 8]
def grouped2_0019 : List Nat := [8]
def grouped3_0020 : List Nat := [0]
def grouped3_0021 : List Nat := [0, 1, 2]
def grouped3_0023 : List Nat := [1]
def grouped3_0024 : List Nat := [1, 2]
def grouped3_0025 : List Nat := [2]
def grouped3_0026 : List Nat := [3]
def grouped3_0027 : List Nat := [3, 4]
def grouped3_0028 : List Nat := [3, 4, 5, 6]
def grouped3_0029 : List Nat := [4]
def grouped3_0030 : List Nat := [5]
def grouped3_0031 : List Nat := [5, 6]
def grouped3_0032 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record002" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"group\",\"kind\":1,\"index\":6},{\"tag\":\"group\",\"kind\":1,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0005\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0018\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0016\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0016\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0027\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0027\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0031\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record002" 106

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record002" "{\"ridges\":[[6,11],[6,35],[7,131],[10,131],[11,259],[12,259],[14,131],[14,259],[15,259],[17,13],[17,37],[22,289],[22,385],[23,321],[25,14],[25,38],[30,290],[30,386],[31,322],[34,11],[34,13],[34,14],[41,35],[41,515],[43,259],[46,259],[47,259],[49,131],[50,259],[52,259],[53,321],[56,131],[56,385],[56,386],[56,770],[58,13],[60,37],[65,321],[65,517],[65,769],[67,289],[67,385],[68,321],[68,385],[68,464],[71,14],[72,38],[77,322],[77,770],[77,832],[79,290],[79,386],[80,386],[80,464],[81,180]],\"owners\":[[6,11,[0,5,7,32,34,45,47],[46]],[34,11,[5,6,7,45,46,47],[0,32]],[6,35,[2,10,11,35,38,41,48,53,54],[44]],[41,35,[6,10,11,44,48,53],[2,35,38,54]],[17,37,[2,35,38,39,40,41,61,63,64],[57,60]],[60,37,[2,35,38,40,41,63,64],[17,39,57,61]],[25,38,[2,35,38,39,40,41,73,75,76],[69,72]],[72,38,[2,35,38,40,41,75,76],[25,39,69,73]],[41,515,[13,15,51,56],[4,34,37,54]],[65,517,[4,34,37,41],[19,43,62,64]],[49,131,[7,10,14,33,39,56],[9,36,55]],[22,289,[11,40,46,53,54,63,64],[67]],[67,289,[11,40,53,54,63,64],[22,46]],[30,290,[11,40,46,53,54,75,76],[79]],[79,290,[11,40,53,54,75,76],[30,46]],[23,321,[12,42,50,53,55,63,68],[65]],[65,321,[12,50,53,55,68],[23,42,63]],[31,322,[12,42,50,53,55,75,80],[77]],[77,322,[12,50,53,55,80],[31,42,75]],[22,385,[14,47,52,55,56,68],[67]],[67,385,[14,52,55,56,68],[22,47]],[30,386,[14,47,52,55,56,80],[79]],[79,386,[14,52,55,56,80],[30,47]],[65,769,[15,54,56],[23,43,64]],[56,770,[31,76,77],[15,43,54]],[77,770,[15,54,56],[31,43,76]],[77,832,[23],[31,65]],[81,180,[61,73],[]],[68,464,[80],[]],[80,464,[68],[]]],\"edges\":[[19,[2,17,25,35,38,39,40,41,57,60,61,63,64,69,72,73,75,76,81]],[37,[11,22,30,40,46,53,54,63,64,67,75,76,79]],[42,[14,22,30,47,52,55,56,67,68,79,80]]],\"groupings\":[1,2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record002" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record002\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-19,-3],[-20,-5],[-21,-2],[-21,-19],[-21,-20],[-22,-21],[-23,-21],[-24,-21],[-25,-3],[-25,-21],[-26,-5],[-26,-21],[-27,-5],[-27,-8],[-27,-21],[-28,-1],[-28,-19],[-28,-21],[-28,-27],[-29,-21],[-29,-28],[-30,-21],[-30,-28],[-31,-21],[-33,-27],[-33,-28],[-36,-4],[-36,-22],[-36,-23],[-36,-24],[-36,-29],[-36,-31],[-36,-32],[-36,-34],[-36,-35],[-37,-36],[-39,-36],[-39,-37],[-40,-11],[-40,-12],[-40,-27],[-40,-30],[-41,-9],[-41,-11],[-41,-12],[-41,-26],[-41,-27],[-41,-28],[-41,-30],[-41,-37],[-41,-40],[-42,-12],[-42,-27],[-42,-30],[-42,-36],[-42,-41],[-43,-8],[-43,-9],[-43,-11],[-43,-27],[-43,-30],[-43,-33],[-43,-37],[-43,-40],[-43,-41],[-43,-42],[-44,-21],[-46,-45],[-48,-45],[-52,-10],[-52,-38],[-52,-49],[-52,-50],[-52,-51],[-53,-48],[-55,-36],[-55,-37],[-55,-39],[-55,-42],[-56,-21],[-60,-20],[-60,-47],[-60,-53],[-60,-58],[-60,-59],[-61,-57],[-62,-40],[-62,-52],[-63,-28],[-63,-52],[-64,-10],[-64,-38],[-64,-50],[-64,-51],[-64,-62],[-64,-63],[-65,-48],[-65,-60],[-67,-36],[-68,-58],[-5,1,4,6,19,21,32,34],[-21,4,5,6,32,33,34],[-13,-21,-45],[-16,-21,-58],[-5,2,7,8,22,25,28,35,40,41],[-28,5,7,8,31,35,40],[-13,2,22,25,26,27,28,48,50,51],[-47,2,22,25,27,28,50,51],[-16,2,22,25,26,27,28,60,62,63],[-59,2,22,25,27,28,62,63],[-28,10,12,38,43],[-52,3,21,24,28],[-36,6,7,11,20,26,43],[-6,-11,-36],[-6,-36,-43],[-7,-11,-36],[-7,-36,-43],[-8,-9,-11],[-8,-11,-30],[-8,-12,-37],[-9,-11,-12],[-9,-11,-33],[-9,-12,-34],[-9,-12,-39],[-11,-12,-37],[-11,-30,-33],[-12,-33,-37],[-12,-34,-37],[-14,8,27,33,40,41,50,51],[-54,8,27,40,41,50,51],[-17,8,27,33,40,41,62,63],[-66,8,27,40,41,62,63],[-15,9,29,37,40,42,50,55],[-52,9,37,40,42,55],[-40,-52,-55],[-18,9,29,37,40,42,62,67],[-64,9,37,40,42,67],[-14,11,34,39,42,43,55],[-54,11,39,42,43,55],[-14,-43,-55],[-43,-54,-55],[-17,11,34,39,42,43,67],[-66,11,39,42,43,67],[-17,-43,-67],[-43,-66,-67],[-52,12,41,43],[-43,18,63,64],[-64,12,41,43],[-64,15],[-68,48,60],[-55,67],[-67,55],[-69,5],[-5,69],[-70,6],[-6,70],[-71,69,70],[-70,71],[-69,71],[-72,27,29,30,52,64],[-64,72],[-73,19,24,25,38,49,61],[-74,22,23,32,45,57],[-75,37,39,40,41,42,43],[-43,75],[-76,20,31,46,47,58,59],[-77,36],[-78,21,28],[-79,44,53,56,65],[-80,72],[-81,73],[-81,74],[-82,80],[-82,81],[-83,75],[-83,76],[-84,78],[-84,79],[-85,77,84],[-86,77],[-86,84],[-87,83,86],[-88,83],[-87,85],[-88,86],[-89,82,88],[-89,87],[89],[-90,48],[-48,90],[-91,55],[-55,91],[-92,60],[-60,92],[-93,67],[-67,93],[-94,68],[-68,94],[-95,50,51],[-96,62,63],[-62,96],[-63,96],[-97,91,92],[-92,97],[-91,97],[-98,90,97],[-97,98],[-90,98],[-90,-97,99],[-100,93,94],[-93,100],[-93,-94,101],[-102,95],[-102,96],[-104,100,102],[-100,103],[-101,104],[-105,98,104],[-98,-104,106],[-99,-103,106],[105],[-106],[2,13,16,22,25,26,27,28,44,47,48,50,51,56,59,60,62,63,68],[8,14,17,27,33,40,41,50,51,54,62,63,66],[11,14,17,34,39,42,43,54,55,66,67]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"group\",\"index\":6,\"kind\":1},{\"tag\":\"group\",\"index\":7,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":32,\"b\":4},{\"tag\":\"incompatible\",\"a\":33,\"b\":6},{\"tag\":\"incompatible\",\"a\":34,\"b\":2},{\"tag\":\"incompatible\",\"a\":34,\"b\":32},{\"tag\":\"incompatible\",\"a\":34,\"b\":33},{\"tag\":\"incompatible\",\"a\":35,\"b\":34},{\"tag\":\"incompatible\",\"a\":36,\"b\":34},{\"tag\":\"incompatible\",\"a\":37,\"b\":34},{\"tag\":\"incompatible\",\"a\":38,\"b\":4},{\"tag\":\"incompatible\",\"a\":38,\"b\":34},{\"tag\":\"incompatible\",\"a\":39,\"b\":6},{\"tag\":\"incompatible\",\"a\":39,\"b\":34},{\"tag\":\"incompatible\",\"a\":40,\"b\":6},{\"tag\":\"incompatible\",\"a\":40,\"b\":11},{\"tag\":\"incompatible\",\"a\":40,\"b\":34},{\"tag\":\"incompatible\",\"a\":41,\"b\":0},{\"tag\":\"incompatible\",\"a\":41,\"b\":32},{\"tag\":\"incompatible\",\"a\":41,\"b\":34},{\"tag\":\"incompatible\",\"a\":41,\"b\":40},{\"tag\":\"incompatible\",\"a\":42,\"b\":34},{\"tag\":\"incompatible\",\"a\":42,\"b\":41},{\"tag\":\"incompatible\",\"a\":43,\"b\":34},{\"tag\":\"incompatible\",\"a\":43,\"b\":41},{\"tag\":\"incompatible\",\"a\":44,\"b\":34},{\"tag\":\"incompatible\",\"a\":46,\"b\":40},{\"tag\":\"incompatible\",\"a\":46,\"b\":41},{\"tag\":\"incompatible\",\"a\":49,\"b\":5},{\"tag\":\"incompatible\",\"a\":49,\"b\":35},{\"tag\":\"incompatible\",\"a\":49,\"b\":36},{\"tag\":\"incompatible\",\"a\":49,\"b\":37},{\"tag\":\"incompatible\",\"a\":49,\"b\":42},{\"tag\":\"incompatible\",\"a\":49,\"b\":44},{\"tag\":\"incompatible\",\"a\":49,\"b\":45},{\"tag\":\"incompatible\",\"a\":49,\"b\":47},{\"tag\":\"incompatible\",\"a\":49,\"b\":48},{\"tag\":\"incompatible\",\"a\":50,\"b\":49},{\"tag\":\"incompatible\",\"a\":52,\"b\":49},{\"tag\":\"incompatible\",\"a\":52,\"b\":50},{\"tag\":\"incompatible\",\"a\":53,\"b\":14},{\"tag\":\"incompatible\",\"a\":53,\"b\":15},{\"tag\":\"incompatible\",\"a\":53,\"b\":40},{\"tag\":\"incompatible\",\"a\":53,\"b\":43},{\"tag\":\"incompatible\",\"a\":54,\"b\":12},{\"tag\":\"incompatible\",\"a\":54,\"b\":14},{\"tag\":\"incompatible\",\"a\":54,\"b\":15},{\"tag\":\"incompatible\",\"a\":54,\"b\":39},{\"tag\":\"incompatible\",\"a\":54,\"b\":40},{\"tag\":\"incompatible\",\"a\":54,\"b\":41},{\"tag\":\"incompatible\",\"a\":54,\"b\":43},{\"tag\":\"incompatible\",\"a\":54,\"b\":50},{\"tag\":\"incompatible\",\"a\":54,\"b\":53},{\"tag\":\"incompatible\",\"a\":55,\"b\":15},{\"tag\":\"incompatible\",\"a\":55,\"b\":40},{\"tag\":\"incompatible\",\"a\":55,\"b\":43},{\"tag\":\"incompatible\",\"a\":55,\"b\":49},{\"tag\":\"incompatible\",\"a\":55,\"b\":54},{\"tag\":\"incompatible\",\"a\":56,\"b\":11},{\"tag\":\"incompatible\",\"a\":56,\"b\":12},{\"tag\":\"incompatible\",\"a\":56,\"b\":14},{\"tag\":\"incompatible\",\"a\":56,\"b\":40},{\"tag\":\"incompatible\",\"a\":56,\"b\":43},{\"tag\":\"incompatible\",\"a\":56,\"b\":46},{\"tag\":\"incompatible\",\"a\":56,\"b\":50},{\"tag\":\"incompatible\",\"a\":56,\"b\":53},{\"tag\":\"incompatible\",\"a\":56,\"b\":54},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":57,\"b\":34},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":61,\"b\":58},{\"tag\":\"incompatible\",\"a\":65,\"b\":13},{\"tag\":\"incompatible\",\"a\":65,\"b\":51},{\"tag\":\"incompatible\",\"a\":65,\"b\":62},{\"tag\":\"incompatible\",\"a\":65,\"b\":63},{\"tag\":\"incompatible\",\"a\":65,\"b\":64},{\"tag\":\"incompatible\",\"a\":66,\"b\":61},{\"tag\":\"incompatible\",\"a\":68,\"b\":49},{\"tag\":\"incompatible\",\"a\":68,\"b\":50},{\"tag\":\"incompatible\",\"a\":68,\"b\":52},{\"tag\":\"incompatible\",\"a\":68,\"b\":55},{\"tag\":\"incompatible\",\"a\":69,\"b\":34},{\"tag\":\"incompatible\",\"a\":73,\"b\":33},{\"tag\":\"incompatible\",\"a\":73,\"b\":60},{\"tag\":\"incompatible\",\"a\":73,\"b\":66},{\"tag\":\"incompatible\",\"a\":73,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"incompatible\",\"a\":74,\"b\":70},{\"tag\":\"incompatible\",\"a\":75,\"b\":53},{\"tag\":\"incompatible\",\"a\":75,\"b\":65},{\"tag\":\"incompatible\",\"a\":76,\"b\":41},{\"tag\":\"incompatible\",\"a\":76,\"b\":65},{\"tag\":\"incompatible\",\"a\":77,\"b\":13},{\"tag\":\"incompatible\",\"a\":77,\"b\":51},{\"tag\":\"incompatible\",\"a\":77,\"b\":63},{\"tag\":\"incompatible\",\"a\":77,\"b\":64},{\"tag\":\"incompatible\",\"a\":77,\"b\":75},{\"tag\":\"incompatible\",\"a\":77,\"b\":76},{\"tag\":\"incompatible\",\"a\":78,\"b\":61},{\"tag\":\"incompatible\",\"a\":78,\"b\":73},{\"tag\":\"incompatible\",\"a\":80,\"b\":49},{\"tag\":\"incompatible\",\"a\":81,\"b\":71},{\"tag\":\"mate\",\"ridge\":11,\"a\":6,\"owners\":[0,5,7,32,34,45,47]},{\"tag\":\"mate\",\"ridge\":11,\"a\":34,\"owners\":[5,6,7,45,46,47]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[17,34,58]},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[25,34,71]},{\"tag\":\"mate\",\"ridge\":35,\"a\":6,\"owners\":[2,10,11,35,38,41,48,53,54]},{\"tag\":\"mate\",\"ridge\":35,\"a\":41,\"owners\":[6,10,11,44,48,53]},{\"tag\":\"mate\",\"ridge\":37,\"a\":17,\"owners\":[2,35,38,39,40,41,61,63,64]},{\"tag\":\"mate\",\"ridge\":37,\"a\":60,\"owners\":[2,35,38,40,41,63,64]},{\"tag\":\"mate\",\"ridge\":38,\"a\":25,\"owners\":[2,35,38,39,40,41,73,75,76]},{\"tag\":\"mate\",\"ridge\":38,\"a\":72,\"owners\":[2,35,38,40,41,75,76]},{\"tag\":\"mate\",\"ridge\":515,\"a\":41,\"owners\":[13,15,51,56]},{\"tag\":\"mate\",\"ridge\":517,\"a\":65,\"owners\":[4,34,37,41]},{\"tag\":\"mate\",\"ridge\":131,\"a\":49,\"owners\":[7,10,14,33,39,56]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[7,14,49]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[7,49,56]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[10,14,49]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[10,49,56]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[11,12,14]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[11,14,43]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[11,15,50]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[12,14,15]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[12,14,46]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[12,15,47]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[12,15,52]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[14,15,50]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[14,43,46]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[15,46,50]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[15,47,50]},{\"tag\":\"mate\",\"ridge\":289,\"a\":22,\"owners\":[11,40,46,53,54,63,64]},{\"tag\":\"mate\",\"ridge\":289,\"a\":67,\"owners\":[11,40,53,54,63,64]},{\"tag\":\"mate\",\"ridge\":290,\"a\":30,\"owners\":[11,40,46,53,54,75,76]},{\"tag\":\"mate\",\"ridge\":290,\"a\":79,\"owners\":[11,40,53,54,75,76]},{\"tag\":\"mate\",\"ridge\":321,\"a\":23,\"owners\":[12,42,50,53,55,63,68]},{\"tag\":\"mate\",\"ridge\":321,\"a\":65,\"owners\":[12,50,53,55,68]},{\"tag\":\"three\",\"ridge\":321,\"vertices\":[53,65,68]},{\"tag\":\"mate\",\"ridge\":322,\"a\":31,\"owners\":[12,42,50,53,55,75,80]},{\"tag\":\"mate\",\"ridge\":322,\"a\":77,\"owners\":[12,50,53,55,80]},{\"tag\":\"mate\",\"ridge\":385,\"a\":22,\"owners\":[14,47,52,55,56,68]},{\"tag\":\"mate\",\"ridge\":385,\"a\":67,\"owners\":[14,52,55,56,68]},{\"tag\":\"three\",\"ridge\":385,\"vertices\":[22,56,68]},{\"tag\":\"three\",\"ridge\":385,\"vertices\":[56,67,68]},{\"tag\":\"mate\",\"ridge\":386,\"a\":30,\"owners\":[14,47,52,55,56,80]},{\"tag\":\"mate\",\"ridge\":386,\"a\":79,\"owners\":[14,52,55,56,80]},{\"tag\":\"three\",\"ridge\":386,\"vertices\":[30,56,80]},{\"tag\":\"three\",\"ridge\":386,\"vertices\":[56,79,80]},{\"tag\":\"mate\",\"ridge\":769,\"a\":65,\"owners\":[15,54,56]},{\"tag\":\"mate\",\"ridge\":770,\"a\":56,\"owners\":[31,76,77]},{\"tag\":\"mate\",\"ridge\":770,\"a\":77,\"owners\":[15,54,56]},{\"tag\":\"mate\",\"ridge\":832,\"a\":77,\"owners\":[23]},{\"tag\":\"mate\",\"ridge\":180,\"a\":81,\"owners\":[61,73]},{\"tag\":\"mate\",\"ridge\":464,\"a\":68,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":464,\"a\":80,\"owners\":[68]},{\"tag\":\"group_or\",\"kind\":1,\"index\":6,\"members\":[6],\"full_literals\":[-69,5]},{\"tag\":\"group_take\",\"kind\":1,\"index\":6,\"member\":6,\"full_literals\":[-5,69]},{\"tag\":\"group_or\",\"kind\":1,\"index\":7,\"members\":[7],\"full_literals\":[-70,6]},{\"tag\":\"group_take\",\"kind\":1,\"index\":7,\"member\":7,\"full_literals\":[-6,70]},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0002\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-71,69,70],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0002\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-70,71],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0002\",\"joined_name\":\"grouped1_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-69,false,71],\"grouped\":true,\"kind\":1},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[40,42,43,65,77],\"full_literals\":[-72,27,29,30,52,64]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":77,\"full_literals\":[-64,72]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[32,37,38,51,62,74],\"full_literals\":[-73,19,24,25,38,49,61]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[35,36,45,58,70],\"full_literals\":[-74,22,23,32,45,57]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[50,52,53,54,55,56],\"full_literals\":[-75,37,39,40,41,42,43]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":56,\"full_literals\":[-43,75]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[33,44,59,60,71,72],\"full_literals\":[-76,20,31,46,47,58,59]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[49],\"full_literals\":[-77,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[34,41],\"full_literals\":[-78,21,28]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[57,66,69,78],\"full_literals\":[-79,44,53,56,65]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-80,72,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-81,73,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-81,false,74],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0004\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0005\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-82,80,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0004\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0005\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-82,false,81],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0012\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-83,75,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-83,false,76],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0017\",\"right_name\":\"grouped2_0019\",\"joined_name\":\"grouped2_0018\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-84,78,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0017\",\"right_name\":\"grouped2_0019\",\"joined_name\":\"grouped2_0018\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-84,false,79],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0015\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0016\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-85,77,84],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0015\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0016\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-86,77,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0015\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0016\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-86,false,84],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-87,83,86],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-88,83,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0013\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-87,false,85],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0013\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-88,false,86],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-89,82,88],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-89,false,87],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[61],\"full_literals\":[-90,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":61,\"full_literals\":[-48,90]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[68],\"full_literals\":[-91,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":68,\"full_literals\":[-55,91]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[73],\"full_literals\":[-92,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":73,\"full_literals\":[-60,92]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[80],\"full_literals\":[-93,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":80,\"full_literals\":[-67,93]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[81],\"full_literals\":[-94,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":81,\"full_literals\":[-68,94]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[63,64],\"full_literals\":[-95,50,51]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[75,76],\"full_literals\":[-96,62,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":75,\"full_literals\":[-62,96]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":76,\"full_literals\":[-63,96]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-97,91,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-92,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-91,false,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-98,90,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-97,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-90,false,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-90,-97,99],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0027\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-100,93,94],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0027\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-93,false,100],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0027\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-93,-94,101],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0030\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0031\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-102,95,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0030\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0031\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-102,false,96],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-104,100,102],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-100,false,103],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0028\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-101,false,104],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-105,98,104],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-98,-104,106],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-99,-103,106],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":19,\"owners\":[2,17,25,35,38,39,40,41,57,60,61,63,64,69,72,73,75,76,81]},{\"tag\":\"edge\",\"edge\":37,\"owners\":[11,22,30,40,46,53,54,63,64,67,75,76,79]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[14,22,30,47,52,55,56,67,68,79,80]}]}"
  "p cnf 106 225\n-19 -3 0\n-20 -5 0\n-21 -2 0\n-21 -19 0\n-21 -20 0\n-22 -21 0\n-23 -21 0\n-24 -21 0\n-25 -3 0\n-25 -21 0\n-26 -5 0\n-26 -21 0\n-27 -5 0\n-27 -8 0\n-27 -21 0\n-28 -1 0\n-28 -19 0\n-28 -21 0\n-28 -27 0\n-29 -21 0\n-29 -28 0\n-30 -21 0\n-30 -28 0\n-31 -21 0\n-33 -27 0\n-33 -28 0\n-36 -4 0\n-36 -22 0\n-36 -23 0\n-36 -24 0\n-36 -29 0\n-36 -31 0\n-36 -32 0\n-36 -34 0\n-36 -35 0\n-37 -36 0\n-39 -36 0\n-39 -37 0\n-40 -11 0\n-40 -12 0\n-40 -27 0\n-40 -30 0\n-41 -9 0\n-41 -11 0\n-41 -12 0\n-41 -26 0\n-41 -27 0\n-41 -28 0\n-41 -30 0\n-41 -37 0\n-41 -40 0\n-42 -12 0\n-42 -27 0\n-42 -30 0\n-42 -36 0\n-42 -41 0\n-43 -8 0\n-43 -9 0\n-43 -11 0\n-43 -27 0\n-43 -30 0\n-43 -33 0\n-43 -37 0\n-43 -40 0\n-43 -41 0\n-43 -42 0\n-44 -21 0\n-46 -45 0\n-48 -45 0\n-52 -10 0\n-52 -38 0\n-52 -49 0\n-52 -50 0\n-52 -51 0\n-53 -48 0\n-55 -36 0\n-55 -37 0\n-55 -39 0\n-55 -42 0\n-56 -21 0\n-60 -20 0\n-60 -47 0\n-60 -53 0\n-60 -58 0\n-60 -59 0\n-61 -57 0\n-62 -40 0\n-62 -52 0\n-63 -28 0\n-63 -52 0\n-64 -10 0\n-64 -38 0\n-64 -50 0\n-64 -51 0\n-64 -62 0\n-64 -63 0\n-65 -48 0\n-65 -60 0\n-67 -36 0\n-68 -58 0\n-5 1 4 6 19 21 32 34 0\n-21 4 5 6 32 33 34 0\n-13 -21 -45 0\n-16 -21 -58 0\n-5 2 7 8 22 25 28 35 40 41 0\n-28 5 7 8 31 35 40 0\n-13 2 22 25 26 27 28 48 50 51 0\n-47 2 22 25 27 28 50 51 0\n-16 2 22 25 26 27 28 60 62 63 0\n-59 2 22 25 27 28 62 63 0\n-28 10 12 38 43 0\n-52 3 21 24 28 0\n-36 6 7 11 20 26 43 0\n-6 -11 -36 0\n-6 -36 -43 0\n-7 -11 -36 0\n-7 -36 -43 0\n-8 -9 -11 0\n-8 -11 -30 0\n-8 -12 -37 0\n-9 -11 -12 0\n-9 -11 -33 0\n-9 -12 -34 0\n-9 -12 -39 0\n-11 -12 -37 0\n-11 -30 -33 0\n-12 -33 -37 0\n-12 -34 -37 0\n-14 8 27 33 40 41 50 51 0\n-54 8 27 40 41 50 51 0\n-17 8 27 33 40 41 62 63 0\n-66 8 27 40 41 62 63 0\n-15 9 29 37 40 42 50 55 0\n-52 9 37 40 42 55 0\n-40 -52 -55 0\n-18 9 29 37 40 42 62 67 0\n-64 9 37 40 42 67 0\n-14 11 34 39 42 43 55 0\n-54 11 39 42 43 55 0\n-14 -43 -55 0\n-43 -54 -55 0\n-17 11 34 39 42 43 67 0\n-66 11 39 42 43 67 0\n-17 -43 -67 0\n-43 -66 -67 0\n-52 12 41 43 0\n-43 18 63 64 0\n-64 12 41 43 0\n-64 15 0\n-68 48 60 0\n-55 67 0\n-67 55 0\n-69 5 0\n-5 69 0\n-70 6 0\n-6 70 0\n-71 69 70 0\n-70 71 0\n-69 71 0\n-72 27 29 30 52 64 0\n-64 72 0\n-73 19 24 25 38 49 61 0\n-74 22 23 32 45 57 0\n-75 37 39 40 41 42 43 0\n-43 75 0\n-76 20 31 46 47 58 59 0\n-77 36 0\n-78 21 28 0\n-79 44 53 56 65 0\n-80 72 0\n-81 73 0\n-81 74 0\n-82 80 0\n-82 81 0\n-83 75 0\n-83 76 0\n-84 78 0\n-84 79 0\n-85 77 84 0\n-86 77 0\n-86 84 0\n-87 83 86 0\n-88 83 0\n-87 85 0\n-88 86 0\n-89 82 88 0\n-89 87 0\n89 0\n-90 48 0\n-48 90 0\n-91 55 0\n-55 91 0\n-92 60 0\n-60 92 0\n-93 67 0\n-67 93 0\n-94 68 0\n-68 94 0\n-95 50 51 0\n-96 62 63 0\n-62 96 0\n-63 96 0\n-97 91 92 0\n-92 97 0\n-91 97 0\n-98 90 97 0\n-97 98 0\n-90 98 0\n-90 -97 99 0\n-100 93 94 0\n-93 100 0\n-93 -94 101 0\n-102 95 0\n-102 96 0\n-104 100 102 0\n-100 103 0\n-101 104 0\n-105 98 104 0\n-98 -104 106 0\n-99 -103 106 0\n105 0\n-106 0\n2 13 16 22 25 26 27 28 44 47 48 50 51 56 59 60 62 63 68 0\n8 14 17 27 33 40 41 50 51 54 62 63 66 0\n11 14 17 34 39 42 43 54 55 66 67 0\n"
  "226 87 0 188 187 0\n227 85 0 226 184 0\n228 71 33 7 8 -86 -96 0 180 167 35 34 33 32 27 181 177 158 159 156 154 102 168 89 106 200 87 0\n229 -28 -5 6 -36 0 34 33 27 16 17 18 101 0\n230 70 -71 7 8 11 -86 0 180 167 35 28 181 177 156 157 153 2 11 113 64 65 229 168 3 10 105 0\n231 -6 -36 55 0 55 37 34 152 114 115 142 138 139 143 225 0\n232 43 11 -36 55 0 55 37 34 152 142 138 139 143 225 0\n233 11 -86 -104 0 222 219 207 205 192 180 167 231 155 152 195 208 190 204 194 150 197 210 215 214 232 57 62 117 228 230 0\n234 -88 -104 0 183 185 175 180 167 36 37 55 233 39 44 59 164 0\n235 -5 -11 -36 -104 0 188 222 226 59 55 36 39 37 44 164 175 182 181 177 116 219 207 205 192 231 35 31 28 234 186 173 170 152 13 229 168 3 10 22 105 118 134 137 160 0\n236 -8 -11 -36 -104 0 222 188 39 55 36 31 234 186 173 170 219 207 205 192 152 14 118 119 134 137 160 0\n237 -11 -36 -104 0 188 222 226 219 207 205 192 231 155 55 37 36 31 234 186 173 170 152 195 208 190 204 194 150 197 210 215 214 39 44 59 116 164 175 182 235 153 157 236 228 25 122 126 134 137 160 0\n238 -36 -104 0 222 188 234 186 173 170 219 207 205 192 152 31 36 55 237 232 58 60 61 64 134 137 160 0\n239 -27 -78 0 15 19 168 0\n240 -52 -95 0 73 74 199 0\n241 -64 -95 0 93 94 199 0\n242 -29 -78 0 20 21 168 0\n243 100 -104 0 227 188 215 213 234 186 173 170 238 167 179 177 239 240 241 242 160 22 23 168 0\n244 -104 0 222 219 207 208 204 205 190 194 192 150 152 197 195 210 243 0\n245 -101 0 244 217 0\n246 98 0 244 221 218 0\n247 -30 0 227 226 22 23 42 49 54 61 168 177 181 179 182 167 175 36 37 164 0\n248 21 28 -52 0 227 226 188 246 72 71 168 177 181 179 185 182 167 186 176 28 29 30 32 33 76 174 112 191 171 172 1 9 162 86 163 68 69 189 206 203 193 81 82 84 85 166 0\n249 84 28 -52 27 0 227 226 188 90 248 10 88 6 3 110 74 73 108 80 67 24 12 8 7 5 4 72 71 181 179 185 182 167 186 176 33 174 171 172 162 86 163 68 69 103 166 84 100 104 223 0\n250 -60 -79 56 44 0 83 98 169 0\n251 -48 -79 56 44 0 75 97 169 0\n252 28 -52 27 0 90 88 74 73 248 3 6 10 12 67 80 108 110 249 178 250 109 251 107 150 223 0\n253 -55 -52 27 0 226 252 48 26 90 88 74 73 76 77 78 79 151 135 167 180 182 175 164 57 140 141 144 145 224 0\n254 40 37 42 -75 55 -28 -52 0 48 71 70 134 58 111 164 124 0\n255 -40 41 -52 0 40 64 146 0\n256 37 42 55 -28 -52 0 226 48 255 71 70 254 134 165 175 111 182 121 180 232 167 0\n257 42 -52 27 0 252 48 255 253 152 26 90 88 74 73 71 70 256 38 63 111 120 125 128 130 132 129 131 225 0\n258 -52 27 0 252 48 257 52 66 146 0\n259 -42 -64 0 52 56 66 148 0\n260 12 43 -64 27 29 0 245 227 222 259 149 96 95 94 93 92 91 148 111 43 46 50 51 133 137 76 192 196 167 205 211 212 179 216 198 177 178 220 168 209 3 6 10 67 80 190 108 110 250 107 109 223 0\n261 -55 41 40 43 42 0 226 76 77 78 167 164 180 175 182 0\n262 -9 -12 43 42 0 40 45 261 152 123 124 121 138 139 142 143 225 0\n263 43 -64 27 29 0 259 149 96 95 94 93 260 40 45 261 152 262 133 38 120 125 127 128 130 132 129 131 225 0\n264 52 27 29 -72 0 247 160 93 94 95 96 263 57 62 64 65 130 132 129 131 224 0\n265 27 -72 29 0 258 264 0\n266 -27 0 227 226 41 47 53 60 239 177 181 179 182 167 175 36 37 164 0\n267 43 -88 0 185 180 167 76 55 37 36 183 175 232 39 44 164 0\n268 29 0 266 188 265 161 170 173 186 185 180 167 36 55 76 99 231 155 267 57 58 59 62 64 117 230 228 201 202 136 147 0\n269 -36 0 268 31 0\n270 -78 0 268 242 0\n271 -77 0 269 167 0\n272 -84 0 270 177 0\n273 0 271 272 227 179 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record002_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record031
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1b44f1b23a8da2eb26698e6c5996359362da4e1b85e0fbc16c4e9365392e74571725694e5c5595355352d64d4b46d4745d0f783b0f2368ce3c4d9334d332ce4b32cab1ac9b16c3bc1d8731e2749ca719e1745c9715c3783e461382e079a164705915254544d0b41d90cc328c9312c2b06e0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db6db6da4934db69a4d269a4924d349a4d2492493492492491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 54), (facetIndex 76)]))
 (.leaf ([(facetIndex 71), (facetIndex 73), (facetIndex 74)])))
 (.branch 3
 (.leaf ([(facetIndex 89), (facetIndex 90), (facetIndex 91)]))
 (.leaf ([(facetIndex 46), (facetIndex 61), (facetIndex 72)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 81), (facetIndex 82), (facetIndex 93)]))
 (.leaf ([(facetIndex 36), (facetIndex 49), (facetIndex 52), (facetIndex 92)])))
 (.branch 7
 (.leaf ([(facetIndex 84), (facetIndex 85), (facetIndex 88)]))
 (.branch 8
 (.leaf ([(facetIndex 63), (facetIndex 66), (facetIndex 69), (facetIndex 87), (facetIndex 94)]))
 (.leaf ([(facetIndex 83), (facetIndex 86)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "74522267866844000000113107007007030000000050050030000000005z24;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7, 8]
def grouped3_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [7, 8]
def grouped3_0016 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record031" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record031" 68

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record031" "{\"ridges\":[[10,194],[15,276],[16,292],[18,769],[18,772],[19,400],[29,276],[33,292],[35,194],[36,390],[37,772],[43,194],[47,194],[48,400],[49,786],[50,194],[53,194],[54,898],[57,276],[59,292],[62,276],[64,276],[64,400],[65,276],[65,769],[67,292],[68,769],[68,772],[69,452],[70,769],[70,772],[75,400],[76,960],[85,786],[88,802],[92,306],[93,312],[94,180]],\"owners\":[[10,194,[83,86,90,91],[35,43,47,50,53]],[35,194,[90,91],[10,43,47,50,53,83,86]],[43,194,[83,86],[10,35,47,50,53,90,91]],[47,194,[86,91],[10,35,43,50,53,83,90]],[50,194,[83,90],[10,35,43,47,53,86,91]],[53,194,[83,86,90,91],[10,35,43,47,50]],[15,276,[82,84,85,93,94],[29,57,62,64,65]],[29,276,[93,94],[15,57,62,64,65,82,84,85]],[57,276,[82,84,85,94],[15,29,62,64,65,93]],[62,276,[84,85],[15,29,57,64,65,82,93,94]],[64,276,[82,85,93],[15,29,57,62,65,84,94]],[65,276,[82,84,93,94],[15,29,57,62,64,85]],[16,292,[82,87,88,93,94],[33,59,62,67,68]],[33,292,[93,94],[16,59,62,67,68,82,87,88]],[59,292,[82,87,88,94],[16,33,62,67,68,93]],[67,292,[82,88,93],[16,33,59,62,68,87,94]],[18,769,[49,52,54,76],[37,65,68,70]],[65,769,[52,54,76],[18,37,49,68,70]],[68,769,[49,54,76],[18,37,52,65,70]],[70,769,[49,52,54],[18,37,65,68,76]],[18,772,[85,88],[37,65,68,70]],[37,772,[],[18,65,68,70,85,88]],[68,772,[85],[18,37,65,70,88]],[70,772,[85,88],[18,37,65,68]],[19,400,[84,92,94],[48,64,75]],[48,400,[94],[19,64,75,84,92]],[64,400,[92],[19,48,75,84,94]],[75,400,[84],[19,48,64,92,94]],[36,390,[84,87],[]],[92,306,[46,82],[]],[49,786,[85],[]],[85,786,[49],[]],[88,802,[52],[]],[54,898,[],[]],[94,180,[61,81],[]],[69,452,[],[]],[93,312,[72],[]],[76,960,[],[]]],\"edges\":[[22,[15,16,18,29,33,36,37,57,59,62,64,65,67,68,69,70,82,84,85,87,88,93,94]],[33,[15,19,29,46,48,49,57,62,64,65,72,75,82,84,85,92,93,94]],[39,[10,35,43,47,50,53,63,66,69,73,74,76,83,86,90,91]],[44,[18,37,49,52,54,65,68,70,76,85,88]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record031" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record031\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,39,42,45,46],[-8,45,46],[-11,39,42],[-13,42,46],[-16,39,45],[-18,39,42,45,46],[-2,38,40,41,48,49],[-6,48,49],[-20,38,40,41,49],[-23,40,41],[-25,38,41,48],[-26,38,40,48,49],[-3,38,43,44,48,49],[-7,48,49],[-21,38,43,44,49],[-28,38,44,48],[-4,15,17,19,36],[-26,17,19,36],[-29,15,19,36],[-31,15,17,19],[-4,41,44],[-10],[-29,41],[-31,41,44],[-5,40,47,49],[-14,49],[-25,47],[-35,40],[-9,40,43],[-47,12,38],[-15,41],[-41,15],[-44,17],[-19],[-49,22,37],[-30],[-48,32],[-36],[-33,50],[-34,50],[-45,51],[-46,51],[-12,52],[-22,52],[-32,52],[-37,53],[-38,53],[-48,53],[-15,54],[-17,54],[-40,55],[-41,55],[-44,55],[-24,56],[-27,56],[-43,56],[-49,56],[-39,57],[-42,57],[-50,58],[-52,59],[-51,59],[-59,60],[-58,60],[-54,61],[-53,-54,62],[-57,63],[-56,63],[-63,64],[-55,64],[-55,-63,65],[-61,-64,66],[-61,-65,67],[-62,66],[-62,-64,67],[-67,68],[-60,-66,68],[-68],[2,3,4,6,7,9,10,20,21,23,25,26,28,29,30,31,38,40,41,43,44,48,49],[2,5,6,12,14,15,20,23,25,26,32,35,38,40,41,47,48,49],[1,8,11,13,16,18,24,27,30,33,34,36,39,42,45,46],[4,10,15,17,19,26,29,31,36,41,44]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":194,\"a\":10,\"owners\":[83,86,90,91]},{\"tag\":\"mate\",\"ridge\":194,\"a\":35,\"owners\":[90,91]},{\"tag\":\"mate\",\"ridge\":194,\"a\":43,\"owners\":[83,86]},{\"tag\":\"mate\",\"ridge\":194,\"a\":47,\"owners\":[86,91]},{\"tag\":\"mate\",\"ridge\":194,\"a\":50,\"owners\":[83,90]},{\"tag\":\"mate\",\"ridge\":194,\"a\":53,\"owners\":[83,86,90,91]},{\"tag\":\"mate\",\"ridge\":276,\"a\":15,\"owners\":[82,84,85,93,94]},{\"tag\":\"mate\",\"ridge\":276,\"a\":29,\"owners\":[93,94]},{\"tag\":\"mate\",\"ridge\":276,\"a\":57,\"owners\":[82,84,85,94]},{\"tag\":\"mate\",\"ridge\":276,\"a\":62,\"owners\":[84,85]},{\"tag\":\"mate\",\"ridge\":276,\"a\":64,\"owners\":[82,85,93]},{\"tag\":\"mate\",\"ridge\":276,\"a\":65,\"owners\":[82,84,93,94]},{\"tag\":\"mate\",\"ridge\":292,\"a\":16,\"owners\":[82,87,88,93,94]},{\"tag\":\"mate\",\"ridge\":292,\"a\":33,\"owners\":[93,94]},{\"tag\":\"mate\",\"ridge\":292,\"a\":59,\"owners\":[82,87,88,94]},{\"tag\":\"mate\",\"ridge\":292,\"a\":67,\"owners\":[82,88,93]},{\"tag\":\"mate\",\"ridge\":769,\"a\":18,\"owners\":[49,52,54,76]},{\"tag\":\"mate\",\"ridge\":769,\"a\":65,\"owners\":[52,54,76]},{\"tag\":\"mate\",\"ridge\":769,\"a\":68,\"owners\":[49,54,76]},{\"tag\":\"mate\",\"ridge\":769,\"a\":70,\"owners\":[49,52,54]},{\"tag\":\"mate\",\"ridge\":772,\"a\":18,\"owners\":[85,88]},{\"tag\":\"mate\",\"ridge\":772,\"a\":37,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":772,\"a\":68,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":772,\"a\":70,\"owners\":[85,88]},{\"tag\":\"mate\",\"ridge\":400,\"a\":19,\"owners\":[84,92,94]},{\"tag\":\"mate\",\"ridge\":400,\"a\":48,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":400,\"a\":64,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":400,\"a\":75,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":390,\"a\":36,\"owners\":[84,87]},{\"tag\":\"mate\",\"ridge\":306,\"a\":92,\"owners\":[46,82]},{\"tag\":\"mate\",\"ridge\":786,\"a\":49,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":786,\"a\":85,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":802,\"a\":88,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":898,\"a\":54,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":180,\"a\":94,\"owners\":[61,81]},{\"tag\":\"mate\",\"ridge\":452,\"a\":69,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":312,\"a\":93,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":960,\"a\":76,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":73,\"full_literals\":[-33,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":74,\"full_literals\":[-34,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":90,\"full_literals\":[-45,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":91,\"full_literals\":[-46,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":46,\"full_literals\":[-12,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":61,\"full_literals\":[-22,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":72,\"full_literals\":[-32,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":81,\"full_literals\":[-37,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":82,\"full_literals\":[-38,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":93,\"full_literals\":[-48,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":49,\"full_literals\":[-15,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":52,\"full_literals\":[-17,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":84,\"full_literals\":[-40,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":85,\"full_literals\":[-41,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":88,\"full_literals\":[-44,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":63,\"full_literals\":[-24,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":66,\"full_literals\":[-27,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":87,\"full_literals\":[-43,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":94,\"full_literals\":[-49,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":83,\"full_literals\":[-39,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":86,\"full_literals\":[-42,57]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-50,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-53,-54,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-63,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-55,-63,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-61,-64,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-61,-65,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-62,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-62,-64,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-60,-66,68],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":22,\"owners\":[15,16,18,29,33,36,37,57,59,62,64,65,67,68,69,70,82,84,85,87,88,93,94]},{\"tag\":\"edge\",\"edge\":33,\"owners\":[15,19,29,46,48,49,57,62,64,65,72,75,82,84,85,92,93,94]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[10,35,43,47,50,53,63,66,69,73,74,76,83,86,90,91]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[18,37,49,52,54,65,68,70,76,85,88]}]}"
  "p cnf 68 82\n-1 39 42 45 46 0\n-8 45 46 0\n-11 39 42 0\n-13 42 46 0\n-16 39 45 0\n-18 39 42 45 46 0\n-2 38 40 41 48 49 0\n-6 48 49 0\n-20 38 40 41 49 0\n-23 40 41 0\n-25 38 41 48 0\n-26 38 40 48 49 0\n-3 38 43 44 48 49 0\n-7 48 49 0\n-21 38 43 44 49 0\n-28 38 44 48 0\n-4 15 17 19 36 0\n-26 17 19 36 0\n-29 15 19 36 0\n-31 15 17 19 0\n-4 41 44 0\n-10 0\n-29 41 0\n-31 41 44 0\n-5 40 47 49 0\n-14 49 0\n-25 47 0\n-35 40 0\n-9 40 43 0\n-47 12 38 0\n-15 41 0\n-41 15 0\n-44 17 0\n-19 0\n-49 22 37 0\n-30 0\n-48 32 0\n-36 0\n-33 50 0\n-34 50 0\n-45 51 0\n-46 51 0\n-12 52 0\n-22 52 0\n-32 52 0\n-37 53 0\n-38 53 0\n-48 53 0\n-15 54 0\n-17 54 0\n-40 55 0\n-41 55 0\n-44 55 0\n-24 56 0\n-27 56 0\n-43 56 0\n-49 56 0\n-39 57 0\n-42 57 0\n-50 58 0\n-52 59 0\n-51 59 0\n-59 60 0\n-58 60 0\n-54 61 0\n-53 -54 62 0\n-57 63 0\n-56 63 0\n-63 64 0\n-55 64 0\n-55 -63 65 0\n-61 -64 66 0\n-61 -65 67 0\n-62 66 0\n-62 -64 67 0\n-67 68 0\n-60 -66 68 0\n-68 0\n2 3 4 6 7 9 10 20 21 23 25 26 28 29 30 31 38 40 41 43 44 48 49 0\n2 5 6 12 14 15 20 23 25 26 32 35 38 40 41 47 48 49 0\n1 8 11 13 16 18 24 27 30 33 34 36 39 42 45 46 0\n4 10 15 17 19 26 29 31 36 41 44 0\n"
  "83 -67 0 78 76 0\n84 2 3 4 6 7 9 20 21 23 25 26 28 29 31 38 40 41 43 44 48 49 0 22 36 79 0\n85 1 8 11 13 16 18 24 27 33 34 39 42 45 46 0 36 38 81 0\n86 4 15 17 26 29 31 41 44 0 22 34 38 82 0\n87 54 0 38 34 49 50 19 32 18 33 17 20 86 0\n88 61 0 87 65 0\n89 -65 0 88 83 73 0\n90 55 53 52 0 43 47 30 27 45 37 44 46 35 8 26 51 52 10 25 28 7 9 12 31 80 0\n91 63 60 0 63 62 42 41 2 64 60 40 39 67 68 58 59 54 55 1 3 5 6 4 85 0\n92 60 0 89 83 87 63 61 91 69 71 75 90 66 0\n93 -66 0 92 78 77 0\n94 -62 0 93 74 0\n95 -64 0 93 88 72 0\n96 -53 0 94 87 66 0\n97 -63 0 95 69 0\n98 -55 0 95 70 0\n99 -38 0 96 47 0\n100 -48 0 96 48 0\n101 -56 0 97 68 0\n102 -40 0 98 51 0\n103 -41 0 98 52 0\n104 -44 0 98 53 0\n105 -43 0 101 56 0\n106 -49 0 101 57 0\n107 -23 0 102 103 10 0\n108 -2 0 102 99 103 100 106 7 0\n109 -20 0 102 99 103 106 9 0\n110 -26 0 102 99 100 106 12 0\n111 -9 0 102 105 29 0\n112 -29 0 103 23 0\n113 -25 0 103 99 100 11 0\n114 -4 0 104 103 21 0\n115 -31 0 104 103 24 0\n116 -28 0 104 99 100 16 0\n117 -21 0 104 99 105 106 15 0\n118 -3 0 104 99 105 100 106 13 0\n119 -6 0 106 100 8 0\n120 -7 0 106 100 14 0\n121 0 114 109 108 118 119 120 111 117 107 113 110 116 112 115 99 102 103 105 104 100 106 84 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record031_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record031
