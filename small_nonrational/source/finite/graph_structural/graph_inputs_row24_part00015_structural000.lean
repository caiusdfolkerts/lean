module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00015Data
public import GraphInputsRow24Part00015Frames
public import GraphInputsRow24Part00015Leaves
public import GraphInputsRow24Part00015Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

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
