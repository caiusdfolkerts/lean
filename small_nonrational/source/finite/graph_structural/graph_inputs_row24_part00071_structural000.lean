module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00071Data
public import GraphInputsRow24Part00071Frames
public import GraphInputsRow24Part00071Leaves
public import GraphInputsRow24Part00071Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record001
def vertexColumn : Fields := ⟨10, hexnat% "ec2f2e2b48eaa68ba9592e1b83eb86d13a699664b939655354b53352d2b46d2743db0ea398ce3c4e9394cd32ce8b32d2b2ac6b86c9b0ee4751d2785c570dc4f4711a199164382e07ac1386912a519264654550d0b41d90c6384d1342c2b06d0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6da4924924db6924934924db692492492489249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fe577ad37fe2c0000000", hexnat% "1000400000400000000", 2251907187867648, hexnat% "880100000000000000", hexnat% "208004000000000000", 9147936743096320]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffc17d527dbfc0000000", hexnat% "60080004000000000", 11399736556781568, hexnat% "88200000000000000", hexnat% "300000000000000000", 1409573906808832]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fefffbd57be0c0000000", hexnat% "1000400040400000000", 703700326678528, 11259067787902976, 34359738368]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffedfb147b20c0000000", hexnat% "200c0004000000000", hexnat% "100021800000000000", 2251907187867648, 288234791378092032, 563508299169792]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fefffffdfbf0c0000000", hexnat% "1000000040400000000", 47244640256, 562949953421312]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "1ffffffffffffc0000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffcbfffc7f74c0000000", hexnat% "300000000000000000", 47244640256, hexnat% "40001008000000000", 703687441776640]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffcb7ff07b64c0000000", 4947802324992, hexnat% "20800c000000000000", hexnat% "140001000000000000", 115964116992, 703687441776640]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fe3cf87df939c0000000", hexnat% "1c00000000000000000", 563783177076736, 360287987369508864, hexnat% "30080000000000000", 144121785145622528]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fe88fb5c7f3fc0000000", hexnat% "1000400000000000000", hexnat% "300020000000000000", hexnat% "410000000000000000", hexnat% "6008000c000000000", 985162418487296]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1feb8ff7c7b24c0000000", hexnat% "1400000000000000000", 115964116992, 5222680231936, hexnat% "70080000000000000", 985162418487296]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fe28f95c792080000000", hexnat% "1c00000000040000000", 133143986176, hexnat% "70080004000000000", 985712174301184, 432352161297334272, hexnat% "100020000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c16 c13
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c17 c12
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c18 c11
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c19 c4
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c20 c1
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c21 c0
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record002
def vertexColumn : Fields := ⟨10, hexnat% "2e43b0bcb8ad296ac6a9a6639b16a58b69392e1ba1e0fad13a4d92e6c539695654b53352d2b46d2743db0ce3a4e5334cb352d2b16c3ba1e4731d2729c6785c970dc4fa511c1a91a859164382e078e11a519295152550d0b41d18d1342c4b0ac1b41c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6936924d36d249a49269b6d249b692492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4123437039616, 108649344231538688, 2451154470235537408, hexnat% "610000000000000000", hexnat% "68000000000000000", 6755425210859520, 18295874023063552]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record006
def vertexColumn : Fields := ⟨10, hexnat% "3b0bcb8a72b28ea9687a39936338ae1b83eb86b19c6c93a699964b91e4e5a55352d58d334ad1b49d0f6c3a8e6338f1394e334cc73a2e4b52ccb2ac6b86c5b0ee8731d2729c6785c8f13c2f4711a458364381eb04e132519295150d50d2341d90c6384d130cd0b12c1b41c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db69b6936936da69249a49a49249a49a493692492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40004000800480000000", 2089670228173651968, 2041655653826560, hexnat% "4200080010010000000", hexnat% "12000000300000000", hexnat% "2400048040000000000", 4529988443308032]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record008
def vertexColumn : Fields := ⟨10, hexnat% "f83d0ec370bc1f2e23a93a2eac639a96658b6938ce2b86e2783eb84f14e479b14e5a54d52d4759354d1b45d0f6c3a8e6338e934ccb392d2b1af07a1e4731ca719e1725c3783c4f0bec4470b24683aa19162590e0786946439915154344d075130cd0b0ac1b81d0705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6da49a49b6d26d24db6d24936db49a4926da492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000800003000000000", 16888498871074816, 3458766163087982592, hexnat% "1c20000000080000000", hexnat% "180000000c0000000000", 280917704704, hexnat% "10002000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record013
def vertexColumn : Fields := ⟨10, hexnat% "b92cc3b0bcb8aca3a87ab1aa6998e64da8e938ce2b86e0fae1b24e92e479b16a5994e54d4b5a358d934cd2b46d2743db0ea398ce34cc73a2e4b52ccb2ac6b16c3bc1e8791cc789d2729c6785e0f23c4f0bd1c469160d90e07ac1384c946685295150d50d2341d90c6344c3342c4b06e0741c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6d36db4926d269249a4d24d249a49a4924d2492491249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffffbfff3cfe60000000", 4611686024869838848, 3298534883328, 211106232532992]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffffbc7f3cfe60000000", 211108380016640, 36029896530591744, 2203318222848, 4827858800541171712]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdf7fdff5620cce0000000", hexnat% "200020008001200000000", 45405432180637696, hexnat% "8000000040000000000", 3440268804096, 149533581377536]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffffafff7d7ea0000000", 140742857064448, 2748779069440, 5764607523034234880]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c7 c0
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffdfafff717ea0000000", 5764607524107976704, hexnat% "200000008000000000", 2203318222848, 153931627888640]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdf7cd24f7fd4ce0000000", hexnat% "200020008001200000000", hexnat% "309800000000000000", hexnat% "8000100000000000000", 2890512990208, 4755801206503243776]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdf7dffff3f97de0000000", hexnat% "200000008000000000", 3382097767038976, 2207613190144, hexnat% "208000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdf0dfaf7ffc7de0000000", 5764607523034234880, 3856880631808, hexnat% "208000000000000000000", hexnat% "7200080000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffff0dfaf5ae07e20000000", 5764607526255460352, hexnat% "9000000140000000000", 3852585664512, 10423370231316480, hexnat% "6200080000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c16 c13
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffff0cf245a205200000000", hexnat% "9000900140020000000", hexnat% "6200080000000000000", 9508577630748672, hexnat% "10d200000080000000", 3990024617984, 1125951446450176]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c19 c12
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c20 c6
  c21
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record013_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record013

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record021
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record021
def vertexColumn : Fields := ⟨10, hexnat% "b52b4b313cb28ea5693a1eac6a9b1695a364da8e938ce4b8ae4785e0fad13c4e9565391e6c5a5655355352d58d3352d4745d0f6c338e5354d331cd4b32d2b2ac6b46c5b0ee8791cc749ca785c5723c4f07cac94a16458364382e324a9295150d50d2342d44c530cd0b12c2b41c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6924db4934da6db6da4924d36924924924db492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "208100700ff89e000000", 108649342084055040, hexnat% "480000000000000000", 123145839181824, hexnat% "200008000000000000", hexnat% "58000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2801da0038ce000000", hexnat% "c00000000000000000", 8521215115264, hexnat% "10020000000000000", hexnat% "78000000000030000000", 131941395333120]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "880019a7938f6000000", hexnat% "70000000000000000000", 7421837705216, hexnat% "10060000000000000", hexnat% "280000000000000000", hexnat% "400000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "880019a17f8ce000000", hexnat% "10060000000000000", hexnat% "480000000000000000", 114350014595072, hexnat% "50200000000000000000", hexnat% "20000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100087ff83e000000", 31525197391593472, hexnat% "78000000000000000000", 108649344231538688, hexnat% "a80000000000000000", hexnat% "400000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8e8019a1900ce000000", hexnat% "10060000000000000", hexnat% "70000000000030000000", 105621835743232, 4844723109888, 2748779069440]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20800008590034000000", 113152943858909184, hexnat% "10060000008000000", hexnat% "400000028000000000", 39822970322944, hexnat% "58280000000000000000", 274877906944]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record021_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record021_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record021_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record021_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record021_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record021_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record021_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record021_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record021_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record021

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record027
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record027
def vertexColumn : Fields := ⟨10, hexnat% "f44f0f2aa93a2e8e6558d64d8b61da4e4b91e1783eb44f1aa699965392e4e5554d54d4b51d64d4b45da8ce364d5334d332cc73c2e8b92e2b4acab46c9b16c3b91d4731d2729c6745c9715c3783c4f07d1c0f2c24382eb04d12c5190e515154354342d0768390cc328e0b42c2b41c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "d36db6db6d26926da4d24934926d34d24924da492493492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2002013ec0030fef8000000", hexnat% "3000120000000000000", 1055531162664960, hexnat% "14000008090000000000", 144115188075855872, hexnat% "80000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2003412ac282956d8000000", hexnat% "3010000000000000000", 422762757750784, hexnat% "84000000000000000", 650910883643392, 216172953912475648]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3014328717e50000000", 422762757750784, 571746180661248, hexnat% "2a400000080000000", hexnat% "180000000000000000", hexnat% "20034000800000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000f03f0fef8000000", hexnat% "3e000000000000000", hexnat% "3000020000000000000", hexnat% "20000100000000000000000", hexnat% "14000008090000000000", hexnat% "80000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200351bec2bf91af8000000", 216172919552737280, hexnat% "2000000000000000000", 841813590016]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2003518ec2b791af8000000", hexnat% "30000000000000000", 144256063003164672, hexnat% "2000100000000000000", 841813590016]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2003418882a691af8000000", 979252543488, 216471849276538880, hexnat% "3010000000000000000", 288371113640067072, hexnat% "26000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200351bed28291ed8000000", hexnat% "2000000002000000000", 825170591744, 144484623982788608, 703687441776640]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20034002e2be9fef8000000", 72075186223972352, hexnat% "18c000000000000000", hexnat% "3010000000000000000", hexnat% "20000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200351bec29991ad8000000", 668503606558720, 216172919552737280, hexnat% "2000000000000000000", 841813590016]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2003418ec28891ad8000000", hexnat% "3010000000000000000", hexnat% "20000004000000000", 967570769313792, 216172919552737280, 566935683072]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c14 c9
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "13010020081a10000000", 981400027136, 1090716071624704, 218442174113513472, hexnat% "20024000800000008000000", hexnat% "2e400000040000000", hexnat% "180000010000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c17 c8
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c18 c3
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c19 c2
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c20 c1
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c21 c0
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record027_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record027_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record027_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record027_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record027_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record027_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record027_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record027_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record027_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record027

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record010
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2e4b32ca2eac6399361da8e938ce2b83eb86c92e6c5a9665395351d70da364d334ad8743db0d332cc73a2d8b92ccb2ac9b0ee8791d4731d2729c5783c8f13c2f470e246866458364381eb04e1a251991465454358350d074c328c6344c3342c8b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6d24db69269a49249b4924926924d2492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 36), (facetIndex 70), (facetIndex 75), (facetIndex 76)]))
 (.leaf ([(facetIndex 53), (facetIndex 66), (facetIndex 68), (facetIndex 69)])))
 (.branch 3
 (.leaf ([(facetIndex 35), (facetIndex 55), (facetIndex 58), (facetIndex 59), (facetIndex 60)]))
 (.leaf ([(facetIndex 37), (facetIndex 39), (facetIndex 50), (facetIndex 63), (facetIndex 77)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 34), (facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 48), (facetIndex 49)]))
 (.leaf ([(facetIndex 43), (facetIndex 51), (facetIndex 52)])))
 (.branch 7
 (.leaf ([(facetIndex 33), (facetIndex 40), (facetIndex 41), (facetIndex 64)]))
 (.branch 8
 (.leaf ([(facetIndex 54), (facetIndex 61), (facetIndex 62)]))
 (.leaf ([(facetIndex 32), (facetIndex 38)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "3000000011010637722200271553440444506638302468z20;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 56), (facetIndex 67)]))
 (.branch 2
 (.leaf ([(facetIndex 71), (facetIndex 79)]))
 (.leaf ([(facetIndex 42), (facetIndex 47), (facetIndex 57)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 72), (facetIndex 73), (facetIndex 74)]))
 (.leaf ([(facetIndex 78), (facetIndex 80), (facetIndex 81)])))
 (.branch 6
 (.leaf ([(facetIndex 65)]))
 (.leaf ([(facetIndex 82)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1a43000db20002800001000000040008z1f;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4]
def grouped2_0009 : List Nat := [4, 5]
def grouped2_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7, 8]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8]
def grouped2_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [0]
def grouped3_0018 : List Nat := [0, 1, 2]
def grouped3_0020 : List Nat := [1]
def grouped3_0021 : List Nat := [1, 2]
def grouped3_0022 : List Nat := [2]
def grouped3_0023 : List Nat := [3]
def grouped3_0024 : List Nat := [3, 4]
def grouped3_0025 : List Nat := [3, 4, 5, 6]
def grouped3_0026 : List Nat := [4]
def grouped3_0027 : List Nat := [5]
def grouped3_0028 : List Nat := [5, 6]
def grouped3_0029 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record010" "{\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record010" 101

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record010" "{\"ridges\":[[6,131],[6,138],[10,35],[11,162],[15,524],[16,49],[19,69],[19,580],[21,648],[22,161],[26,38],[26,50],[30,162],[30,194],[32,37],[34,138],[35,524],[38,37],[38,38],[39,194],[40,67],[40,69],[40,70],[40,259],[41,580],[43,50],[44,138],[45,35],[45,138],[46,138],[46,194],[48,138],[48,259],[49,138],[49,648],[51,162],[52,35],[52,259],[53,704],[54,37],[54,49],[55,524],[58,524],[60,524],[62,37],[62,49],[63,69],[64,37],[65,676],[66,704],[68,648],[69,161],[69,704],[70,50],[72,204],[73,70],[73,580],[73,586],[74,138],[76,50],[77,38],[77,70],[78,194],[80,194],[80,586],[82,676]],\"owners\":[[40,67,[10,12,46,47,50,53],[3,33,36,41]],[6,131,[11,12,37,39,42,51,53],[34,44,48,49]],[6,138,[71,72,74,79,80],[34,44,45,46,48,49]],[34,138,[79,80],[6,44,45,46,48,49,71,72,74]],[44,138,[71,72,74,80],[6,34,45,46,48,49,79]],[45,138,[72,74,80],[6,34,44,46,48,49,71,79]],[46,138,[71,74,79],[6,34,44,45,48,49,72,80]],[48,138,[71,72,74,79,80],[6,34,44,45,46,49]],[49,138,[71,72,79],[6,34,44,45,46,48,74,80]],[74,138,[6,44,45,46,48,79],[34,49,71,72,80]],[16,49,[8,43,50,51,52,67],[54,61,62]],[54,49,[8,50,51,52],[16,43,61,62,67]],[62,49,[8,43,50,51,67],[16,52,54,61]],[26,50,[8,43,50,51,52,79],[70,75,76]],[43,50,[26,75,76],[8,50,51,52,70,79]],[70,50,[8,50,51,52],[26,43,75,76,79]],[76,50,[8,43,50,51,79],[26,52,70,75]],[22,161,[11,37,45,51,56,65,67],[63,69]],[69,161,[11,37,45,51,56,67],[22,63,65]],[11,162,[30,71,77,79],[37,45,51]],[30,162,[11,37,45,51,71,79],[77]],[51,162,[30,71,77],[11,37,45,79]],[15,524,[73,74,81],[35,55,58,59,60]],[35,524,[81],[15,55,58,59,60,73,74]],[55,524,[73,74,81],[15,35,58,59,60]],[58,524,[74],[15,35,55,59,60,73,81]],[60,524,[73,74,81],[15,35,55,58,59]],[19,580,[73,78,81,82],[41,58,64,66]],[41,580,[81,82],[19,58,64,66,73,78]],[73,580,[19,64,66,82],[41,58,78,81]],[21,648,[74,80,81],[49,59,68]],[49,648,[81],[21,59,68,74,80]],[68,648,[74],[21,49,59,80,81]],[53,704,[81,82],[23,66,68,69,78,80]],[66,704,[80],[23,53,68,69,78,81,82]],[69,704,[78,80,81],[23,53,66,68,82]],[73,586,[47,80],[]],[80,586,[47,73],[]],[72,204,[57,81],[]],[65,676,[82],[]],[82,676,[65],[]]],\"edges\":[[23,[15,19,35,41,42,55,58,59,60,64,65,66,73,74,78,81,82]],[27,[6,21,34,44,45,46,48,49,56,57,59,67,68,71,72,74,79,80,81]],[30,[8,16,26,43,50,51,52,54,61,62,67,70,75,76,79]],[36,[11,22,30,37,45,51,56,63,65,67,69,71,77,79,82]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record010" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record010\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-14,-13],[-16,-13],[-18,-2],[-18,-13],[-18,-17],[-19,-18],[-21,-13],[-21,-19],[-22,-13],[-24,-18],[-25,-13],[-25,-24],[-26,-5],[-26,-13],[-26,-20],[-26,-24],[-27,-4],[-29,-13],[-29,-14],[-29,-24],[-31,-4],[-31,-13],[-31,-18],[-31,-19],[-31,-24],[-31,-26],[-32,-13],[-32,-18],[-32,-19],[-32,-25],[-32,-26],[-32,-27],[-32,-31],[-33,-18],[-33,-19],[-33,-25],[-33,-31],[-34,-20],[-35,-13],[-35,-24],[-36,-13],[-41,-13],[-42,-13],[-42,-18],[-42,-19],[-43,-19],[-44,-34],[-45,-42],[-45,-44],[-46,-15],[-46,-40],[-47,-20],[-47,-44],[-47,-45],[-49,-46],[-50,-5],[-50,-20],[-50,-27],[-50,-44],[-50,-45],[-50,-49],[-53,-46],[-55,-20],[-55,-44],[-55,-46],[-56,-18],[-57,-19],[-57,-43],[-58,-15],[-58,-23],[-58,-40],[-58,-47],[-58,-55],[-58,-56],[-59,-18],[-59,-20],[-59,-44],[-59,-58],[-61,-14],[-61,-27],[-61,-49],[-62,-18],[-62,-20],[-62,-39],[-62,-40],[-62,-44],[-62,-46],[-62,-58],[-3,-26,-33],[-13,-43,-45],[-19,-35,-45],[-11,-19,-58],[-21,3,5,27,28,31,34],[-8,-21,-44],[-21,-54,-58],[-21,-29,-33],[-1,4,5,18,20,23,32,34],[-1,52,53,55,60,61],[-15,60,61],[-25,52,53,55,61],[-26,53,55,61],[-27,52,55,60],[-29,52,53,55,60,61],[-30,52,53,60],[-55,1,25,26,27,29,60],[-7,2,24,31,32,33,48],[-35,2,31,32,33],[-43,2,24,31,32,48],[-11,2,24,31,32,33,60],[-24,11,56,57],[-51,2,31,32,33],[-57,2,24,31,32,60],[-10,4,18,26,32,37,46,48],[-50,4,18,26,32,37,48],[-4,12,52,58,60],[-12,4,18,26,32,52,60],[-32,12,52,58],[-12,-20,-61],[-12,-27,-59],[-6,54,55,62],[-16,62],[-36,54,55,62],[-39,55],[-41,54,55,62],[-8,54,59,62,63],[-22,62,63],[-54,8,45,47,63],[-9,55,61,62],[-30,62],[-49,55],[-34,62,63],[-47,61],[-50,59,61,62],[-54,28,61],[-61,28,54],[-53,38,62],[-46,63],[-63,46],[-64,17,51,56,57],[-65,34,47,49,50],[-66,16,36,39,40,41],[-67,18,20,31,44,58],[-68,15,25,26,27,29,30],[-69,24,32,33],[-70,14,21,22,45],[-71,35,42,43],[-72,13,19],[-73,64],[-73,65],[-74,66,67],[-75,67],[-76,73,75],[-77,73],[-76,74],[-77,75],[-78,68],[-78,69],[-79,71,72],[-80,71],[-80,72],[-81,70,80],[-82,70],[-81,79],[-82,80],[-83,78,82],[-84,78],[-83,81],[-84,82],[-85,76],[-85,77,84],[-85,83],[85],[-37,86],[-48,86],[-52,87],[-60,87],[-23,88],[-28,88],[-38,88],[-89,53,54,55],[-54,89],[-90,59,61,62],[-61,90],[-91,46],[-46,91],[-92,63],[-63,92],[-88,93],[-87,93],[-93,94],[-86,94],[-90,95],[-96,89],[-96,90],[-89,-90,96],[-97,91,92],[-98,91],[-91,-92,98],[-98,99],[-99,96,97],[-95,-98,100],[-96,99],[-100,101],[-94,-99,101],[-101],[6,8,16,22,23,36,39,40,41,45,46,47,54,55,59,62,63],[1,9,15,25,26,27,29,30,37,38,40,48,49,52,53,55,60,61,62],[2,7,11,24,31,32,33,35,42,43,48,51,56,57,60],[4,10,12,18,26,32,37,44,46,48,50,52,58,60,63]],\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":33,\"b\":32},{\"tag\":\"incompatible\",\"a\":35,\"b\":32},{\"tag\":\"incompatible\",\"a\":37,\"b\":8},{\"tag\":\"incompatible\",\"a\":37,\"b\":32},{\"tag\":\"incompatible\",\"a\":37,\"b\":36},{\"tag\":\"incompatible\",\"a\":38,\"b\":37},{\"tag\":\"incompatible\",\"a\":40,\"b\":32},{\"tag\":\"incompatible\",\"a\":40,\"b\":38},{\"tag\":\"incompatible\",\"a\":41,\"b\":32},{\"tag\":\"incompatible\",\"a\":43,\"b\":37},{\"tag\":\"incompatible\",\"a\":44,\"b\":32},{\"tag\":\"incompatible\",\"a\":44,\"b\":43},{\"tag\":\"incompatible\",\"a\":45,\"b\":12},{\"tag\":\"incompatible\",\"a\":45,\"b\":32},{\"tag\":\"incompatible\",\"a\":45,\"b\":39},{\"tag\":\"incompatible\",\"a\":45,\"b\":43},{\"tag\":\"incompatible\",\"a\":46,\"b\":11},{\"tag\":\"incompatible\",\"a\":48,\"b\":32},{\"tag\":\"incompatible\",\"a\":48,\"b\":33},{\"tag\":\"incompatible\",\"a\":48,\"b\":43},{\"tag\":\"incompatible\",\"a\":50,\"b\":11},{\"tag\":\"incompatible\",\"a\":50,\"b\":32},{\"tag\":\"incompatible\",\"a\":50,\"b\":37},{\"tag\":\"incompatible\",\"a\":50,\"b\":38},{\"tag\":\"incompatible\",\"a\":50,\"b\":43},{\"tag\":\"incompatible\",\"a\":50,\"b\":45},{\"tag\":\"incompatible\",\"a\":51,\"b\":32},{\"tag\":\"incompatible\",\"a\":51,\"b\":37},{\"tag\":\"incompatible\",\"a\":51,\"b\":38},{\"tag\":\"incompatible\",\"a\":51,\"b\":44},{\"tag\":\"incompatible\",\"a\":51,\"b\":45},{\"tag\":\"incompatible\",\"a\":51,\"b\":46},{\"tag\":\"incompatible\",\"a\":51,\"b\":50},{\"tag\":\"incompatible\",\"a\":52,\"b\":37},{\"tag\":\"incompatible\",\"a\":52,\"b\":38},{\"tag\":\"incompatible\",\"a\":52,\"b\":44},{\"tag\":\"incompatible\",\"a\":52,\"b\":50},{\"tag\":\"incompatible\",\"a\":53,\"b\":39},{\"tag\":\"incompatible\",\"a\":54,\"b\":32},{\"tag\":\"incompatible\",\"a\":54,\"b\":43},{\"tag\":\"incompatible\",\"a\":55,\"b\":32},{\"tag\":\"incompatible\",\"a\":60,\"b\":32},{\"tag\":\"incompatible\",\"a\":61,\"b\":32},{\"tag\":\"incompatible\",\"a\":61,\"b\":37},{\"tag\":\"incompatible\",\"a\":61,\"b\":38},{\"tag\":\"incompatible\",\"a\":62,\"b\":38},{\"tag\":\"incompatible\",\"a\":63,\"b\":53},{\"tag\":\"incompatible\",\"a\":64,\"b\":61},{\"tag\":\"incompatible\",\"a\":64,\"b\":63},{\"tag\":\"incompatible\",\"a\":65,\"b\":34},{\"tag\":\"incompatible\",\"a\":65,\"b\":59},{\"tag\":\"incompatible\",\"a\":66,\"b\":39},{\"tag\":\"incompatible\",\"a\":66,\"b\":63},{\"tag\":\"incompatible\",\"a\":66,\"b\":64},{\"tag\":\"incompatible\",\"a\":68,\"b\":65},{\"tag\":\"incompatible\",\"a\":69,\"b\":12},{\"tag\":\"incompatible\",\"a\":69,\"b\":39},{\"tag\":\"incompatible\",\"a\":69,\"b\":46},{\"tag\":\"incompatible\",\"a\":69,\"b\":63},{\"tag\":\"incompatible\",\"a\":69,\"b\":64},{\"tag\":\"incompatible\",\"a\":69,\"b\":68},{\"tag\":\"incompatible\",\"a\":72,\"b\":65},{\"tag\":\"incompatible\",\"a\":74,\"b\":39},{\"tag\":\"incompatible\",\"a\":74,\"b\":63},{\"tag\":\"incompatible\",\"a\":74,\"b\":65},{\"tag\":\"incompatible\",\"a\":75,\"b\":37},{\"tag\":\"incompatible\",\"a\":76,\"b\":38},{\"tag\":\"incompatible\",\"a\":76,\"b\":62},{\"tag\":\"incompatible\",\"a\":77,\"b\":34},{\"tag\":\"incompatible\",\"a\":77,\"b\":42},{\"tag\":\"incompatible\",\"a\":77,\"b\":59},{\"tag\":\"incompatible\",\"a\":77,\"b\":66},{\"tag\":\"incompatible\",\"a\":77,\"b\":74},{\"tag\":\"incompatible\",\"a\":77,\"b\":75},{\"tag\":\"incompatible\",\"a\":78,\"b\":37},{\"tag\":\"incompatible\",\"a\":78,\"b\":39},{\"tag\":\"incompatible\",\"a\":78,\"b\":63},{\"tag\":\"incompatible\",\"a\":78,\"b\":77},{\"tag\":\"incompatible\",\"a\":80,\"b\":33},{\"tag\":\"incompatible\",\"a\":80,\"b\":46},{\"tag\":\"incompatible\",\"a\":80,\"b\":68},{\"tag\":\"incompatible\",\"a\":81,\"b\":37},{\"tag\":\"incompatible\",\"a\":81,\"b\":39},{\"tag\":\"incompatible\",\"a\":81,\"b\":58},{\"tag\":\"incompatible\",\"a\":81,\"b\":59},{\"tag\":\"incompatible\",\"a\":81,\"b\":63},{\"tag\":\"incompatible\",\"a\":81,\"b\":65},{\"tag\":\"incompatible\",\"a\":81,\"b\":77},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[10,45,52]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[32,62,64]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[38,54,64]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[26,38,77]},{\"tag\":\"mate\",\"ridge\":67,\"a\":40,\"owners\":[10,12,46,47,50,53]},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[19,40,63]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[40,73,77]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[40,48,52]},{\"tag\":\"mate\",\"ridge\":131,\"a\":6,\"owners\":[11,12,37,39,42,51,53]},{\"tag\":\"mate\",\"ridge\":138,\"a\":6,\"owners\":[71,72,74,79,80]},{\"tag\":\"mate\",\"ridge\":138,\"a\":34,\"owners\":[79,80]},{\"tag\":\"mate\",\"ridge\":138,\"a\":44,\"owners\":[71,72,74,80]},{\"tag\":\"mate\",\"ridge\":138,\"a\":45,\"owners\":[72,74,80]},{\"tag\":\"mate\",\"ridge\":138,\"a\":46,\"owners\":[71,74,79]},{\"tag\":\"mate\",\"ridge\":138,\"a\":48,\"owners\":[71,72,74,79,80]},{\"tag\":\"mate\",\"ridge\":138,\"a\":49,\"owners\":[71,72,79]},{\"tag\":\"mate\",\"ridge\":138,\"a\":74,\"owners\":[6,44,45,46,48,79]},{\"tag\":\"mate\",\"ridge\":49,\"a\":16,\"owners\":[8,43,50,51,52,67]},{\"tag\":\"mate\",\"ridge\":49,\"a\":54,\"owners\":[8,50,51,52]},{\"tag\":\"mate\",\"ridge\":49,\"a\":62,\"owners\":[8,43,50,51,67]},{\"tag\":\"mate\",\"ridge\":50,\"a\":26,\"owners\":[8,43,50,51,52,79]},{\"tag\":\"mate\",\"ridge\":50,\"a\":43,\"owners\":[26,75,76]},{\"tag\":\"mate\",\"ridge\":50,\"a\":70,\"owners\":[8,50,51,52]},{\"tag\":\"mate\",\"ridge\":50,\"a\":76,\"owners\":[8,43,50,51,79]},{\"tag\":\"mate\",\"ridge\":161,\"a\":22,\"owners\":[11,37,45,51,56,65,67]},{\"tag\":\"mate\",\"ridge\":161,\"a\":69,\"owners\":[11,37,45,51,56,67]},{\"tag\":\"mate\",\"ridge\":162,\"a\":11,\"owners\":[30,71,77,79]},{\"tag\":\"mate\",\"ridge\":162,\"a\":30,\"owners\":[11,37,45,51,71,79]},{\"tag\":\"mate\",\"ridge\":162,\"a\":51,\"owners\":[30,71,77]},{\"tag\":\"three\",\"ridge\":194,\"vertices\":[30,39,80]},{\"tag\":\"three\",\"ridge\":194,\"vertices\":[30,46,78]},{\"tag\":\"mate\",\"ridge\":524,\"a\":15,\"owners\":[73,74,81]},{\"tag\":\"mate\",\"ridge\":524,\"a\":35,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":524,\"a\":55,\"owners\":[73,74,81]},{\"tag\":\"mate\",\"ridge\":524,\"a\":58,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":524,\"a\":60,\"owners\":[73,74,81]},{\"tag\":\"mate\",\"ridge\":580,\"a\":19,\"owners\":[73,78,81,82]},{\"tag\":\"mate\",\"ridge\":580,\"a\":41,\"owners\":[81,82]},{\"tag\":\"mate\",\"ridge\":580,\"a\":73,\"owners\":[19,64,66,82]},{\"tag\":\"mate\",\"ridge\":648,\"a\":21,\"owners\":[74,80,81]},{\"tag\":\"mate\",\"ridge\":648,\"a\":49,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":648,\"a\":68,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":704,\"a\":53,\"owners\":[81,82]},{\"tag\":\"mate\",\"ridge\":704,\"a\":66,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":704,\"a\":69,\"owners\":[78,80,81]},{\"tag\":\"mate\",\"ridge\":586,\"a\":73,\"owners\":[47,80]},{\"tag\":\"mate\",\"ridge\":586,\"a\":80,\"owners\":[47,73]},{\"tag\":\"mate\",\"ridge\":204,\"a\":72,\"owners\":[57,81]},{\"tag\":\"mate\",\"ridge\":676,\"a\":65,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":676,\"a\":82,\"owners\":[65]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[36,70,75,76],\"full_literals\":[-64,17,51,56,57]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[53,66,68,69],\"full_literals\":[-65,34,47,49,50]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[35,55,58,59,60],\"full_literals\":[-66,16,36,39,40,41]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[37,39,50,63,77],\"full_literals\":[-67,18,20,31,44,58]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[34,44,45,46,48,49],\"full_literals\":[-68,15,25,26,27,29,30]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[43,51,52],\"full_literals\":[-69,24,32,33]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[33,40,41,64],\"full_literals\":[-70,14,21,22,45]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[54,61,62],\"full_literals\":[-71,35,42,43]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[32,38],\"full_literals\":[-72,13,19]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-73,64,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-73,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-74,66,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-75,false,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-76,73,75],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-77,73,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-76,false,74],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-77,false,75],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-78,68,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-78,false,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-79,71,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-80,71,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-80,false,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-81,70,80],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-82,70,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-81,false,79],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-82,false,80],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-83,78,82],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-84,78,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-83,false,81],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-84,false,82],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-85,76,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-85,77,84],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-85,false,83],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":56,\"full_literals\":[-37,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":67,\"full_literals\":[-48,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":71,\"full_literals\":[-52,87]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":79,\"full_literals\":[-60,87]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":42,\"full_literals\":[-23,88]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":47,\"full_literals\":[-28,88]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":57,\"full_literals\":[-38,88]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[72,73,74],\"full_literals\":[-89,53,54,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":73,\"full_literals\":[-54,89]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[78,80,81],\"full_literals\":[-90,59,61,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":80,\"full_literals\":[-61,90]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[65],\"full_literals\":[-91,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":65,\"full_literals\":[-46,91]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[82],\"full_literals\":[-92,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":82,\"full_literals\":[-63,92]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-88,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-87,false,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-93,94],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-86,false,94],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-90,95],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-96,89,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-96,false,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-89,-90,96],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-97,91,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-98,91,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-91,-92,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-98,99],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-99,96,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-95,-98,100],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-96,false,99],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-100,101],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-94,-99,101],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":23,\"owners\":[15,19,35,41,42,55,58,59,60,64,65,66,73,74,78,81,82]},{\"tag\":\"edge\",\"edge\":27,\"owners\":[6,21,34,44,45,46,48,49,56,57,59,67,68,71,72,74,79,80,81]},{\"tag\":\"edge\",\"edge\":30,\"owners\":[8,16,26,43,50,51,52,54,61,62,67,70,75,76,79]},{\"tag\":\"edge\",\"edge\":36,\"owners\":[11,22,30,37,45,51,56,63,65,67,69,71,77,79,82]}]}"
  "p cnf 101 209\n-14 -13 0\n-16 -13 0\n-18 -2 0\n-18 -13 0\n-18 -17 0\n-19 -18 0\n-21 -13 0\n-21 -19 0\n-22 -13 0\n-24 -18 0\n-25 -13 0\n-25 -24 0\n-26 -5 0\n-26 -13 0\n-26 -20 0\n-26 -24 0\n-27 -4 0\n-29 -13 0\n-29 -14 0\n-29 -24 0\n-31 -4 0\n-31 -13 0\n-31 -18 0\n-31 -19 0\n-31 -24 0\n-31 -26 0\n-32 -13 0\n-32 -18 0\n-32 -19 0\n-32 -25 0\n-32 -26 0\n-32 -27 0\n-32 -31 0\n-33 -18 0\n-33 -19 0\n-33 -25 0\n-33 -31 0\n-34 -20 0\n-35 -13 0\n-35 -24 0\n-36 -13 0\n-41 -13 0\n-42 -13 0\n-42 -18 0\n-42 -19 0\n-43 -19 0\n-44 -34 0\n-45 -42 0\n-45 -44 0\n-46 -15 0\n-46 -40 0\n-47 -20 0\n-47 -44 0\n-47 -45 0\n-49 -46 0\n-50 -5 0\n-50 -20 0\n-50 -27 0\n-50 -44 0\n-50 -45 0\n-50 -49 0\n-53 -46 0\n-55 -20 0\n-55 -44 0\n-55 -46 0\n-56 -18 0\n-57 -19 0\n-57 -43 0\n-58 -15 0\n-58 -23 0\n-58 -40 0\n-58 -47 0\n-58 -55 0\n-58 -56 0\n-59 -18 0\n-59 -20 0\n-59 -44 0\n-59 -58 0\n-61 -14 0\n-61 -27 0\n-61 -49 0\n-62 -18 0\n-62 -20 0\n-62 -39 0\n-62 -40 0\n-62 -44 0\n-62 -46 0\n-62 -58 0\n-3 -26 -33 0\n-13 -43 -45 0\n-19 -35 -45 0\n-11 -19 -58 0\n-21 3 5 27 28 31 34 0\n-8 -21 -44 0\n-21 -54 -58 0\n-21 -29 -33 0\n-1 4 5 18 20 23 32 34 0\n-1 52 53 55 60 61 0\n-15 60 61 0\n-25 52 53 55 61 0\n-26 53 55 61 0\n-27 52 55 60 0\n-29 52 53 55 60 61 0\n-30 52 53 60 0\n-55 1 25 26 27 29 60 0\n-7 2 24 31 32 33 48 0\n-35 2 31 32 33 0\n-43 2 24 31 32 48 0\n-11 2 24 31 32 33 60 0\n-24 11 56 57 0\n-51 2 31 32 33 0\n-57 2 24 31 32 60 0\n-10 4 18 26 32 37 46 48 0\n-50 4 18 26 32 37 48 0\n-4 12 52 58 60 0\n-12 4 18 26 32 52 60 0\n-32 12 52 58 0\n-12 -20 -61 0\n-12 -27 -59 0\n-6 54 55 62 0\n-16 62 0\n-36 54 55 62 0\n-39 55 0\n-41 54 55 62 0\n-8 54 59 62 63 0\n-22 62 63 0\n-54 8 45 47 63 0\n-9 55 61 62 0\n-30 62 0\n-49 55 0\n-34 62 63 0\n-47 61 0\n-50 59 61 62 0\n-54 28 61 0\n-61 28 54 0\n-53 38 62 0\n-46 63 0\n-63 46 0\n-64 17 51 56 57 0\n-65 34 47 49 50 0\n-66 16 36 39 40 41 0\n-67 18 20 31 44 58 0\n-68 15 25 26 27 29 30 0\n-69 24 32 33 0\n-70 14 21 22 45 0\n-71 35 42 43 0\n-72 13 19 0\n-73 64 0\n-73 65 0\n-74 66 67 0\n-75 67 0\n-76 73 75 0\n-77 73 0\n-76 74 0\n-77 75 0\n-78 68 0\n-78 69 0\n-79 71 72 0\n-80 71 0\n-80 72 0\n-81 70 80 0\n-82 70 0\n-81 79 0\n-82 80 0\n-83 78 82 0\n-84 78 0\n-83 81 0\n-84 82 0\n-85 76 0\n-85 77 84 0\n-85 83 0\n85 0\n-37 86 0\n-48 86 0\n-52 87 0\n-60 87 0\n-23 88 0\n-28 88 0\n-38 88 0\n-89 53 54 55 0\n-54 89 0\n-90 59 61 62 0\n-61 90 0\n-91 46 0\n-46 91 0\n-92 63 0\n-63 92 0\n-88 93 0\n-87 93 0\n-93 94 0\n-86 94 0\n-90 95 0\n-96 89 0\n-96 90 0\n-89 -90 96 0\n-97 91 92 0\n-98 91 0\n-91 -92 98 0\n-98 99 0\n-99 96 97 0\n-95 -98 100 0\n-96 99 0\n-100 101 0\n-94 -99 101 0\n-101 0\n6 8 16 22 23 36 39 40 41 45 46 47 54 55 59 62 63 0\n1 9 15 25 26 27 29 30 37 38 40 48 49 52 53 55 60 61 62 0\n2 7 11 24 31 32 33 35 42 43 48 51 56 57 60 0\n4 10 12 18 26 32 37 44 46 48 50 52 58 60 63 0\n"
  "210 76 0 172 169 0\n211 83 0 172 171 0\n212 74 0 210 154 0\n213 81 0 211 167 0\n214 79 0 213 163 0\n215 -100 0 205 203 0\n216 -98 94 0 215 190 189 176 175 188 179 191 174 173 197 201 184 192 50 51 55 62 65 87 183 101 98 100 103 104 128 102 207 0\n217 -91 98 0 184 198 137 187 0\n218 25 26 27 29 49 58 44 20 18 -55 15 47 34 30 93 0 172 189 176 188 177 105 143 156 166 170 153 155 149 151 140 142 56 21 33 97 0\n219 -25 -59 0 211 172 78 77 76 75 11 12 30 36 144 157 165 166 164 170 160 155 147 151 24 142 0\n220 -26 -59 0 172 78 77 76 75 14 16 26 31 142 151 155 170 166 168 157 164 144 160 35 147 0\n221 -27 -59 94 0 220 78 77 75 216 217 185 138 190 189 176 175 191 174 173 17 32 58 119 113 209 0\n222 73 32 24 -59 0 210 172 78 77 76 75 152 153 151 170 142 166 37 157 144 0\n223 32 -29 49 -59 47 34 22 86 0 172 20 19 220 78 77 76 75 174 173 222 149 140 60 114 21 142 151 155 170 166 168 157 162 144 145 96 0\n224 49 -55 -59 15 47 62 94 0 172 221 220 219 78 77 76 75 216 217 185 138 131 129 126 191 190 218 18 223 29 33 147 142 160 151 164 155 168 170 0\n225 -32 13 -59 0 172 78 77 76 75 29 33 147 142 160 151 164 155 168 170 0\n226 4 32 50 26 58 44 18 94 0 216 217 185 138 190 189 176 175 191 174 173 113 116 209 0\n227 -29 50 -59 94 0 172 220 78 77 76 75 18 20 225 226 21 142 151 155 170 166 168 157 164 144 160 35 147 0\n228 61 62 -99 0 205 172 204 190 188 179 136 129 216 217 185 138 186 196 200 194 193 189 176 178 132 134 99 182 180 75 76 77 78 219 220 221 224 61 227 143 156 166 170 155 151 142 21 33 226 0\n229 -31 18 32 44 58 94 0 191 174 173 21 26 114 226 0\n230 50 26 18 32 44 58 -61 34 22 94 0 210 172 229 81 79 190 189 176 175 226 115 118 142 151 155 152 170 149 168 140 162 164 54 160 145 7 8 147 0\n231 -50 31 18 44 58 14 22 0 172 57 60 142 151 155 170 168 162 164 145 160 7 8 147 0\n232 18 32 44 58 -61 34 22 94 0 210 172 81 80 79 190 188 178 229 231 230 13 15 16 142 151 155 152 170 149 166 168 140 157 162 54 144 145 89 93 0\n233 32 44 58 -61 34 22 94 0 190 189 176 191 174 232 3 10 23 34 44 66 106 108 109 112 107 111 208 0\n234 44 58 -61 34 22 94 0 172 190 189 175 233 27 28 29 33 117 147 118 160 142 164 151 168 155 170 0\n235 -44 -54 49 14 34 22 63 0 172 49 53 59 127 140 94 149 145 153 162 170 168 0\n236 -32 -72 0 27 29 147 0\n237 -19 -71 -45 0 48 46 91 146 0\n238 -84 21 15 27 14 30 22 0 166 168 156 162 164 145 159 160 237 147 11 14 18 143 0\n239 -13 -68 15 27 30 0 11 14 18 143 0\n240 62 -99 0 205 172 213 211 204 216 217 185 138 190 188 178 126 129 131 228 79 80 81 135 235 234 69 72 74 95 238 170 153 149 140 60 145 161 162 160 165 236 156 157 239 147 35 67 92 144 110 0\n241 -80 -69 13 0 159 160 236 147 35 45 46 144 146 40 0\n242 -31 -99 0 205 240 88 86 82 204 33 229 0\n243 -99 0 212 172 240 82 83 84 85 86 88 242 142 151 150 155 170 166 168 157 164 241 2 41 42 141 0\n244 -98 0 243 199 0\n245 -96 0 243 202 0\n246 -91 0 244 217 0\n247 -46 0 246 185 0\n248 -63 0 247 138 0\n249 -84 0 166 168 157 162 164 241 159 1 7 9 39 43 145 146 90 0\n250 77 0 249 172 170 0\n251 73 0 250 153 0\n252 75 0 250 155 0\n253 64 0 251 148 0\n254 65 0 251 149 0\n255 67 0 252 151 0\n256 -20 0 254 38 52 57 63 140 130 0\n257 -31 32 0 211 22 24 25 37 147 144 160 157 164 165 0\n258 -18 32 0 253 214 257 3 4 5 6 34 44 66 107 111 147 139 158 68 146 0\n259 -44 0 254 47 53 59 64 140 130 0\n260 -58 0 254 245 248 247 70 71 72 73 78 88 123 130 121 126 131 140 60 133 183 195 181 125 120 122 124 206 0\n261 32 0 256 255 260 259 257 258 142 0\n262 -18 0 261 28 0\n263 -31 0 261 33 0\n264 0 262 263 259 260 255 256 142 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record010_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record010
