module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00071Data
public import GraphInputsRow24Part00071Frames
public import GraphInputsRow24Part00071Leaves
public import GraphInputsRow24Part00071Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

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
