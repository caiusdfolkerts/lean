module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00012Data
public import GraphInputsRow16Part00012Frames
public import GraphInputsRow16Part00012Leaves
public import GraphInputsRow16Part00012Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00012.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record000
def vertexColumn : Fields := ⟨10, hexnat% "ccb1a8e8e62d8ce8b91e1783ecc7198e4e52d4cd8b51d1743dc8ea338f138cd332ce4b52ccb8ae1b16c3b89c6745c9715e0f43c8f0bf0a468c6298361381ec2519314a50d44d0770330e2328d130ce0b42c4b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "69a49a49a692692492492492492492491249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e378ddfbe9a0000000", hexnat% "80200001400000000", 9232379245773193216, 567347999932416, 360287970189639680, hexnat% "140000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e7f8a9df83e0000000", 22518307374497792, 360288038909116416, 1724171671306240, hexnat% "180000000400000000", 144115188075855872]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e2b9f9df83e0000000", hexnat% "14000004800000000", hexnat% "140000001000000000", 1724171671306240, 432345581407436800, hexnat% "80000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e2b8afe33000000000", hexnat% "1004000c880000000", hexnat% "40100040240000000", hexnat% "100400000400000000", 26393110904832, 148618787703226368, hexnat% "84000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c5 c0
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "eaf89fe37120000000", 432345581407436800, hexnat% "10040008880000000", 30787399319552, 81064801882603520, hexnat% "140000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "beefb246ffe0000000", 27487790694400, hexnat% "10040000000000000", 3553621580972032, hexnat% "401001000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "aeebb0067360000000", 3623990325149696, hexnat% "10040018880000000", hexnat% "100402000400000000", 26388279066624, hexnat% "401001000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e378d19fc1e0000000", 3483390275747840, hexnat% "80200001400000000", 81064801882603520, hexnat% "100402000000000000", hexnat% "48000000000000000", 34359738368]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c11 c14
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e27abfe37120000000", hexnat% "10040008880000000", hexnat% "180000000400000000", 30787399319552, 360287970189639680, hexnat% "48000000200000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c11 c16
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "ffffffffffe0000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c19 c15
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c20 c13
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c21 c6
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00012.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00012.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record009
def vertexColumn : Fields := ⟨10, hexnat% "1f32a3a87ac58d61d98e3386e1783e9c7293a479c54d51d58d5346d1743dc8ce3c4cd31cf0b62ccb8ad2b2ac6b16c3bc1d8731c6785d1725c570dc4f0bc1f332324388e8c47132469314554348d1370388e130cd0b22c2b41c8705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6936d349a4924d34d249249a493492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "601482c4677000000", 589971551185534976, 2630102182384369664, 703723948998656, 21440476741632, 68853694464]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2630137375346393088, 721313987559424, 87820192800833536, hexnat% "60040000000000000", 576465974983655424, 21357395968, 12163380936704]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record009_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00012.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00012.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record013
def vertexColumn : Fields := ⟨10, hexnat% "1f3323a87a35876c38ce1b85e0fb319a4e91e55535475c346d1743dc8ce3c4cd38cd331cf0ba2ccb2ac6b16c3bc1d8731c6725c570de0f43c4f0bc1f3322a4588e1c4c98a469315151548d1370388d130ce0b22c2b41c8705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6da6db49249a4d34d249249a493492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨64, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10000094244000000", 128352589380059136, 1013309916158361600, 708119848026112, 52845814480896, 19780337664, 2748779069440]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record013_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00012.record013

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00012.record034
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record034
def vertexColumn : Fields := ⟨10, hexnat% "1a639b1635876c38ce1ba1e17a59c95a53971535475c34cd1b45d68d63c4cd31cf0b32c6b86f0761cc719e1745c9715c3783d0f23c4f0be1c3885a498a6078e186459c1525296158341d30d2328c6314c4b06d0721c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "936db6924926d3692693492492492492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨53, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1154049603536945152, 657526645107720192, 6917529027641081856, hexnat% "40040200a108000000", 400222232510464, hexnat% "200200004210000000", 124017180672]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record034_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record034_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record034_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record034_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record034_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record034_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record034_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record034_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record034_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00012.record034

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00012.record033
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3b0ea368e6c5876c38ce2b86e8785e3a65936565397151d70d334ad1b61dc8da338f1334c73c2e8b32cab1ac9b16f0731ca719e1745c570de0f43c8f13c2f1721a4981e384c986459494651544d0770348ca384e0b22c1b41c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6db4924934d349249b492692692492492249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 37), (facetIndex 38), (facetIndex 50), (facetIndex 59), (facetIndex 60)]))
 (.leaf ([(facetIndex 36), (facetIndex 43), (facetIndex 46), (facetIndex 49)])))
 (.branch 3
 (.leaf ([(facetIndex 33), (facetIndex 51), (facetIndex 55), (facetIndex 57), (facetIndex 58)]))
 (.leaf ([(facetIndex 62), (facetIndex 63)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 34), (facetIndex 40), (facetIndex 47), (facetIndex 48)]))
 (.leaf ([(facetIndex 41), (facetIndex 53), (facetIndex 61)])))
 (.branch 7
 (.leaf ([(facetIndex 24), (facetIndex 27), (facetIndex 29), (facetIndex 30), (facetIndex 31), (facetIndex 32)]))
 (.leaf ([(facetIndex 25), (facetIndex 26), (facetIndex 28), (facetIndex 42)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6e809042840c8403ec001116db7dfez12;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 54), (facetIndex 56)]))
 (.branch 2
 (.leaf ([(facetIndex 67), (facetIndex 69)]))
 (.leaf ([(facetIndex 35), (facetIndex 39), (facetIndex 52)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 64), (facetIndex 65), (facetIndex 66)]))
 (.leaf ([(facetIndex 70), (facetIndex 72), (facetIndex 73)])))
 (.branch 6
 (.leaf ([(facetIndex 44), (facetIndex 45)]))
 (.leaf ([(facetIndex 68), (facetIndex 71)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "24d0e2db00000000200002d0004004z1a;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6, 7]
def grouped3_0007 : List Nat := [0]
def grouped3_0008 : List Nat := [0, 1, 2]
def grouped3_0010 : List Nat := [1]
def grouped3_0011 : List Nat := [1, 2]
def grouped3_0012 : List Nat := [2]
def grouped3_0013 : List Nat := [3]
def grouped3_0014 : List Nat := [3, 4]
def grouped3_0015 : List Nat := [3, 4, 5, 6]
def grouped3_0016 : List Nat := [4]
def grouped3_0017 : List Nat := [5, 6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00012.record033" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00012.record033" 30

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00012.record033" "{\"ridges\":[[10,769],[10,770],[34,162],[36,769],[40,162],[43,769],[43,770],[46,769],[46,770],[47,224],[48,162],[49,769],[49,770],[54,780],[56,788],[67,780],[69,788]],\"owners\":[[34,162,[72],[8,40,47,48,65,70]],[40,162,[70],[8,34,47,48,65,72]],[48,162,[65,70,72],[8,34,40,47]],[10,769,[54,56],[36,43,46,49]],[36,769,[],[10,43,46,49,54,56]],[43,769,[56],[10,36,46,49,54]],[46,769,[54],[10,36,43,49,56]],[49,769,[54,56],[10,36,43,46]],[10,770,[67,69],[36,43,46,49]],[43,770,[69],[10,36,46,49,67]],[46,770,[67],[10,36,43,49,69]],[49,770,[67,69],[10,36,43,46]],[47,224,[73],[19,57,61,70,72]],[54,780,[67],[]],[67,780,[54],[]],[56,788,[69],[]],[69,788,[56],[]]],\"edges\":[[44,[10,36,43,46,49,54,56,67,69]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00012.record033" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00012.record033\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-2,16],[-4,15],[-8,12,15,16],[-1,10,11],[-3],[-5,11],[-6,10],[-9,10,11],[-1,13,14],[-5,14],[-6,13],[-9,13,14],[-7,17],[-10,13],[-13,10],[-11,14],[-14,11],[-18,2,4,7,8],[-19,18],[-20,19],[-21,20],[21],[-10,22],[-11,22],[-13,23],[-14,23],[-12,24],[-15,25],[-16,25],[-17,25],[-23,26],[-22,-26,27],[-25,28],[-24,28],[-28,29],[-27,-29,30],[-30],[1,3,5,6,9,10,11,13,14]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":162,\"a\":34,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":162,\"a\":40,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":162,\"a\":48,\"owners\":[65,70,72]},{\"tag\":\"mate\",\"ridge\":769,\"a\":10,\"owners\":[54,56]},{\"tag\":\"mate\",\"ridge\":769,\"a\":36,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":769,\"a\":43,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":769,\"a\":46,\"owners\":[54]},{\"tag\":\"mate\",\"ridge\":769,\"a\":49,\"owners\":[54,56]},{\"tag\":\"mate\",\"ridge\":770,\"a\":10,\"owners\":[67,69]},{\"tag\":\"mate\",\"ridge\":770,\"a\":43,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":770,\"a\":46,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":770,\"a\":49,\"owners\":[67,69]},{\"tag\":\"mate\",\"ridge\":224,\"a\":47,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":780,\"a\":54,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":780,\"a\":67,\"owners\":[54]},{\"tag\":\"mate\",\"ridge\":788,\"a\":56,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":788,\"a\":69,\"owners\":[56]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[34,40,47,48],\"full_literals\":[-18,2,4,7,8]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-19,18,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-20,19,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-21,false,20],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":54,\"full_literals\":[-10,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":56,\"full_literals\":[-11,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":67,\"full_literals\":[-13,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":69,\"full_literals\":[-14,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":65,\"full_literals\":[-12,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":70,\"full_literals\":[-15,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":72,\"full_literals\":[-16,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":73,\"full_literals\":[-17,25]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-23,false,26],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-22,-26,27],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-25,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-24,false,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-28,false,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-27,-29,30],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":44,\"owners\":[10,36,43,46,49,54,56,67,69]}]}"
  "p cnf 30 38\n-2 16 0\n-4 15 0\n-8 12 15 16 0\n-1 10 11 0\n-3 0\n-5 11 0\n-6 10 0\n-9 10 11 0\n-1 13 14 0\n-5 14 0\n-6 13 0\n-9 13 14 0\n-7 17 0\n-10 13 0\n-13 10 0\n-11 14 0\n-14 11 0\n-18 2 4 7 8 0\n-19 18 0\n-20 19 0\n-21 20 0\n21 0\n-10 22 0\n-11 22 0\n-13 23 0\n-14 23 0\n-12 24 0\n-15 25 0\n-16 25 0\n-17 25 0\n-23 26 0\n-22 -26 27 0\n-25 28 0\n-24 28 0\n-28 29 0\n-27 -29 30 0\n-30 0\n1 3 5 6 9 10 11 13 14 0\n"
  "39 20 0 22 21 0\n40 19 0 39 20 0\n41 18 0 40 19 0\n42 1 5 6 9 10 11 13 14 0 5 38 0\n43 28 0 41 33 34 28 29 30 27 2 1 13 3 18 0\n44 29 0 43 35 0\n45 -27 0 44 37 36 0\n46 13 14 0 9 11 14 10 16 12 42 0\n47 23 0 25 26 46 0\n48 26 0 47 31 0\n49 -22 0 48 45 32 0\n50 -10 0 49 23 0\n51 -11 0 49 24 0\n52 -1 0 50 51 4 0\n53 -6 0 50 7 0\n54 -13 0 50 15 0\n55 -5 0 51 6 0\n56 -14 0 51 17 0\n57 -9 0 51 50 8 0\n58 0 53 52 55 57 50 51 54 56 42 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00012.record033_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00012.record033
