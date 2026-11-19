module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00128Data
public import GraphInputsRow24Part00128Frames
public import GraphInputsRow24Part00128Leaves
public import GraphInputsRow24Part00128Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record003
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 63772748152832, (certNat% 4), 4503737066323968, (certNat% 5)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), (certNat% 8), (certNat% 9)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), 41781441855488, 9007336693694464, 9295429643777605632, 1125899906842624]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 12), (certNat% 13), 9007371053432832, (certNat% 14)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), 41781441855488, (certNat% 13), (certNat% 14), 562949953421312]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), 41781441855488, (certNat% 17), (certNat% 18), 9295429633040187392, (certNat% 19)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), 1688862745165824, 540431955284459520, (certNat% 22), (certNat% 23)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 25), (certNat% 26), (certNat% 27), 1688862745165824, (certNat% 13)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c13 c14
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 29), 9223372041149743104, 41781441855488]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), 9223372041149743104, (certNat% 31), 41781441855488, 1125899906842624]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), 41782515597312, 1688854155231232, 9331458427911667712, (certNat% 26), (certNat% 33)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 26), (certNat% 35), (certNat% 36), (certNat% 37), 4503599627370496]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 38)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 39), (certNat% 40), 59373627899904, 1125899906842624, (certNat% 41), (certNat% 29)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 43), 1132496976609280, (certNat% 44), 52776558133248, 432345615767175168]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), (certNat% 46), 69269232549888, (certNat% 47), 1829587348619264, 288230427691319296, 6755399441055744]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c28 c25
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c29 c22
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c30 c21
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c31 c11
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c32 c10
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c33 c9
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c34 c0
  c35
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record003_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record007
def vertexColumn : Fields := ⟨10, (certNat% 48)⟩
def kindColumn : Fields := ⟨3, (certNat% 49)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), 426612659060736, (certNat% 51), 144116837343297536, (certNat% 52), (certNat% 53)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), 301721452544, 9020393394274304, 422214612549632, (certNat% 55), (certNat% 56)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 57), 13519612155002880, (certNat% 58), 144116837343297536, (certNat% 59), (certNat% 60)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 61), (certNat% 62), 323258566049792, (certNat% 63), 144117120811139072, 13519612155002880]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 64), 11270011364573184, (certNat% 65), (certNat% 63), 144117113294946304, 426612659060736]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 66), (certNat% 67), 283467841536, 13519594975133696]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 68), 294669116243968, (certNat% 69), 284541583360, 13510798882111488]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), 13519603565068288, (certNat% 71), (certNat% 72), 144116013783318528, 426612659060736]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 73), (certNat% 74), (certNat% 62), (certNat% 8), 144117120811139072, 13510816061980672]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 75), (certNat% 59), (certNat% 76), 426613732802560, 13519620744937472, (certNat% 77), 144117112221204480]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c12 c9
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c14 c3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c15 c2
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c16 c1
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c17 c0
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record007_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record008
def vertexColumn : Fields := ⟨10, (certNat% 78)⟩
def kindColumn : Fields := ⟨3, (certNat% 79)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 80), (certNat% 81), (certNat% 82), 275414777856, (certNat% 83), 2199023255552]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [5780224455632486400, (certNat% 84), 345744867328, (certNat% 85), (certNat% 86), (certNat% 87)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 88), 9007268511088640, (certNat% 82), 274877906944, (certNat% 89), (certNat% 83)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [15483323547648000, 3458766163087982592, 4899986763323277312, (certNat% 90), (certNat% 91), 362924736512, 17592320262144]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record008_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record000
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2788f2729aa5a8e87a599561d92e2b83ed86719a699966391e565556351d62d4b4ad8743d98e5354cd38cc7392e2b4acab1ae1b16c3b61d4729c6745c570dd0f27162269262588e0b81e985619462986499494952342d0754348c6324c5322c2b06d0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db4da49249269b69249249a692492492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 70), (facetIndex 71), (facetIndex 72)]))
 (.leaf ([(facetIndex 36), (facetIndex 38), (facetIndex 45), (facetIndex 62), (facetIndex 75)])))
 (.branch 3
 (.leaf ([(facetIndex 33), (facetIndex 34), (facetIndex 35), (facetIndex 37), (facetIndex 39)]))
 (.leaf ([(facetIndex 42), (facetIndex 55), (facetIndex 64), (facetIndex 65), (facetIndex 66)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 53), (facetIndex 67), (facetIndex 68), (facetIndex 69)]))
 (.leaf ([(facetIndex 41), (facetIndex 48), (facetIndex 50), (facetIndex 51), (facetIndex 52)])))
 (.branch 7
 (.leaf ([(facetIndex 46), (facetIndex 54), (facetIndex 56), (facetIndex 57), (facetIndex 58)]))
 (.leaf ([(facetIndex 40), (facetIndex 43), (facetIndex 44)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2000248db0401b67a5b4518feef45149z19;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 59), (facetIndex 61)]))
 (.branch 2
 (.leaf ([(facetIndex 73), (facetIndex 74)]))
 (.leaf ([(facetIndex 47), (facetIndex 49), (facetIndex 63)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 76), (facetIndex 77), (facetIndex 78)]))
 (.leaf ([(facetIndex 79), (facetIndex 80), (facetIndex 82)])))
 (.branch 6
 (.leaf ([(facetIndex 60)]))
 (.leaf ([(facetIndex 81)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1348db0480000004050000000104z23;"⟩
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
def grouped2_0010 : List Nat := [4, 5, 6, 7]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7]
def grouped2_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [0]
def grouped3_0016 : List Nat := [0, 1, 2]
def grouped3_0018 : List Nat := [1]
def grouped3_0019 : List Nat := [1, 2]
def grouped3_0020 : List Nat := [2]
def grouped3_0021 : List Nat := [3]
def grouped3_0022 : List Nat := [3, 4]
def grouped3_0023 : List Nat := [3, 4, 5, 6]
def grouped3_0024 : List Nat := [4]
def grouped3_0025 : List Nat := [5]
def grouped3_0026 : List Nat := [5, 6]
def grouped3_0027 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record000" "{\"atoms\":[{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record000" 72

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record000" "{\"ridges\":[[39,131],[41,82],[42,536],[44,41],[44,42],[44,131],[50,82],[50,131],[51,82],[52,82],[53,608],[54,41],[57,41],[60,564],[65,536],[65,592],[67,41],[68,592],[68,608],[69,608],[70,42],[72,42],[76,42],[77,42],[79,42],[80,562],[81,564],[82,120]],\"owners\":[[41,82,[73,74,80],[8,34,48,50,51,52,76,78]],[50,82,[73,74,76,78,80],[8,34,41,48,51,52]],[51,82,[73,76,78,80],[8,34,41,48,50,52,74]],[52,82,[73,74,76],[8,34,41,48,50,51,78,80]],[42,536,[81,82],[19,55,64,65,66,77,78]],[65,536,[77,81],[19,42,55,64,66,78,82]],[65,592,[80],[21,52,68,78,82]],[68,592,[78],[21,52,65,80,82]],[53,608,[82],[23,67,68,69,79,80]],[68,608,[79],[23,53,67,69,80,82]],[69,608,[79,80,82],[23,53,67,68]],[80,562,[49,77],[]],[60,564,[81],[]],[81,564,[60],[]],[82,120,[63,76],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record000" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record000\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-9,-7],[-11,-1],[-11,-5],[-11,-8],[-11,-10],[-12,-11],[-15,-2],[-15,-3],[-15,-4],[-15,-7],[-18,-10],[-18,-13],[-18,-16],[-18,-17],[-20,-7],[-21,-11],[-23,-11],[-24,-13],[-26,-7],[-28,-7],[-29,-10],[-31,-10],[-31,-25],[-33,-11],[-34,-22],[-37,-7],[-37,-10],[-37,-24],[-37,-32],[-38,-7],[-39,-10],[-40,-10],[-41,-7],[-41,-19],[-41,-24],[-41,-30],[-41,-32],[-6,-11,-15],[-11,-19,-29],[-11,-22,-29],[-11,-32,-40],[-11,-34,-37],[-11,-34,-38],[-11,-34,-40],[-8,35,36,41],[-15,35,36,37,39,41],[-16,35,37,39,41],[-17,35,36,37],[-9,42,43],[-27,38,42],[-27,41],[-30,39],[-18,43],[-30,40],[-31,40,41,43],[-41,14,38],[-24,42],[-42,24],[-43,25,37],[-44,1,32,33,34],[-45,2,3,4,5,6],[-46,9,20,26,27,28],[-47,18,29,30,31],[-48,8,13,15,16,17],[-49,12,19,21,22,23],[-50,7,10,11],[-51,44],[-52,45],[-52,46],[-53,51],[-53,52],[-54,47],[-54,48],[-55,49],[-55,50],[-56,54],[-56,55],[-57,53],[-57,56],[57],[-35,58],[-36,58],[-14,59],[-25,59],[-39,60],[-61,40,41,43],[-62,24],[-24,62],[-63,42],[-42,63],[-59,64],[-58,64],[-64,65],[-60,66],[-67,61],[-68,62,63],[-69,62],[-62,-63,69],[-69,70],[-70,67,68],[-66,-69,71],[-71,72],[-65,-70,72],[-72]],\"atoms\":[{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":42,\"b\":40},{\"tag\":\"incompatible\",\"a\":44,\"b\":32},{\"tag\":\"incompatible\",\"a\":44,\"b\":37},{\"tag\":\"incompatible\",\"a\":44,\"b\":41},{\"tag\":\"incompatible\",\"a\":44,\"b\":43},{\"tag\":\"incompatible\",\"a\":46,\"b\":44},{\"tag\":\"incompatible\",\"a\":50,\"b\":33},{\"tag\":\"incompatible\",\"a\":50,\"b\":34},{\"tag\":\"incompatible\",\"a\":50,\"b\":35},{\"tag\":\"incompatible\",\"a\":50,\"b\":40},{\"tag\":\"incompatible\",\"a\":53,\"b\":43},{\"tag\":\"incompatible\",\"a\":53,\"b\":48},{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":53,\"b\":52},{\"tag\":\"incompatible\",\"a\":55,\"b\":40},{\"tag\":\"incompatible\",\"a\":56,\"b\":44},{\"tag\":\"incompatible\",\"a\":58,\"b\":44},{\"tag\":\"incompatible\",\"a\":60,\"b\":48},{\"tag\":\"incompatible\",\"a\":64,\"b\":40},{\"tag\":\"incompatible\",\"a\":66,\"b\":40},{\"tag\":\"incompatible\",\"a\":67,\"b\":43},{\"tag\":\"incompatible\",\"a\":69,\"b\":43},{\"tag\":\"incompatible\",\"a\":69,\"b\":63},{\"tag\":\"incompatible\",\"a\":71,\"b\":44},{\"tag\":\"incompatible\",\"a\":72,\"b\":57},{\"tag\":\"incompatible\",\"a\":76,\"b\":40},{\"tag\":\"incompatible\",\"a\":76,\"b\":43},{\"tag\":\"incompatible\",\"a\":76,\"b\":60},{\"tag\":\"incompatible\",\"a\":76,\"b\":70},{\"tag\":\"incompatible\",\"a\":77,\"b\":40},{\"tag\":\"incompatible\",\"a\":78,\"b\":43},{\"tag\":\"incompatible\",\"a\":79,\"b\":43},{\"tag\":\"incompatible\",\"a\":80,\"b\":40},{\"tag\":\"incompatible\",\"a\":80,\"b\":54},{\"tag\":\"incompatible\",\"a\":80,\"b\":60},{\"tag\":\"incompatible\",\"a\":80,\"b\":68},{\"tag\":\"incompatible\",\"a\":80,\"b\":70},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[39,44,50]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[44,54,67]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[44,57,67]},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[44,70,79]},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[44,72,76]},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[44,72,77]},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[44,72,79]},{\"tag\":\"mate\",\"ridge\":82,\"a\":41,\"owners\":[73,74,80]},{\"tag\":\"mate\",\"ridge\":82,\"a\":50,\"owners\":[73,74,76,78,80]},{\"tag\":\"mate\",\"ridge\":82,\"a\":51,\"owners\":[73,76,78,80]},{\"tag\":\"mate\",\"ridge\":82,\"a\":52,\"owners\":[73,74,76]},{\"tag\":\"mate\",\"ridge\":536,\"a\":42,\"owners\":[81,82]},{\"tag\":\"mate\",\"ridge\":536,\"a\":65,\"owners\":[77,81]},{\"tag\":\"mate\",\"ridge\":592,\"a\":65,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":592,\"a\":68,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":608,\"a\":53,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":608,\"a\":68,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":608,\"a\":69,\"owners\":[79,80,82]},{\"tag\":\"mate\",\"ridge\":562,\"a\":80,\"owners\":[49,77]},{\"tag\":\"mate\",\"ridge\":564,\"a\":60,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":564,\"a\":81,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":120,\"a\":82,\"owners\":[63,76]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[32,70,71,72],\"full_literals\":[-44,1,32,33,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[33,34,35,37,39],\"full_literals\":[-45,2,3,4,5,6]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[42,55,64,65,66],\"full_literals\":[-46,9,20,26,27,28]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[53,67,68,69],\"full_literals\":[-47,18,29,30,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[41,48,50,51,52],\"full_literals\":[-48,8,13,15,16,17]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[46,54,56,57,58],\"full_literals\":[-49,12,19,21,22,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[40,43,44],\"full_literals\":[-50,7,10,11]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-51,44,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-52,45,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-52,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-53,51,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-53,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-54,47,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-54,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-55,49,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-55,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-56,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-56,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-57,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-57,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":73,\"full_literals\":[-35,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":74,\"full_literals\":[-36,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":49,\"full_literals\":[-14,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":63,\"full_literals\":[-25,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":78,\"full_literals\":[-39,60]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[79,80,82],\"full_literals\":[-61,40,41,43]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[60],\"full_literals\":[-62,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":60,\"full_literals\":[-24,62]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[81],\"full_literals\":[-63,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":81,\"full_literals\":[-42,63]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-67,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-68,62,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-69,62,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-62,-63,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-69,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-70,67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-66,-69,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-71,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-65,-70,72],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true}]}"
  "105 53 0 80 78 0\n106 56 0 80 79 0\n107 51 0 105 70 0\n108 52 0 105 71 0\n109 54 0 106 76 0\n110 55 0 106 77 0\n111 44 0 107 67 0\n112 45 0 108 68 0\n113 46 0 108 69 0\n114 47 0 109 72 0\n115 48 0 109 73 0\n116 49 0 110 74 0\n117 50 0 110 75 0\n118 -71 0 104 102 0\n119 -69 58 0 118 115 82 81 97 101 87 94 18 28 35 85 46 48 45 47 64 0\n120 -62 69 0 87 98 57 90 0\n121 -37 0 117 111 26 27 29 66 2 24 42 60 0\n122 -15 10 0 117 112 7 8 9 10 66 3 38 61 0\n123 -11 -40 0 111 2 24 41 44 60 0\n124 41 -70 0 121 104 117 113 103 93 92 119 120 88 58 91 84 59 49 89 96 100 95 51 86 32 123 66 15 19 20 62 0\n125 -10 -70 0 121 104 114 124 36 103 93 91 84 59 53 21 22 63 0\n126 -70 0 104 117 111 103 93 91 83 124 33 37 56 125 66 2 24 43 60 0\n127 -69 0 126 99 0\n128 -62 0 127 120 0\n129 -24 0 128 88 0\n130 -42 0 129 58 0\n131 -18 -11 0 115 5 122 4 12 13 14 64 0\n132 -29 -11 0 116 17 16 6 39 40 65 0\n133 -11 0 114 121 116 111 2 6 16 17 24 123 54 131 132 63 23 59 55 34 37 65 60 25 0\n134 -7 0 113 130 1 15 19 20 30 62 50 0\n135 10 0 134 117 133 66 0\n136 -18 0 135 11 0\n137 -29 0 135 21 0\n138 -31 0 135 22 0\n139 -39 0 135 31 0\n140 30 0 138 114 137 136 63 0\n141 0 140 139 52 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record017
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "23c56a6659a5635a365392e2b85e0fb615663999565a54d58d54d8b52d2b61d1743d98d6394d5334e3362d4b2ad1b16c3b91d4731e2749ca719e170dd0f13e542712a268961588e0b81e945292664589615254552342d0754348c9314d0b22c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6936924db4d24d24926924d2492492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 50), (facetIndex 68)]))
 (.branch 2
 (.leaf ([(facetIndex 62), (facetIndex 69)]))
 (.leaf ([(facetIndex 75), (facetIndex 81)]))))
 (.branch 4
 (.leaf ([(facetIndex 76), (facetIndex 82)]))
 (.branch 5
 (.leaf ([(facetIndex 55), (facetIndex 66), (facetIndex 70)]))
 (.leaf ([(facetIndex 79), (facetIndex 80)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "d5a034001081000400008z29;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4, 5]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record017" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record017" 37

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record017" "{\"ridges\":[[12,321],[12,322],[19,545],[40,545],[42,322],[48,321],[50,562],[52,321],[52,322],[54,322],[55,610],[61,545],[63,545],[67,545],[68,568],[70,864],[76,562],[79,356],[80,610],[82,568]],\"owners\":[[12,321,[62,66,69,70],[42,48,52,54]],[48,321,[66,70],[12,42,52,54,62,69]],[52,321,[62,66,70],[12,42,48,54,69]],[12,322,[75,79,81],[42,48,52,54]],[42,322,[81],[12,48,52,54,75,79]],[52,322,[75,79],[12,42,48,54,81]],[54,322,[75,81],[12,42,48,52,79]],[19,545,[50,55,68,70],[40,61,63,67]],[40,545,[68,70],[19,50,55,61,63,67]],[61,545,[50,55,70],[19,40,63,67,68]],[63,545,[55,70],[19,40,50,61,67,68]],[67,545,[50,68],[19,40,55,61,63,70]],[50,562,[76],[]],[76,562,[50],[]],[55,610,[80],[]],[80,610,[55],[]],[79,356,[66],[]],[68,568,[82],[]],[82,568,[68],[]],[70,864,[],[]]],\"edges\":[[38,[19,40,50,55,61,63,67,68,70,76,80,82]],[40,[12,42,48,52,54,62,66,69,70,75,79,81]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record017" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record017\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-13,-9],[-13,-10],[-21,-13],[-1,11,13,16,17],[-5,13,17],[-7,11,13,17],[-1,18,20,22],[-4,22],[-7,18,20],[-8,18,22],[-2,6,9,15,17],[-3,15,17],[-10,6,9,17],[-12,9,17],[-14,6,15],[-6,19],[-19,6],[-9,21],[-21,9],[-20,13],[-15,23],[-23,15],[-17],[-6,24],[-15,24],[-11,25],[-16,25],[-18,26],[-22,26],[-19,27],[-23,27],[-9,28],[-13,28],[-21,29],[-26,30],[-25,30],[-30,31],[-24,31],[-24,-30,32],[-28,33],[-28,-29,34],[-34,36],[-27,35],[-27,-33,36],[-31,-36,37],[-32,-35,37],[-37],[2,3,6,9,10,12,14,15,17,19,21,23],[1,4,5,7,8,11,13,16,17,18,20,22]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":66,\"b\":55},{\"tag\":\"incompatible\",\"a\":66,\"b\":61},{\"tag\":\"incompatible\",\"a\":80,\"b\":66},{\"tag\":\"mate\",\"ridge\":321,\"a\":12,\"owners\":[62,66,69,70]},{\"tag\":\"mate\",\"ridge\":321,\"a\":48,\"owners\":[66,70]},{\"tag\":\"mate\",\"ridge\":321,\"a\":52,\"owners\":[62,66,70]},{\"tag\":\"mate\",\"ridge\":322,\"a\":12,\"owners\":[75,79,81]},{\"tag\":\"mate\",\"ridge\":322,\"a\":42,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":322,\"a\":52,\"owners\":[75,79]},{\"tag\":\"mate\",\"ridge\":322,\"a\":54,\"owners\":[75,81]},{\"tag\":\"mate\",\"ridge\":545,\"a\":19,\"owners\":[50,55,68,70]},{\"tag\":\"mate\",\"ridge\":545,\"a\":40,\"owners\":[68,70]},{\"tag\":\"mate\",\"ridge\":545,\"a\":61,\"owners\":[50,55,70]},{\"tag\":\"mate\",\"ridge\":545,\"a\":63,\"owners\":[55,70]},{\"tag\":\"mate\",\"ridge\":545,\"a\":67,\"owners\":[50,68]},{\"tag\":\"mate\",\"ridge\":562,\"a\":50,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":562,\"a\":76,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":610,\"a\":55,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":610,\"a\":80,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":356,\"a\":79,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":568,\"a\":68,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":568,\"a\":82,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":864,\"a\":70,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":50,\"full_literals\":[-6,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":68,\"full_literals\":[-15,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":62,\"full_literals\":[-11,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":69,\"full_literals\":[-16,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":75,\"full_literals\":[-18,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":81,\"full_literals\":[-22,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":76,\"full_literals\":[-19,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":82,\"full_literals\":[-23,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":55,\"full_literals\":[-9,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":66,\"full_literals\":[-13,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":80,\"full_literals\":[-21,29]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-26,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-25,false,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-24,false,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-24,-30,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-28,false,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-28,-29,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-34,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-27,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-27,-33,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-31,-36,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-32,-35,37],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[19,40,50,55,61,63,67,68,70,76,80,82]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[12,42,48,52,54,62,66,69,70,75,79,81]}]}"
  "50 2 3 6 9 10 12 14 15 19 21 23 0 23 48 0\n51 1 4 5 7 8 11 13 16 18 20 22 0 23 49 0\n52 -13 24 0 23 24 25 15 22 12 17 1 2 3 14 11 50 0\n53 31 0 23 37 38 35 36 28 29 26 27 8 10 52 5 20 4 6 51 0\n54 -36 0 53 47 45 0\n55 -34 0 54 42 0\n56 15 6 9 0 23 13 17 19 14 12 22 15 11 50 0\n57 30 13 5 0 20 35 36 28 29 26 27 7 9 8 10 51 0\n58 27 9 0 30 31 16 21 56 0\n59 9 -30 0 47 58 43 46 39 24 25 56 0\n60 -9 0 55 18 32 34 41 0\n61 27 0 60 58 0\n62 -30 0 60 59 0\n63 -33 0 61 54 44 0\n64 -28 0 63 40 0\n65 -13 0 64 33 0\n66 -5 0 65 23 5 0\n67 0 65 66 62 57 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record017
