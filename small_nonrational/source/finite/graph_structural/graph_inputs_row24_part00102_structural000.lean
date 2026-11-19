module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00102Data
public import GraphInputsRow24Part00102Frames
public import GraphInputsRow24Part00102Leaves
public import GraphInputsRow24Part00102Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record009
def vertexColumn : Fields := ⟨10, hexnat% "3e2d43b29c670dcb48f23aa9a368ba1eac6a98e6c5a969595635a8e3392e2b86e8791e2785eb44f13a699364b91e6c5a94e5c5695955553568d3352d2b46d8751d2745dc4e5354c734ac6b86c5b0ef0791d4789d2785d1715e0f13c1f390ac468664382e464654342d18e1344c5342c2b06e0741c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6d36db6db6da6db6da49a6db6db6da6db6da49a6d2492492492492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨56, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨80, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200100400100400000000000", hexnat% "100000102004400000", hexnat% "1800001800000000000", 2203485995008, 1984274890752, 4051697664, 68719476736]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record009_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record010
def vertexColumn : Fields := ⟨10, hexnat% "f8b50ec570dc3c8ea368ba1eaa639b16a5996358ce4b8ae1ba1e4789e17ad13c5591e6c5a94e5c5695955553554d4b61d4745da8ce3c4e9334cb31cd2b1ae1b16c3bc1e8731e2749ca719e1745c9715e0f13c1f3906ca491aa18a64382e1a519164654344d0b61344d0b0ac1b81d0709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "da6db6da4d36d24d36da4da6db69349b49b692492692493692249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "122a0106c4637e7000000", hexnat% "10081000000000000000000", hexnat% "1800000c000000000", 141836999983104]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "281806c06d287000000", hexnat% "20200000000060000000", hexnat% "10080001000000000000000", 158913789952, hexnat% "101000000000000000000", 212205744160768]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "101a3a1806c06c7e3000000", 1152991942070501376, 137506062336, 141836999983104]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2121806c06c063000000", 212205744160768, hexnat% "2000000000304000000", hexnat% "100000000001400000000", hexnat% "10080801000000080000000", 137438953472]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000068c577e7000000", hexnat% "20200004000000000000", hexnat% "18000008000000000", hexnat% "181000000000000000000", hexnat% "10000801000000000000000", 2199023255552]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2020102cc53765000000", hexnat% "18040000000000000", hexnat% "3800000000000000000", hexnat% "180000000000000000000", 3023690530816, hexnat% "10000000000000080000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "101838010284017a4000000", 140876017827840, hexnat% "18044000000000000", hexnat% "20200000000000000000", 7421737041920, 1099511627776]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100818010280000a4000000", hexnat% "18044000000000000", hexnat% "120000000001000000000", hexnat% "2200000040001000000", 212206817902592, 167503724544, 3023690530816]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c13 c2
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record010
