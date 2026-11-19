module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00030Data
public import GraphInputsRow26Part00030Frames
public import GraphInputsRow26Part00030Leaves
public import GraphInputsRow26Part00030Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00030.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record000
def vertexColumn : Fields := ⟨10, hexnat% "f0aca72aaa9a99a56a3ab19c6a9a66659564d8ce2b86e2785e0fbc1b25c9aa669665598e6c5716a59959555535334ad1b49d1743de0f43b0dc3a8e6364d538cd33a2d8b92d4b32e2b2ac6b86d1b26c5b0ee8761e4751cc789d2729c6745c9715c3723c4f0bc1fa2a4a8a83a6194645836a26498a4396154545435"⟩
def kindColumn : Fields := ⟨3, hexnat% "1a69369a6d24db6d34d26d34da49b6da6db6db6d34da6db6d34d36db4da6db249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨20, by decide⟩, ⟨23, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨40, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨56, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨88, by decide⟩, ⟨90, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨96, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000100000200100000", hexnat% "9c000000000800000", hexnat% "b200000010000000000", hexnat% "13800000000000000000000", hexnat% "1640000000000000000000000", 43983149465600]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00030.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00030.record052
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record052
def vertexColumn : Fields := ⟨10, hexnat% "f08bae1b46a99a6a59962da4e5386e17bc12e785d16a569695654b59354d1b45de0f43b0dc3a8da3a4d9392d4b2ac6b26c5bc1e8761e2749ca719e1745c9715e0f43c3c2c83a919460d84e0b81e2c439915450d44d0b41da0d8390d4328c930cc4b0ac1b81d0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1a69b6d24934d36da492492492492492492492491249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3be1df00829d1000000000", 824158731808800768, hexnat% "20f000000000000000", hexnat% "41e000000000000000000", 38405597560832, 291959919593127936]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3be1df00429b1000000000", 842173130318282752, hexnat% "20f000000000000000", hexnat% "41e000000000000000000", 40604620816384, 291959919593127936]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3be1df0022995000000000", 851180329573023744, hexnat% "20f000000000000000", hexnat% "41e000000000000000000", 42528766164992, 291959919593127936]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3be1df0012993000000000", 855683929200394240, hexnat% "20f000000000000000", hexnat% "41e000000000000000000", 42666205118464, 291959919593127936]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "17ffe1fffffffe00000000", hexnat% "2800000000000000000000", hexnat% "1e0000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record052_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record052_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record052_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record052_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record052_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record052_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record052_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record052_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record052_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00030.record052
