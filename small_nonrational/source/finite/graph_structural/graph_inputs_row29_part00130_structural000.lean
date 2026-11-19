module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00130Data
public import GraphInputsRow29Part00130Frames
public import GraphInputsRow29Part00130Leaves
public import GraphInputsRow29Part00130Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00130.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130.record002
def vertexColumn : Fields := ⟨10, hexnat% "7ce4a9a66b86c5a5655a364d876a398e338ae8791e1783ee469966785c5655556354d475a358d334ad8751d1743de0f13a4d9394d538cd33a2d8b32cab86d1b26f0791d4731e2749ca785d1715c3783d0f07c781b0721a85a0ea86618662384e0b8711a4590e685614652344d0b68360c6384d1314c3322c4b0ac1b81d0721c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "26da6db69249b49b69b6da4926d2492492492492492492492449249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨82, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨100, by decide⟩, ⟨104, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40f000000000000000000", hexnat% "103c0000000000000000000000", hexnat% "10040c0103000003c8000000000", 8940129045446656, hexnat% "80f20000000000000", hexnat% "7f0c0000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00130.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00130.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130.record003
def vertexColumn : Fields := ⟨10, hexnat% "38ca725c8f07ca68da2e87aa5996a398e5392e8789e1783ee2699964d98e4b91e785a559595635c368d6364d5362d4b61d2745d0f69364cd32ce8b52ccb4acab86c9b16c3ba1d8751d2785d1725e0f23c1f1d06c1c98a1a866158364384e0ba911c6896246919615154358350d1342d60c6324c530cd0b22c4b0ad0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db69b69b6926d249b6d34d2492492692492492692692492489249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨94, by decide⟩, ⟨98, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4473c20e961f771c000000000", hexnat% "160000000000000000", 2161730020161093632, hexnat% "b000000080000000000", 4398046511104]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "61c0be911f76bc000000000", 1008810714577502208, hexnat% "10000020000100000000000", hexnat% "146000000000000000", hexnat% "4402020000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "61808e801f761c000000000", hexnat% "10000020000100000000000", 2161730020161093632, hexnat% "4402420016000000000000000", hexnat% "30000000c0000000000", hexnat% "140000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4473c20e361f771c000000000", hexnat% "1c0000000000000000", 2161730020161093632, hexnat% "b000000080000000000", 4398046511104]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "52c0be311f75bc000000000", 1008810714577502208, hexnat% "20000080000200000000000", hexnat% "146000000000000000", hexnat% "4401020000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "52808e201f751c000000000", hexnat% "20000080000200000000000", 2161730020161093632, hexnat% "4401420016000000000000000", hexnat% "30000000c0000000000", hexnat% "140000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "700000000a0008000000000", hexnat% "800000154000000000000", 2161730020161093632, hexnat% "b010000080000000000", 127818226728960, hexnat% "4403420006003000000000000", hexnat% "fe0000010000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c11 c4
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00130.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00130.record003
