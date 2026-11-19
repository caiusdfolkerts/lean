module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow23Part00011Data
public import GraphInputsRow23Part00011Frames
public import GraphInputsRow23Part00011Leaves
public import GraphInputsRow23Part00011Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00011.record095
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record095
def vertexColumn : Fields := ⟨10, hexnat% "a716a59a9665a1e2785e0fb915a69959595a364d8b49d1743d70da3a4d534cd4b4ae1b46c9b16c3ba1d8751cc749ca785d1715c3783c8fa506c871626486a198961382e07961a45911a619a1465854958344d0b41d60d4348c6344c9312c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "12492492492492492492492492492492489249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1008001a0000000000000", hexnat% "1510810000000000000", hexnat% "ec00000c000000000", hexnat% "a0200001a40000000000", hexnat% "1e000000000000000000", hexnat% "240000000080000000000", 3891110078048108544, 654209418526720, 21392098230009856]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record095_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record095_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record095_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record095_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record095_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record095_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record095_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record095_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record095_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00011.record095

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00011.record096
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record096
def vertexColumn : Fields := ⟨10, hexnat% "3925aa9a59a9665a1e2785e0fb915a699596956561d2745d0f78370da3c4d534ce8b92d4b8ad2b46c9b16c3ba1d8751cc749ca785d1715c3783c8f1b162a49921aa1a198961382e07961a45911a619194951342d0768360d4348c6384d1324e0b12c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "2492492492492492492492492492492492489249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81205f979ae0000000000", hexnat% "280a00000000000000000", 652835028992000, 469500261153374208, hexnat% "1004000000000000000000", hexnat% "8020000000000000000", hexnat% "1580000000000000000", hexnat% "560000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5785f913fffc000000000", 468374361246531584, 5206161169240293376, hexnat% "802000000000000000000", hexnat% "1080000000000000000000", hexnat% "200a00000000000000000", hexnat% "5002000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "144501ffffffc000000000", hexnat% "802000000000000000000", hexnat% "38000000000000000000", hexnat% "1e0000000000000000", hexnat% "100400000000000000000", hexnat% "280a00000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "47d7fb513ffc000000000", hexnat% "1180000000000000000000", 5215168368495034368, hexnat% "200800000000000000000", hexnat% "802000000000000000000", 183521684815347712]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1415ff97fffc000000000", hexnat% "4200000000000000000", hexnat% "38000000000000000000", 468374361246531584, hexnat% "802000000000000000000", hexnat% "280800000000000000000", hexnat% "1400000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4019f963ffc000000000", hexnat% "60000000000000000", hexnat% "2800000000000000000", hexnat% "38000000000000000000", hexnat% "a00000000000000000000", hexnat% "5600010000000000000", hexnat% "1580000000000000000000", 471752060967059456]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5785f507fffc000000000", 468374361246531584, 9871890383196127232, hexnat% "802000000000000000000", hexnat% "1080000000000000000000", hexnat% "200a00000000000000000", hexnat% "5002000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "47d7f7453ffc000000000", hexnat% "1180000000000000000000", 9880897582450868224, hexnat% "200800000000000000000", hexnat% "802000000000000000000", 183521684815347712]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c6 c11
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c12 c2
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "802001160500000000000", hexnat% "1004000802c000000000", hexnat% "280a00001a40000000000", hexnat% "1004012010000000000000", hexnat% "8020804010000000000", 468374361246531584, hexnat% "140500002080000000000", 13835058055282163712, hexnat% "421080000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c16 c9
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c17 c0
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record096_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record096_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record096_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record096_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record096_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record096_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record096_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record096_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record096_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00011.record096
