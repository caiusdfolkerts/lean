module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00061Data
public import GraphInputsRow24Part00061Frames
public import GraphInputsRow24Part00061Leaves
public import GraphInputsRow24Part00061Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00061.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record000
def vertexColumn : Fields := ⟨10, hexnat% "bad1ac659a9635936a38ce4b89e2e745b1565a54d54d68d3352d2774370d63a4cd34ccb3a2ccb4acabc1e8731e2719e1745c9715e0f43c8f13c3cb089a0ea46519260d82e07ac12643991545494350b41da0e4350cc348c930cc8b0ac1b81d0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "249369b49249b4da492492492492492492449249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "15b6b6891651000000000", 165507286305865728, hexnat% "49000080000000000", hexnat% "80100400808800000000", hexnat% "24800000000000000000", 20203526160384, 81627743246090240]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1db6b6851619000000000", hexnat% "100400880800000000", 183521684815347712, hexnat% "49000000000000000", hexnat% "24800000000000000000", 24601572671488, 81627743246090240]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "15b6b6819615000000000", 199284283511144448, hexnat% "49000080000000000", hexnat% "80100400808800000000", hexnat% "24800000000000000000", 24326694764544, 81627743246090240]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1db6b6815611800000000", hexnat% "100400888000000000", 200410183417987072, hexnat% "49000000000000000", hexnat% "24800000000000000000", 24601572671488, 81627743246090240]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "1fffffffffff800000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00061.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00061.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record010
def vertexColumn : Fields := ⟨10, hexnat% "34aaaa9a2e8e6358b69394e4b91ed26a9a64b9394d52d64d5352d4774370ea338e9334f0ba2e4b52e2b4acab86d1b26e4731d2729c6745c9715e0f13c3cb08b20e9460d90e0b81eb04b10e5450d50d0b41da0e4350cc328c930ce0b42c2b06d0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36d369a49b69b4d2492492492492492492491249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "240481e9cbfa00000000", 434038812134342656, hexnat% "801000000400000000", 2882303761517117440, hexnat% "1400000000000000000", 4556376185503744]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c03802d7fe00000000", hexnat% "4008000000000000000", hexnat% "20040008080000000000", 477381560501272576, 5946158883012608, 90071992547409920]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "180375fb78600000000", hexnat% "400800002000000000", hexnat% "4008000001000000000", hexnat% "20040000480000000000", 309237645312, 45035996273704960]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c038069ffe00000000", hexnat% "4008000000000000000", hexnat% "20040008400000000000", 477381560501272576, 4820258976169984, 90071992547409920]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40381ff9b600000000", hexnat% "20040000000000000000", hexnat% "1800000000000000000", hexnat% "4008000020000000000", 279223176896970752, 288235083435868160]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400800413b000000000", 4035225274713899008, hexnat% "20040008480000000000", hexnat% "1c00000000000000000", 432350271511724032, 5523963597815808, 135107988821114880]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00061.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00061.record037
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record037
def vertexColumn : Fields := ⟨10, hexnat% "b8a9a599564d8b69394e4b8ae4789eb85b1d25a9a6599555352d64d5352d2b49db0ea398d6338e9354d332ce4b52d2b2ae1b46e4751d2729d1725c570de0f43c8f13c2f5911ca289a1981e586894649951525195154341da0e4328c6324e0b22c1b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1a4db6db49b6d249b49a49249b49b492492492492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4301448e3e70000000", hexnat% "100000000000000000000", 36100269569736704, 15762598695796736, hexnat% "8080000000c080000000", 14699749183737298944]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10042017c8c6e70000000", hexnat% "10000020000000000", 36100269569736704, hexnat% "80800000009080000000", 14699749183737298944]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30100062800000000", hexnat% "100400000000040000000", hexnat% "8080001000d080000000", 57570428830351360, 14699749183737298944, 9078668047417344, 30333206528]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record037_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record037_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record037_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record037_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record037_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record037_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record037_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record037_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00061.record037_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00061.record037
