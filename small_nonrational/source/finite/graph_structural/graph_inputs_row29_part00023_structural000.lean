module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00023Data
public import GraphInputsRow29Part00023Frames
public import GraphInputsRow29Part00023Leaves
public import GraphInputsRow29Part00023Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record000
def vertexColumn : Fields := ⟨10, hexnat% "e334cb332cc713ccab1a4eb26c5936c3a8e938ce8b92e2b86e8791e2785e0fb89d26c9e1745b170da358d9354d3352d2b46d4749d1743db0d33c2e8b92d2b2ac6b46c9b16f07a1e4749ca719d1725c5783d0f23c4f0bc1fb2138b1134b0a8a928ca0ea86918c60d9313252946439315254543530c3322c4b0ac1b21c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b4da6d369a49b6db6d369b4db6d26d36926924924d249249b492249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨90, by decide⟩, ⟨93, by decide⟩, ⟨96, by decide⟩, ⟨99, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4004800260300000000000", hexnat% "240000000512090000000000", 7486127996928, 3799912185593856, hexnat% "9018020032000000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record001
def vertexColumn : Fields := ⟨10, hexnat% "2ccb293ae1b46b1a8e938ce2b86e2785e0fb29c6539e1745c9715a364d3362d2b46d8749d1743de0f43b0f0ba2e4b4acab1ad1b26c5bc1e8761e4751ca719c9715e0f23c4f0bc1fb22c44d1323283a3192645836b0531a264932439c1685914c5495150d4c348d130cc8b12c2b06d0721c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "249b4da6db4da4924936db69b4d2492492492493492249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨84, by decide⟩, ⟨87, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40010000090000000000000", hexnat% "f000002000000000000", hexnat% "189000200800000000000000", hexnat% "80c0400000f000000000", 246572079598534656, 560750930165760]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record002
def vertexColumn : Fields := ⟨10, hexnat% "32ac693ae1b46b18ce2b86e2785e0fb29c6539e1745b14cd2b46d2745d0f783d0f23c4f0b8ad2b2ac6b86d1b26c5bc1e8761e4751ca719c9715c8f13c2f07ec84d2c24ca8a928ca0e8c6499160dac14c689924c90e4c5495150d703a0e4330d2344c3382c8b12c2b06d0721c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "369b49b6d369b49b6d2492492492492492492449249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80080000d000000000000", hexnat% "4004001440000000000000", hexnat% "420420000078000000000", hexnat% "1e000000000000000", 835628837109760, 842173130318282752]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record003
def vertexColumn : Fields := ⟨10, hexnat% "2cc4f2ca4eb86d1ac6c9b164da8e938ce4b8ae1b91e2785e0fac94e785d1725c568d9352d2b46d4749d17783d0f23c4e8b92d2b2ac6b46c9b16f07a1d8791d4731e2749ca719e1745c9715c3783d0f23c4f0bc1fb11343303cb09323283ab053132439c1685914c5495150d48d1342d07703a0e4330d2344c3322c4b0ac1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "249369b4da6db6d24924924924924924924934d34db4da6d2489249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨43, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨88, by decide⟩, ⟨91, by decide⟩, ⟨94, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "78040000000000000", hexnat% "78000000000000000000", hexnat% "a000081201200010000000000", hexnat% "14000106006002000000000000", 972777777210064896, hexnat% "d80000000000000000", hexnat% "490200000028880000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record010
def vertexColumn : Fields := ⟨10, hexnat% "b90f4ab26c4f0bc1f3a2d8ae2e4b52b4b2aaaa6ac6a9a96ac6a9a66398d6a3a4e8b92e2b86e4789e17ba1d86e16c5713c729aa6694e4b91e4e5355352d4754b4ad1b51d2745d0f783d0ec3c8ea368e6358ce364d5334f0ba2e4b8ad2b2ac6b26c5b31d2729c6745d0f23c4f0bf28c291a2585607929464a5194951542d0751324c5342c1b21c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6da6d36db69b6db4936db69b4da4d24924936db6db4926da6d24d2492449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨86, by decide⟩, ⟨93, by decide⟩, ⟨96, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40e001bea00e03ba800000", 18014398526259200, hexnat% "1000000400000011000000000", hexnat% "200000000000000004000000", hexnat% "80100000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4040013ea00e033a800000", hexnat% "1000000400000011000000000", 9223372039002259456, hexnat% "80100000004000000", hexnat% "20000040000001000000", hexnat% "200080000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "404001be200e03b8800000", hexnat% "1000000400000011000000000", 36028797052518400, hexnat% "80100000004000000", hexnat% "20000040000001000000", hexnat% "200080000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2040e001bde00f03bc000000", 58720256, 144115188075855872, hexnat% "480000001000000000", hexnat% "1000000000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "408001b5e00e03b8000000", hexnat% "60000000000000000000", hexnat% "1200000000000011000000000", 125829120, 720575940379279360, hexnat% "480000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80098de00e130c800000", hexnat% "1000000400000010000000000", hexnat% "200000000000000000000000", hexnat% "4060000000000000000000", 3602879701896396800, 3003121664]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2001bf600e0339800000", hexnat% "40000080000002000000", hexnat% "480000011000000000", hexnat% "1200000000000000000000000", hexnat% "4000000000000080000000", hexnat% "80000000000004000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "187000e0308000000", hexnat% "1000000400000011000000000", hexnat% "200080000000000004000000", hexnat% "4060000000000000000000", hexnat% "80820000000000000", 3512807709348986880, 3011510272]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c14 c2
  c15
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record027
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record027
def vertexColumn : Fields := ⟨10, hexnat% "ea358e9354e334cb332cab1acc725c5713cb2b2aaab1a9693ab1b26a9b1695936c3a8e938ce8b92e2b86e8791e2785e0fb89d26c96a5594e785d16c5695554d70da358d9354d3352d2b46d4749d1743db0d33c2e8b92ccb4ac6b46c9b0ef07a1e4731d2719d1725c3783d0f23c4f0bc1fa2a4a2a85aa1a46298564a4a946459494a54545528c5322c4b0ac1b21c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6db6d34d34d34da4db4db69b6d24db4936db6934d36da4924934924926d2489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨78, by decide⟩, ⟨83, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨91, by decide⟩, ⟨93, by decide⟩, ⟨95, by decide⟩, ⟨97, by decide⟩, ⟨99, by decide⟩, ⟨101, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2aa988420006a1fe483c000000", hexnat% "1800000000000000000", hexnat% "a0000001100000000", 695784701952, hexnat% "40000000400000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20188438606a1fe0d3c000000", hexnat% "28000000000000000000000000", hexnat% "80000001000000000", hexnat% "880000000000006000000000", hexnat% "200000000000008200000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a2188438006a1fe883c000000", hexnat% "20800000000000002000000000", hexnat% "a0000001100000000", hexnat% "80000000000004000000000", hexnat% "40000000600000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "aa188038e04a1febf3c000000", hexnat% "20000000000000000000000000", hexnat% "40000200000000000000", hexnat% "80000000000004000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "22088038e04a1fe1d3c000000", hexnat% "10040000200000000000000", hexnat% "28000000000000000000000000", 970662608896, hexnat% "880000000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20088038200a1fe083c000000", hexnat% "28010000000000000000000000", hexnat% "80600001000000000", hexnat% "80040000000004000000000", hexnat% "40000000700000000", hexnat% "a0000000000000a000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c9 c0
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2aa988410006a1fe823c000000", hexnat% "2800000000000000000", hexnat% "60000000500000000", 446676598784, hexnat% "80000001000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80188438a06a1fe133c000000", hexnat% "22000000000000000000000000", hexnat% "40000000400000000", hexnat% "a0000000000000a000000000", hexnat% "80000000000004800000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a0988438006a1fe423c000000", hexnat% "20800000000000002000000000", hexnat% "60000000500000000", hexnat% "200000000000008000000000", hexnat% "80000001800000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a8980438e0681fe7f3c000000", hexnat% "20000000000000000000000000", hexnat% "800000020000000000000", hexnat% "200000000000008000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80900438e0681fe173c000000", hexnat% "8800000020000000000000", hexnat% "22000000000000000000000000", 996432412672, hexnat% "a00000000000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8010043820601fe023c000000", hexnat% "22008000000000000000000000", hexnat% "400a0000400000000", hexnat% "200800000000008000000000", hexnat% "80000001900000000", hexnat% "880000000000006000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c18 c13
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c19 c12
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c20 c11
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2aa988400806a094ff3c000000", hexnat% "60000000000000000", 354042744143872, hexnat% "2800000200000000000", hexnat% "1000000080000000000"]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "988418e06a01eff3c000000", hexnat% "a00000000000000000000000", hexnat% "2000000200000000000", hexnat% "22000000000000c00000000000", hexnat% "8000000000001000000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "82988400e06a114ff3c000000", hexnat% "20800000000000400000000000", hexnat% "2800000220000000000", hexnat% "2000000000000800000000000", hexnat% "1000000080000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "888000e00a014ff3c000000", hexnat% "a10000000000000000000000", hexnat% "2000040000000800000000000", hexnat% "18000000a0000000000", hexnat% "2000600200000000000", hexnat% "28000000000001400000000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c26 c23
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c27 c22
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2aa988400406a114ff3c000000", hexnat% "a0000000000000000", 213305255788544, hexnat% "1800000080000000000", hexnat% "2000000200000000000"]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2188428e06a036ff3c000000", hexnat% "880000000000000000000000", hexnat% "1000000080000000000", hexnat% "28000000000001400000000000", hexnat% "2000000000000800000000000"]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "22988400e06a094ff3c000000", hexnat% "20800000000000400000000000", hexnat% "18000000a0000000000", hexnat% "8000000000001000000000000", hexnat% "2000000200000000000"]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2100400e060014ff3c000000", hexnat% "888000000000000000000000", hexnat% "8000800000001000000000000", hexnat% "10000a0080000000000", hexnat% "2800000220000000000", hexnat% "22000000000000c00000000000"]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c33 c30
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c34 c29
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "28a10800000001d6ea20000000", hexnat% "2088040000000000010000000", hexnat% "10400a0000004000000", hexnat% "2080600000008000000", hexnat% "800000280000000000", hexnat% "20000001500000000"]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20988428a06a1fe7f3c000000", hexnat% "1040000000000000000", hexnat% "a00000000000008000000000", hexnat% "28000000000000000000000000"]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20988438406a1fe5e3c000000", hexnat% "a0000000100000000", hexnat% "28000000000000000000000000", hexnat% "a0000000000000a000000000"]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "428a06017e1f18000000", hexnat% "10400a0000004000000", hexnat% "22008000000000800000000000", hexnat% "880000000000006000000000", hexnat% "8210800000000000020000000", 549755813888]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c39 c38
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c40 c37
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "28a9080000000174ff3c000000", hexnat% "2008040000000800000000000", hexnat% "60080000000000000", hexnat% "2080600000000000000", hexnat% "18000000a0000000000", 9007199254740992]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "28e060136ff3c000000", hexnat% "10000a0080000000000", hexnat% "888000000000000000000000", hexnat% "8210800000000000000000000", hexnat% "22000000000000c00000000000", hexnat% "40000000000000000000"]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2a988400006a1f6eb3c000000", hexnat% "2080000000000000000", hexnat% "28000000000000000000000000", hexnat% "1040000000000000000", 8881992368128, hexnat% "820000000000000000"]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "188410e06a17e3f3c000000", hexnat% "2800000000000000000", hexnat% "8200000000000000000000000", hexnat% "2080000000000000000000000", 141562122076160, hexnat% "20800000000000000000000000"]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2a988400006a1b4eb3c000000", hexnat% "60000000400000000", hexnat% "2080000000000000000", hexnat% "28000000000000400000000000", 8864812498944, hexnat% "1800000020000000000"]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "188410e06a13c3f3c000000", hexnat% "2800000020000000000", hexnat% "880000000000004000000000", hexnat% "8200000000000000000000000", 141287244169216, hexnat% "22000000000000400000000000"]
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2a98840000021b4eb34000000", hexnat% "28000000000000400000000000", hexnat% "60080000400000000", hexnat% "18000000a0000000000", hexnat% "2080600000008000000", 68719476736]
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "88804000002134eb14000000", hexnat% "60080000400000000", hexnat% "18000000a0000000000", hexnat% "8210800000000000020000000", hexnat% "22000000000000c00000000000", hexnat% "2080600000008000000", 68719476736]
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c49 c48
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c50 c47
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c51 c46
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c52 c45
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c53 c44
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c54 c43
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c55 c42
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c56 c41
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c57 c36
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c58 c35
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c59 c28
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c60 c21
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c61 c10
  c62
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record027_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record027_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record027_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record027_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record027_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record027_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record027_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record027_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record027_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record027
