module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00122Data
public import GraphInputsRow24Part00122Frames
public import GraphInputsRow24Part00122Leaves
public import GraphInputsRow24Part00122Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record001
def vertexColumn : Fields := ⟨10, hexnat% "1f06d13c7897272b1a9695a4e9a68d936638ce4ba1e4785e0f9e1745b15c4f17265956539356352d4cd1743d70da358ce394d538cd331cd8b92d4b32d2b86d1b16c3ba1cc789e1715c3723c4f0bc1f5621c709a2528a683a19164a5854358341d30ca382c4b81c8709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36d34da69b6da6db6db69369349269b6db4934d3492692489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨68, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "204000001400000000000", 28147497738174464, hexnat% "10100000000a10400000", hexnat% "80000002006000000000", 434597364041252864, 3816816640, 549755813888]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record003
def vertexColumn : Fields := ⟨10, hexnat% "7c1e87325c6ca3a4d8ce8785e0f9e1745b15c4f1725a95a4e9966391e5c5c56554d58d9354d3352d8745d0f5a364cd38cd332ce8b32e2b86c5b0ed8731d2745c570dc8f13c2f07d542aa16839c1685514c4c92a545855151560d134a384c3382c8b0ae0705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6d36924d269b6924d24d269b4924934db492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4b43bb4980fe000000", hexnat% "200400000000000000", hexnat% "2000000002800000000", hexnat% "100000060000000000", 274877906944]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7b47934a80ea000000", 4432406249472, 11258999336861696, hexnat% "2000000002000000000", 1374456643584]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "220439308a8ea000000", 11258999336861696, hexnat% "420400000000000000", hexnat% "180000040000000000", 1374456643584, hexnat% "10000420000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7846a00fe8fe000000", hexnat% "10000400000000000", hexnat% "2000003000000000000", hexnat% "20018000000000000", 72057594037927936]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "22b05bb03e87e000000", 13196287016960, 144115188075855872, hexnat% "404000400000000000", hexnat% "100000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800b00fe8fe000000", hexnat% "2000003000000000000", hexnat% "20408000000000000", 216172782113783808, hexnat% "700000000000000000", hexnat% "14000400000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7946804600c4000000", hexnat% "20008008000000000", hexnat% "2000003002802000000", 8796629893120, 85568392920039424, 1374792187904]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7b47b34280e6000000", 13228499271680, hexnat% "2000000002000000000", 2251800216338432, 1374389534720]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5b413b4fe8fe000000", hexnat% "2000000000000000000", 180143985094819840, hexnat% "200400000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5b41304fe8fe000000", hexnat% "200080000000000000", hexnat% "2000003000000000000", 144115188075855872, 290482175965396992]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7b45104a8044000000", 36033197749829632, 11258999471079424, hexnat% "2000003002802000000", 1374389534720, 144115188075855872]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "209013b00285e000000", 180143987779174400, hexnat% "620400000000000000", 4611687667694829568, 11269994184704, hexnat% "100000440000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2090023002846000000", hexnat% "500000400000000000", hexnat% "24008008000000000", hexnat% "200410000000000000", 252201581817102336, 1374792187904, 15393162788864]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c21 c10
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c22 c9
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c23 c4
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record007
def vertexColumn : Fields := ⟨10, hexnat% "1f07a1cca71d25c9ca5aa3a71b16659366394e3392e8789e0f9e1745b15c4f13a6998e4b97169565535a34cd8749d0f5c358d9354cd38cd331ce4b32e2b86c9b0ed8751cc749d1725c3723c4f0bc1f651624c86a85916838c91a6152560d2346384c3382c4b0ae0705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db4d36926db4db6db4db6934926d36d24924d36da492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨59, by decide⟩, ⟨67, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200080f00700bc00000", 27021598032658432, hexnat% "a0000000208000000000", hexnat% "80000000a00000000", hexnat% "5000000000004000000", 3298534883328]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8700080d03fa1fc00000", hexnat% "80002000000000000", hexnat% "20000000200000000000", 27021597764222976]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100080d03fa1fc00000", 18577348462903296, hexnat% "4080000000000000000", hexnat% "2000020000000000000", hexnat% "a0000000200000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a0000004239a1e400000", 576461164637061120, hexnat% "4080000000000000000", 21110623253299200, hexnat% "2000020000000000000", hexnat% "1000000000000800000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a0000000228002000000", 577586789665996800, hexnat% "2000020000018000000", 21110623257493504, hexnat% "4080000000000000000", hexnat% "1000000010004000000", 386555445248]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record007_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record008
def vertexColumn : Fields := ⟨10, hexnat% "6e1cc6b1728e93a958d68d87633a2e6c571725a9c6699666394e4b9715a559695954d58d4b51d68d6354d3362d4b4ad58e5354cd38cd331cd4b32e2b4ae1b46c9b0ee4731e2719e1725c570dc8f13dd08382e70591544d14c5894a4c58348d0b61314c3382c2b81c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db69249b4d34db69b6934926924936926d2492692449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨58, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a04004e7376800000", hexnat% "4000004000001000000", hexnat% "1000000300000000000", 9225623838815944704, 27866022694354944, hexnat% "2c00000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "34284677e6287000000", hexnat% "800008000000800000", hexnat% "4000000000040000000", hexnat% "80000001000000000", 5100273664]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ca84077e6287000000", hexnat% "4000000000040800000", 29273397577908224, 5100273664, 68719476736]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30284027e2087000000", hexnat% "4000004004040800000", 5100273664, 29554872554618880, hexnat% "c80000000000000000", 77309411328]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30a00027e7262000000", hexnat% "4000004000001800000", 4630511616, hexnat% "c00020000000000000", 9513854214967656448, 18295873486192640]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "700046f7e6247800000", hexnat% "888000000000000000", hexnat% "420000000000000000", 6979321856, 68987912192]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30a04407e3206000000", hexnat% "4000004004041800000", 5100273664, hexnat% "808028000000000000", hexnat% "400003000000000000", 2147483648]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "480844d3043f7800000", hexnat% "420002002000000000", 81432579932160, hexnat% "80020000000000000", hexnat% "3000000040000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ca8020343202800000", 290482178112880640, 19984723363233792, hexnat% "4000000084040000000", 72568102977536, 4831838208]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10800007e13f7800000", hexnat% "808408000000000000", hexnat% "2420000000000000000", hexnat% "4000004004000000000", 844562369085440, 27021597764222976]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30a0000360202800000", hexnat% "4000004084040000000", 70442027057152, 29554872571396096, hexnat% "808400000000000000", 2751463424, hexnat% "400002002000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c15 c10
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c16 c9
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c17 c6
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c18 c5
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record010
def vertexColumn : Fields := ⟨10, hexnat% "761d46d23c7296a8ea968d8b693a2e1ba1e0f9d16c5c95a7196655936639715a55969565555356354d4b59362d1b61d1743d70da358e938ccb362e4b52ccb8ad2b1ae1b26c3ba1e4789ca719e1725c3783c4f0bc1f4e0c6705914c5494a61946439316152543530e0b12c2b81c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6db6924926936934926da6936db6924926924924924c9249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5922a1607e7ef800000", 68987912192, 4971973988617027584, hexnat% "2600000000000000000", hexnat% "40000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2001404f7ff800000", hexnat% "1000002030000000000", hexnat% "f00000000000000000", hexnat% "40600000000000000", 7566047373982433280, hexnat% "6000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "94451607f7ff800000", hexnat% "2600000000000000000", hexnat% "4022800000000000000", 144115188075855872, hexnat% "1000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4976486349969293312, hexnat% "40204000000000000", hexnat% "4022800000000000000", hexnat% "f00000000000000000", hexnat% "1000002000000000000", hexnat% "2000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "244471404f417800000", hexnat% "4202000000000000000", 16777216000, hexnat% "20802000000000000", hexnat% "1900000020000000000", 1099511627776]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1266f1607a3ff800000", hexnat% "6100000000000000000", hexnat% "400000001400000000", hexnat% "800000004000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5066f1601809c800000", 14545846272, hexnat% "400000001400000000", hexnat% "2300000000000000000", 7009386627072, hexnat% "800000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1b2040607e131800000", hexnat% "6002000000000000000", 11844714496, hexnat% "440010001000000000", 144115205322833920, 5260204364902957056]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6f66f0605f65c800000", hexnat% "1000000020000000000", 4503599677702144, 6979321856]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5b26d06010658800000", hexnat% "2000200000000000000", 7046430720, hexnat% "440010001000000000", 7559142440960, 50331648]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2226f040117fc800000", 4503599677702144, hexnat% "5000002000000000000", 7559142440960, hexnat% "540000000000000000", hexnat% "800000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [870892064789757952, hexnat% "900000004000000000", 7133701809754865664, hexnat% "5020000000000000000", hexnat% "640000000000000000", hexnat% "2000000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f04f0407f7ff800000", hexnat% "4020002000000000000", hexnat% "40010000000000000", hexnat% "2002000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "804f140117ff800000", hexnat% "4022000000000000000", 7559142440960, hexnat% "1000002000000000000", hexnat% "2700000000000000000", hexnat% "40000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "746f1401d49d800000", 4402375032832, hexnat% "5020002000000000000", hexnat% "800000022000000000", hexnat% "2000000000040000000", 9126805504]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5060c0601001d800000", 4688247212092686336, 16676552704, hexnat% "400000001400000000", hexnat% "2202200000000000000", 7559142440960, hexnat% "900000000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c21 c18
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c22 c15
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c23 c14
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c24 c13
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c25 c10
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c26 c9
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c27 c6
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c28 c5
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c29 c2
  c30
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record012
def vertexColumn : Fields := ⟨10, hexnat% "1f0761b4c71e26c9cac699a69966c59968d9362db0e5386e8791e0f9d13c5c96655936479656352d54d1b51d0f5c3a4d938ccb362e4b52ccb1ae1b46c9b0ed8751e2729c6785d1725c3743c4f0bc1f8711c708e252a0e438e12c619854358341d30ca318e0b12e0709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36d269b6db6da4d26d36db6936926da69249b6da493692489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2001b0007060103c00000", hexnat% "140000000010000000000", 17867667931136, 2314850210615918592, 550829555712, 18014398509481984]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2001320241040a6400000", 18577348462903296, hexnat% "140000001010000000000", hexnat% "80000000041000000", 4303355904, 7146825580544]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1400200030780c3800000", 2314867800654479360, hexnat% "190000000000000000", 18014403412623360, hexnat% "200000004000000000000", 274877906944]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3206210c1a6c00000", hexnat% "200000004000000000000", 7696598171648, hexnat% "180000000000000000", hexnat% "140000001000000000000", 1073741824]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "13000214c1e7c00000", 27021597764222976, 2305843009213693952, hexnat% "200000004000000000000", hexnat% "40080000020000000000", hexnat% "100000001010000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1400a0005078023800000", 2314867802801963008, hexnat% "200110000000000400000", 5435817984, 274877906944, 18577348462903296]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "220201280a2800000", hexnat% "140000001010000000000", 4672945389568, hexnat% "190000000000000000", hexnat% "200000006000000000000", 18014402871558144, 1073741824]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record012_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record012
