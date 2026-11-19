module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00055Data
public import GraphInputsRow29Part00055Frames
public import GraphInputsRow29Part00055Leaves
public import GraphInputsRow29Part00055Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00055.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000
def vertexColumn : Fields := ⟨10, hexnat% "3b0ce1b89e2746b0bc1f3a2aca72d2b2a6aa6a96a3a2e87a69a66958d68d8b61d98e4b8ae1b89e1783ee8791cc6b16c749ca5a9c6599966394e4b969655356352d58d4b4ad2743de0f43c8ea368e9394cd38ccb3c2d8b92d4b8ad2b2ae1b26c5b0ed8791cc789d2729e1725c570dd0f23c2f07cb41703cc89a24a8a61382e94459254551341dc0d8390d0b12c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6da49b6936db4db69b49349b6db6db4db6934db4924d34db49269b69a49b4d2692449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨71, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨90, by decide⟩, ⟨95, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "106000ec00868fa8f45c97800000", hexnat% "800000000000000000000000000", hexnat% "40000000000000020000000", hexnat% "400800000000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c6080ec00868ca8f44497800000", 72057628397666304, hexnat% "40000000000000020000000", 144115256795332608]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6000ec008685a8f44c97800000", hexnat% "400000000000200000000000000", hexnat% "1800000000000800000000000000", 69256347648, hexnat% "840000000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨101, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "182084ec00808fa8d454b7800000", hexnat% "60000000000000000", hexnat% "440000000000000000000000000", 35218731827200]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "182004ec00808fa0d41487800000", hexnat% "440800000000000000000000000", hexnat% "20000000030000000", 2287293423419392, hexnat% "40000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "180000ec00808ca0540487800000", 144255994283687936, hexnat% "60000000010000000", hexnat% "460800000000000000000000000", 74344612583440384, hexnat% "40000000000004020000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "460840c008487a8f458b5800000", hexnat% "20000000400000000", hexnat% "e000000000000000000000", hexnat% "1800000000000800000000000000", 33554432]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "460048c008487a8f448b5800000", hexnat% "20000000400000000", hexnat% "800000000000001000000000", hexnat% "800002000000000000000000000", hexnat% "1000004000000800000002000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "182084ec00840c287448b7800000", 85899345920, 252342316621103104, hexnat% "28000000000000000", hexnat% "440000000000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "84cc008403a8f45cb7800000", hexnat% "800002000000000000000000000", hexnat% "28c00000000000000", hexnat% "460000000000000000000000000", hexnat% "1000000000000000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "44c00860028345c35800000", hexnat% "800002000000000000000000000", 252412685365280768, hexnat% "460808000000000000000000000", 9511602415153971200, hexnat% "1000000000000800000002000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c16 c13
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c17 c12
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c18 c11
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "180080ac00028fa8f45c87800000", hexnat% "20004000000000000000000000", hexnat% "440000000000000000000000000", hexnat% "40000000000000030000000", hexnat% "840000000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1820006c00868ca8545cb7800000", hexnat% "840000000000000000000000", 216313519602139136, hexnat% "440008000000000000000000000", 35184372088832]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "184000ec00828fa0f45087800000", 17985175552, hexnat% "40008000800000000", hexnat% "420800000000000000000000000", hexnat% "40000000000000000000000"]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1840000c00868da8b44c97800000", hexnat% "40000000000000020000000", hexnat% "e000000000000000000000", 144185625539510272, hexnat% "420800000000000000000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1800808c00028fa0f45ca7800000", hexnat% "6000000000000000000000", hexnat% "460000000000000000000000000", hexnat% "840008000010000000", hexnat% "40000000000000000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1800000c00028ca0a45cb7800000", hexnat% "e000000000000000000000", 216260743044005888, hexnat% "840008000000000000", hexnat% "840000000000000000000000", hexnat% "460000000000000000000000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c26 c23
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c27 c23
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c28 c22
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c29 c21
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c30 c20
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "180084ac00028e08f454b7800000", 72057628397666304, hexnat% "840000000000000000", hexnat% "20004000000000000000000000", hexnat% "4400000000000a0000000000000"]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80a000000708f45c27800000", hexnat% "4600000000000a0000000000000", hexnat% "800000c00000000000000000000", hexnat% "44000000000000080000000", hexnat% "860000000010000000", hexnat% "1000000000008800000000000000"]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c33 c32
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c6080ec00868ca0e44037800000", 88046829568, 216190374299828224, 2251834173423616, hexnat% "40000000000000000000000"]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c60844c00868fa8e440b7800000", hexnat% "a000000000000000000000", 85899345920, 17626545782784]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c60044000068fa0f448b7800000", hexnat% "800008000000000000", hexnat% "808000000000001000000000", 17179869184, hexnat% "2c00000000000000000000"]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c37 c36
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c60804000068ea0e45cb7800000", hexnat% "800008000000000000", hexnat% "a400000000000000000000", 72075186223972352, hexnat% "40800000000000000000000"]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c60046c00868fa8f45037800000", hexnat% "808000000000000000000000", 19327352832, 34359738368]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c60004800868fa8f45037800000", hexnat% "a400000000000000000000", 19327352832, 34359738368, hexnat% "840000000000000000000000"]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c41 c40
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "186004ec00868fa8604837800000", 88046829568, 162727720910848, hexnat% "400800000000000000000000000"]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "186080c000868ea8e054b7800000", hexnat% "400000000000000040000000000", hexnat% "2c00000000000000000000", hexnat% "40000000000000000000000", 72075220583710720]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c6000c000868ea8f450b7800000", hexnat% "840000000000000000000000", 51539607552, 72057594037927936, hexnat% "2c00000000000000000000"]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1860004000868ea8e45037800000", hexnat% "400808000000000000000000000", 19327352832, hexnat% "2c00000000000000000000", 72075220583710720, hexnat% "40000000000000000000000"]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c46 c45
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c47 c44
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c48 c43
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c49 c42
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c50 c39
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c51 c38
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨102, by decide⟩ c52 c35
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "146080c000000fa0d45007000000", hexnat% "400000080000000a0000000", hexnat% "800002c00000000000000800000", hexnat% "40008000810000000", hexnat% "800000200000000000", hexnat% "20000000400000000"]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "460840c00848fa8f458b7800000", hexnat% "20000000400000000", hexnat% "e000000000000000000000", hexnat% "1800000000000000000000000000"]
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c6084ec00840d28645835800000", hexnat% "20000000400000000", 144273517750255616, 2181038080, 9259400833873739776]
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "460048c00848fa8f448b7800000", hexnat% "20000000400000000", hexnat% "800000000000001000000000", hexnat% "800002000000000000000000000", hexnat% "1000004000000000000000000000"]
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c6084ec00840fa86448b7800000", 158329674399744, hexnat% "28000000000000000", 85899345920]
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "146084ec00840fa8f448b7800000", hexnat% "800000000000000000000000000", 85899345920, hexnat% "28000000000000000"]
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c2084ec00840da87048b7800000", hexnat% "20000000400000000", 9223376434901286912, hexnat% "40000000000000800000000000", 144115256795332608]
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c60 c59
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨106, by decide⟩ c61 c58
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4cc00860da8604c35800000", hexnat% "800002000000000000000000000", 144277915796766720, hexnat% "1000000000008000000000000000", hexnat% "460800000000000000000000000", 70900514816]
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c63 c62
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c64 c57
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c65 c56
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c66 c55
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "460808000800fa8f44005000000", hexnat% "40000000810000000", 88617254912, hexnat% "28000000000000000", hexnat% "800002c00000000000000800000", hexnat% "1000044000000000000000000000"]
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "146080c000000ea8c45007000000", hexnat% "400000080000000a0000000", hexnat% "860000000010000000", hexnat% "800002c00000000000000800000", 72110404955799552, 17179869184]
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "460808000000ea8c454a7000000", 72110404955799552, hexnat% "860000000010000000", hexnat% "6400000000000000000000", hexnat% "1000040000008000000000000000", hexnat% "800000800000000000000800000"]
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "186084ec00000c08405087800000", hexnat% "860000000010000000", hexnat% "4000000000002a0040000000000", 9223372037391646720, 35235911696384, 72215923712327680]
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1860846c00008c084050b5800000", hexnat% "860000000000000000", hexnat% "400008000000000040000000000", 51573161984, 189291921837916160, 72110370596061184]
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1060046000860c08505cb7800000", hexnat% "800000c00000000000000000000", 72233515898372096, hexnat% "400808000000000000000000000", 9268412431174991872, 144115188075855872]
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "146084c000028ca84450a7000000", hexnat% "840000000010000000", 35235911696384, 216331111788183552, hexnat% "800002c00000000000000800000"]
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1860044400008c08405007000000", hexnat% "860000000010000000", hexnat% "400808000000000000000000000", hexnat% "2800000000000000800000", 19864223744, 72110404955799552, 189296319884427264]
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c75 c74
  let c77 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c76 c73
  let c78 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c77 c72
  let c79 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c78 c71
  let c80 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c79 c70
  let c81 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨101, by decide⟩ c80 c69
  let c82 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨102, by decide⟩ c81 c68
  let c83 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c82 c67
  let c84 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c83 c54
  let c85 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c84 c53
  let c86 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c85 c34
  let c87 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c86 c31
  let c88 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c87 c19
  let c89 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c88 c10
  c89
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00055.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00055.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001
def vertexColumn : Fields := ⟨10, hexnat% "1ac2f3a2e4ab2d2b2a6aa6ac699a96a3a2e9a699a5635a362d98e4b8ae1b89e0fba1e46b1d27296a669c6599966392e5a599655356352d58d4b4ad1b49d0f783d0f23a8da398f13a4d9394cd38ccb3c2d8b92d4b8ad2b2ac6b86d1b26c5b0ed8791cc789d2729c6785c9715c3743c8f13c2f07c5cc89a29492a168a6258561382e07b21686514a459294951544d0b41d"⟩
def kindColumn : Fields := ⟨3, hexnat% "da6da4db4da6934d24926da4db4da6934d249369a6db4db6db69b6da6db6d36936d2449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨33, by decide⟩, ⟨40, by decide⟩, ⟨46, by decide⟩, ⟨55, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨95, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨100, by decide⟩, ⟨103, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨112, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11896b41896945080410263800000", hexnat% "10000200000000000000000", hexnat% "a0000000000000000000000", hexnat% "a0000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11890be0812be5080410263800000", hexnat% "11000000000000000000000", hexnat% "6000000000000000000000000", hexnat% "84000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11890bc08109e5080410263800000", hexnat% "11000200000000000000000", hexnat% "2020000000000000000000000", hexnat% "4000004000000000000000000", hexnat% "82000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨103, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8169e0810be5080410263800000", hexnat% "86000000000000000000", hexnat% "10000010000000000000000000000", hexnat% "1000200000000000000000000000", hexnat% "80001000000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "810bf1810ba5080410263800000", hexnat% "11000000000000000000000000000", hexnat% "6040000000000000000", hexnat% "86000000000000000000000000", hexnat% "80000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1896941096b45080410263800000", hexnat% "10800000000000000000000", hexnat% "10000200000000000000000000000", hexnat% "80000080000000000000000", hexnat% "20000020000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "896940816be5080410263800000", hexnat% "1000001080000000000000000000", hexnat% "10000010000000000000000000000", hexnat% "2a0000000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1890951896b45080410263800000", hexnat% "6000000000000000000000000", hexnat% "a0000000000000000", hexnat% "10000200000000000000000000000", hexnat% "a0000000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "890940090be5080410263800000", hexnat% "4000004000000000000000000", hexnat% "11800000000000000000000", hexnat% "2000002000000000000000000", hexnat% "2a0000000000000000000000", hexnat% "11000000000000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨103, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨107, by decide⟩ c15 c4
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8069e0802960000000260800000", hexnat% "80000000003000000", hexnat% "84000080010000000000", hexnat% "1080001000000000000000000000", hexnat% "10200010200000000000000000", hexnat% "10000010000005000400000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11810351816be5080410263800000", hexnat% "80000080000000000000000000", hexnat% "a0000000000000000000000", hexnat% "2800000000000000000000000", hexnat% "4000000000000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11810351816be5080410263800000", hexnat% "80000080000000000000000000", hexnat% "a0000000000000000000000", hexnat% "6000000000000000000000000", hexnat% "800000000000000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "118801518869e5080410263800000", hexnat% "2a0000000000000000000000", hexnat% "6000000000000000000000000", hexnat% "10000010200000000000000000", hexnat% "800000000000000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "118103f1816be5000400261800000", hexnat% "2800000000000000000000000", 36029896564146176, hexnat% "80000080000000000000000000", hexnat% "4000000000000000000000000"]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8003e08069e5000400263800000", hexnat% "2800000000000000000000000", hexnat% "10000010000000000000000000000", hexnat% "10000010200000000000000000", hexnat% "84000000000080010000000000", hexnat% "1000001080000000000000000000"]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c23 c20
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c24 c19
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c25 c18
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11816b40806945080410263800000", hexnat% "a0000000000000000000000", hexnat% "2a0000000000000000", hexnat% "11010000000000000000000", hexnat% "80000080000000000000000000"]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11816b40016a45080410263800000", hexnat% "11800000000000000000000", hexnat% "a0000000000000000000000", hexnat% "1a0000000000000000", hexnat% "80000080000000000000000000"]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "816840006845080410263800000", hexnat% "10000010000000000000000000000", hexnat% "3a0000000000000000", hexnat% "1080001080000000000000000000", hexnat% "3a0000000000000000000000", hexnat% "810000000000000000000"]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c29 c28
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨107, by decide⟩ c30 c27
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "118963e10962e5080410263800000", hexnat% "10800000000000000000000", hexnat% "800000800000000000000000", hexnat% "100000000000000000"]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "118903e0010be5080410263800000", hexnat% "11800000000000000000000", hexnat% "2800000000000000000000000", hexnat% "4000004000000000000000000", hexnat% "82000000000000000000"]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨103, by decide⟩ c33 c32
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "118103e00103e0000400243000000", hexnat% "800000800000000000000000", hexnat% "11800005000000000000000", hexnat% "4000004000080010020000000", hexnat% "2000002000000000000800000", hexnat% "80000080000000000000000000"]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c35 c34
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11810351810345000400240000000", hexnat% "820000820000000000000000", hexnat% "80000080000000003800000", hexnat% "4000004000080010020000000", hexnat% "82000000000000000000", hexnat% "82000000000000000000000000"]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "118002d18002c5080410263800000", hexnat% "86000000000000000000", hexnat% "10000010000000000000000000", hexnat% "86000000000000000000000000", hexnat% "100000100000000000000000", hexnat% "820000820000000000000000"]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11890351890be5000400241000000", hexnat% "2820000000000000000000000", hexnat% "80000000000000002800000", hexnat% "6000000000020000000", hexnat% "4000000000080010000000000"]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11890251890345000400240000000", hexnat% "920000000000000000000000", hexnat% "2820000000000000000", hexnat% "4000004000080010020000000", hexnat% "80000080000000003800000", hexnat% "2000000000000000000000000"]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c40 c39
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1886340896be5080410263800000", hexnat% "11000000000000000000000", hexnat% "a0000000000000000000000", hexnat% "10010000000000000000000000000", hexnat% "800000000000000000000000"]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1886b60896be0080410261800000", hexnat% "80000000000000002000000", hexnat% "10010000000001000000000000000", hexnat% "11000004000000000000000"]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1812b40810be0080410241000000", hexnat% "a0000000000000002800000", hexnat% "4000004000000000020000000", hexnat% "82000000000000000000", hexnat% "10000010000005000000000000000", hexnat% "80001000000000000000000000"]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨97, by decide⟩ c44 c43
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c45 c42
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c46 c42
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "118002d18001c5080410263800000", hexnat% "86000000000000000000", hexnat% "10000010200000000000000000", hexnat% "86000000000000000000000000", hexnat% "920000000000000000000000", hexnat% "820000000000000000"]
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000be0802be4000400243800000", hexnat% "86000000000000000020000000", hexnat% "11010001000000000000000", hexnat% "10810000000000000000000000000", hexnat% "84000080010000000000"]
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1002ae08029e5080410263800000", hexnat% "4000004000000000000000000", hexnat% "80001080000000000000000000", hexnat% "810100000000000000000000000", hexnat% "10000010000000000000000000000", hexnat% "10200000000000000000"]
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1086be1886964080410263800000", hexnat% "280000000000000000", hexnat% "10810000000001000000000000000", hexnat% "10010000000000000000000"]
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1086261886164080410260800000", hexnat% "800000800000000000000000", hexnat% "80000080000000003000000", hexnat% "10000010000001000000000000000", hexnat% "810100000000000000000000000", hexnat% "10200000000000000000"]
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c52 c51
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10002c08801e4000400243800000", hexnat% "2800000000000000000", hexnat% "10810000000001000000000000000", hexnat% "4000004000080010020000000", hexnat% "11010200000000000000000", hexnat% "920000000000000000000000", hexnat% "82000000000000000000000000"]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c54 c53
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c55 c50
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c56 c49
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c57 c48
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c58 c47
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨108, by decide⟩ c59 c41
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c60 c38
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c61 c37
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c62 c36
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c63 c31
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c64 c26
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c65 c17
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c66 c16
  c67
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00055.record001
