import cubical_indecomposability.face_data
import cubical_indecomposability.cube_data
import cubical_indecomposability.face_data_checks.cube_complete
import cubical_indecomposability.face_data_checks.lower_facets
import cubical_indecomposability.face_data_checks.supports
import cubical_indecomposability.face_data_checks.injective
import cubical_indecomposability.face_data_checks.pairing
import cubical.cube_face_code
import Lean.Elab.Tactic.Omega

/-!
# Kernel checks for the complete finite face catalogue

The numerical checks use small, genuine finite domains. An elementary interval
coverage proof accounts for every original index. Cube order is proved once
from the ordinary coordinate-face order and transported along the injective
cube-vertex labellings. No native-decision axiom is used.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CubicalIndecomposability

private def finiteCheckIndex {n lo width : ℕ} (h : lo + width ≤ n)
    (j : Fin width) : Fin n :=
  ⟨lo + j.val, by have := j.isLt; omega⟩

private theorem finiteCheck_cover {n lo width : ℕ} {P : Fin n → Prop}
    (h : lo + width ≤ n)
    (hcheck : ∀ j : Fin width, P (finiteCheckIndex h j))
    (i : Fin n) (hlo : lo ≤ i.val) (hhi : i.val < lo + width) : P i := by
  let j : Fin width := ⟨i.val - lo, by omega⟩
  have he : finiteCheckIndex h j = i := by
    apply Fin.ext
    dsimp [finiteCheckIndex, j]
    omega
  simpa only [he] using hcheck j

private def BasicFaceChecks (i : Fin 1069) : Prop :=
  (faceMask i).Nonempty ∧
  faceFlag i (faceRank i) = i ∧
  (∀ k : Fin 4, faceMask (faceFlag i k.castSucc) ⊂ faceMask (faceFlag i k.succ)) ∧
  (∀ k : Fin 5, faceRank (faceFlag i k) = k) ∧
  (1 ≤ (faceRank i).val → (lowerFacets i).Nonempty) ∧
  (faceRank i = 0 → ∃ v : Fin 144, v.castLE (by decide) = i) ∧
  (faceRank i = 3 → ∃ f : Fin 130, codeFace f 0 = i) ∧
  (faceRank i = 4 ↔ i = 1068)

private instance (i : Fin 1069) : Decidable (BasicFaceChecks i) := by
  unfold BasicFaceChecks
  infer_instance

private theorem basicFaceChecks_part0000 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 0) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0001 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 4) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0002 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 8) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0003 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 12) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0004 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 16) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0005 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 20) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0006 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 24) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0007 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 28) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0008 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 32) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0009 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 36) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0010 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 40) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0011 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 44) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0012 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 48) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0013 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 52) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0014 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 56) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0015 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 60) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0016 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 64) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0017 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 68) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0018 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 72) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0019 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 76) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0020 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 80) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0021 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 84) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0022 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 88) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0023 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 92) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0024 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 96) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0025 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 100) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0026 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 104) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0027 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 108) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0028 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 112) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0029 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 116) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0030 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 120) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0031 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 124) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0032 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 128) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0033 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 132) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0034 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 136) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0035 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 140) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0036 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 144) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0037 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 148) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0038 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 152) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0039 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 156) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0040 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 160) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0041 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 164) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0042 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 168) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0043 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 172) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0044 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 176) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0045 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 180) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0046 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 184) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0047 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 188) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0048 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 192) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0049 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 196) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0050 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 200) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0051 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 204) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0052 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 208) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0053 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 212) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0054 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 216) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0055 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 220) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0056 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 224) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0057 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 228) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0058 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 232) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0059 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 236) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0060 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 240) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0061 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 244) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0062 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 248) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0063 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 252) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0064 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 256) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0065 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 260) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0066 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 264) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0067 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 268) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0068 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 272) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0069 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 276) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0070 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 280) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0071 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 284) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0072 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 288) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0073 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 292) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0074 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 296) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0075 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 300) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0076 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 304) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0077 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 308) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0078 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 312) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0079 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 316) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0080 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 320) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0081 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 324) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0082 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 328) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0083 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 332) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0084 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 336) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0085 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 340) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0086 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 344) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0087 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 348) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0088 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 352) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0089 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 356) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0090 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 360) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0091 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 364) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0092 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 368) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0093 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 372) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0094 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 376) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0095 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 380) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0096 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 384) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0097 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 388) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0098 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 392) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0099 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 396) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0100 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 400) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0101 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 404) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0102 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 408) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0103 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 412) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0104 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 416) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0105 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 420) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0106 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 424) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0107 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 428) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0108 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 432) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0109 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 436) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0110 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 440) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0111 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 444) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0112 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 448) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0113 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 452) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0114 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 456) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0115 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 460) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0116 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 464) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0117 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 468) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0118 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 472) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0119 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 476) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0120 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 480) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0121 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 484) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0122 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 488) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0123 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 492) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0124 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 496) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0125 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 500) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0126 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 504) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0127 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 508) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0128 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 512) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0129 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 516) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0130 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 520) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0131 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 524) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0132 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 528) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0133 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 532) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0134 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 536) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0135 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 540) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0136 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 544) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0137 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 548) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0138 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 552) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0139 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 556) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0140 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 560) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0141 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 564) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0142 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 568) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0143 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 572) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0144 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 576) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0145 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 580) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0146 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 584) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0147 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 588) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0148 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 592) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0149 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 596) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0150 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 600) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0151 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 604) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0152 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 608) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0153 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 612) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0154 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 616) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0155 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 620) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0156 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 624) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0157 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 628) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0158 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 632) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0159 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 636) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0160 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 640) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0161 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 644) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0162 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 648) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0163 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 652) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0164 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 656) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0165 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 660) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0166 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 664) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0167 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 668) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0168 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 672) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0169 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 676) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0170 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 680) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0171 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 684) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0172 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 688) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0173 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 692) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0174 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 696) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0175 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 700) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0176 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 704) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0177 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 708) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0178 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 712) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0179 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 716) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0180 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 720) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0181 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 724) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0182 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 728) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0183 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 732) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0184 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 736) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0185 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 740) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0186 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 744) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0187 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 748) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0188 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 752) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0189 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 756) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0190 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 760) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0191 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 764) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0192 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 768) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0193 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 772) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0194 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 776) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0195 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 780) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0196 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 784) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0197 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 788) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0198 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 792) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0199 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 796) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0200 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 800) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0201 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 804) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0202 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 808) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0203 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 812) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0204 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 816) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0205 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 820) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0206 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 824) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0207 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 828) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0208 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 832) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0209 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 836) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0210 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 840) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0211 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 844) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0212 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 848) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0213 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 852) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0214 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 856) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0215 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 860) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0216 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 864) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0217 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 868) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0218 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 872) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0219 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 876) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0220 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 880) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0221 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 884) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0222 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 888) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0223 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 892) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0224 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 896) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0225 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 900) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0226 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 904) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0227 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 908) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0228 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 912) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0229 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 916) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0230 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 920) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0231 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 924) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0232 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 928) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0233 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 932) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0234 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 936) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0235 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 940) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0236 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 944) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0237 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 948) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0238 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 952) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0239 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 956) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0240 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 960) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0241 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 964) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0242 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 968) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0243 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 972) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0244 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 976) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0245 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 980) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0246 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 984) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0247 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 988) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0248 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 992) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0249 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 996) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0250 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 1000) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0251 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 1004) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0252 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 1008) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0253 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 1012) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0254 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 1016) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0255 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 1020) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0256 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 1024) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0257 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 1028) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0258 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 1032) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0259 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 1036) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0260 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 1040) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0261 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 1044) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0262 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 1048) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0263 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 1052) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0264 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 1056) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0265 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 1060) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0266 : ∀ j : Fin 4,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 1064) (width := 4) (by decide) j) := by decide +kernel

private theorem basicFaceChecks_part0267 : ∀ j : Fin 1,
    BasicFaceChecks (finiteCheckIndex (n := 1069) (lo := 1068) (width := 1) (by decide) j) := by decide +kernel

private theorem basicFaceChecks : ∀ i : Fin 1069, BasicFaceChecks i := by
  intro i
  have hi_bound := i.isLt
  by_cases h536 : i.val < 536
  ·
    by_cases h268 : i.val < 268
    ·
      by_cases h132 : i.val < 132
      ·
        by_cases h64 : i.val < 64
        ·
          by_cases h32 : i.val < 32
          ·
            by_cases h16 : i.val < 16
            ·
              by_cases h8 : i.val < 8
              ·
                by_cases h4 : i.val < 4
                ·
                  exact finiteCheck_cover (lo := 0) (width := 4)
                    (by decide) basicFaceChecks_part0000 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 4) (width := 4)
                    (by decide) basicFaceChecks_part0001 i (by omega) (by omega)
              ·
                by_cases h12 : i.val < 12
                ·
                  exact finiteCheck_cover (lo := 8) (width := 4)
                    (by decide) basicFaceChecks_part0002 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 12) (width := 4)
                    (by decide) basicFaceChecks_part0003 i (by omega) (by omega)
            ·
              by_cases h24 : i.val < 24
              ·
                by_cases h20 : i.val < 20
                ·
                  exact finiteCheck_cover (lo := 16) (width := 4)
                    (by decide) basicFaceChecks_part0004 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 20) (width := 4)
                    (by decide) basicFaceChecks_part0005 i (by omega) (by omega)
              ·
                by_cases h28 : i.val < 28
                ·
                  exact finiteCheck_cover (lo := 24) (width := 4)
                    (by decide) basicFaceChecks_part0006 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 28) (width := 4)
                    (by decide) basicFaceChecks_part0007 i (by omega) (by omega)
          ·
            by_cases h48 : i.val < 48
            ·
              by_cases h40 : i.val < 40
              ·
                by_cases h36 : i.val < 36
                ·
                  exact finiteCheck_cover (lo := 32) (width := 4)
                    (by decide) basicFaceChecks_part0008 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 36) (width := 4)
                    (by decide) basicFaceChecks_part0009 i (by omega) (by omega)
              ·
                by_cases h44 : i.val < 44
                ·
                  exact finiteCheck_cover (lo := 40) (width := 4)
                    (by decide) basicFaceChecks_part0010 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 44) (width := 4)
                    (by decide) basicFaceChecks_part0011 i (by omega) (by omega)
            ·
              by_cases h56 : i.val < 56
              ·
                by_cases h52 : i.val < 52
                ·
                  exact finiteCheck_cover (lo := 48) (width := 4)
                    (by decide) basicFaceChecks_part0012 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 52) (width := 4)
                    (by decide) basicFaceChecks_part0013 i (by omega) (by omega)
              ·
                by_cases h60 : i.val < 60
                ·
                  exact finiteCheck_cover (lo := 56) (width := 4)
                    (by decide) basicFaceChecks_part0014 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 60) (width := 4)
                    (by decide) basicFaceChecks_part0015 i (by omega) (by omega)
        ·
          by_cases h96 : i.val < 96
          ·
            by_cases h80 : i.val < 80
            ·
              by_cases h72 : i.val < 72
              ·
                by_cases h68 : i.val < 68
                ·
                  exact finiteCheck_cover (lo := 64) (width := 4)
                    (by decide) basicFaceChecks_part0016 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 68) (width := 4)
                    (by decide) basicFaceChecks_part0017 i (by omega) (by omega)
              ·
                by_cases h76 : i.val < 76
                ·
                  exact finiteCheck_cover (lo := 72) (width := 4)
                    (by decide) basicFaceChecks_part0018 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 76) (width := 4)
                    (by decide) basicFaceChecks_part0019 i (by omega) (by omega)
            ·
              by_cases h88 : i.val < 88
              ·
                by_cases h84 : i.val < 84
                ·
                  exact finiteCheck_cover (lo := 80) (width := 4)
                    (by decide) basicFaceChecks_part0020 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 84) (width := 4)
                    (by decide) basicFaceChecks_part0021 i (by omega) (by omega)
              ·
                by_cases h92 : i.val < 92
                ·
                  exact finiteCheck_cover (lo := 88) (width := 4)
                    (by decide) basicFaceChecks_part0022 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 92) (width := 4)
                    (by decide) basicFaceChecks_part0023 i (by omega) (by omega)
          ·
            by_cases h112 : i.val < 112
            ·
              by_cases h104 : i.val < 104
              ·
                by_cases h100 : i.val < 100
                ·
                  exact finiteCheck_cover (lo := 96) (width := 4)
                    (by decide) basicFaceChecks_part0024 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 100) (width := 4)
                    (by decide) basicFaceChecks_part0025 i (by omega) (by omega)
              ·
                by_cases h108 : i.val < 108
                ·
                  exact finiteCheck_cover (lo := 104) (width := 4)
                    (by decide) basicFaceChecks_part0026 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 108) (width := 4)
                    (by decide) basicFaceChecks_part0027 i (by omega) (by omega)
            ·
              by_cases h120 : i.val < 120
              ·
                by_cases h116 : i.val < 116
                ·
                  exact finiteCheck_cover (lo := 112) (width := 4)
                    (by decide) basicFaceChecks_part0028 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 116) (width := 4)
                    (by decide) basicFaceChecks_part0029 i (by omega) (by omega)
              ·
                by_cases h124 : i.val < 124
                ·
                  exact finiteCheck_cover (lo := 120) (width := 4)
                    (by decide) basicFaceChecks_part0030 i (by omega) (by omega)
                ·
                  by_cases h128 : i.val < 128
                  ·
                    exact finiteCheck_cover (lo := 124) (width := 4)
                      (by decide) basicFaceChecks_part0031 i (by omega) (by omega)
                  ·
                    exact finiteCheck_cover (lo := 128) (width := 4)
                      (by decide) basicFaceChecks_part0032 i (by omega) (by omega)
      ·
        by_cases h200 : i.val < 200
        ·
          by_cases h164 : i.val < 164
          ·
            by_cases h148 : i.val < 148
            ·
              by_cases h140 : i.val < 140
              ·
                by_cases h136 : i.val < 136
                ·
                  exact finiteCheck_cover (lo := 132) (width := 4)
                    (by decide) basicFaceChecks_part0033 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 136) (width := 4)
                    (by decide) basicFaceChecks_part0034 i (by omega) (by omega)
              ·
                by_cases h144 : i.val < 144
                ·
                  exact finiteCheck_cover (lo := 140) (width := 4)
                    (by decide) basicFaceChecks_part0035 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 144) (width := 4)
                    (by decide) basicFaceChecks_part0036 i (by omega) (by omega)
            ·
              by_cases h156 : i.val < 156
              ·
                by_cases h152 : i.val < 152
                ·
                  exact finiteCheck_cover (lo := 148) (width := 4)
                    (by decide) basicFaceChecks_part0037 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 152) (width := 4)
                    (by decide) basicFaceChecks_part0038 i (by omega) (by omega)
              ·
                by_cases h160 : i.val < 160
                ·
                  exact finiteCheck_cover (lo := 156) (width := 4)
                    (by decide) basicFaceChecks_part0039 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 160) (width := 4)
                    (by decide) basicFaceChecks_part0040 i (by omega) (by omega)
          ·
            by_cases h180 : i.val < 180
            ·
              by_cases h172 : i.val < 172
              ·
                by_cases h168 : i.val < 168
                ·
                  exact finiteCheck_cover (lo := 164) (width := 4)
                    (by decide) basicFaceChecks_part0041 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 168) (width := 4)
                    (by decide) basicFaceChecks_part0042 i (by omega) (by omega)
              ·
                by_cases h176 : i.val < 176
                ·
                  exact finiteCheck_cover (lo := 172) (width := 4)
                    (by decide) basicFaceChecks_part0043 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 176) (width := 4)
                    (by decide) basicFaceChecks_part0044 i (by omega) (by omega)
            ·
              by_cases h188 : i.val < 188
              ·
                by_cases h184 : i.val < 184
                ·
                  exact finiteCheck_cover (lo := 180) (width := 4)
                    (by decide) basicFaceChecks_part0045 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 184) (width := 4)
                    (by decide) basicFaceChecks_part0046 i (by omega) (by omega)
              ·
                by_cases h192 : i.val < 192
                ·
                  exact finiteCheck_cover (lo := 188) (width := 4)
                    (by decide) basicFaceChecks_part0047 i (by omega) (by omega)
                ·
                  by_cases h196 : i.val < 196
                  ·
                    exact finiteCheck_cover (lo := 192) (width := 4)
                      (by decide) basicFaceChecks_part0048 i (by omega) (by omega)
                  ·
                    exact finiteCheck_cover (lo := 196) (width := 4)
                      (by decide) basicFaceChecks_part0049 i (by omega) (by omega)
        ·
          by_cases h232 : i.val < 232
          ·
            by_cases h216 : i.val < 216
            ·
              by_cases h208 : i.val < 208
              ·
                by_cases h204 : i.val < 204
                ·
                  exact finiteCheck_cover (lo := 200) (width := 4)
                    (by decide) basicFaceChecks_part0050 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 204) (width := 4)
                    (by decide) basicFaceChecks_part0051 i (by omega) (by omega)
              ·
                by_cases h212 : i.val < 212
                ·
                  exact finiteCheck_cover (lo := 208) (width := 4)
                    (by decide) basicFaceChecks_part0052 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 212) (width := 4)
                    (by decide) basicFaceChecks_part0053 i (by omega) (by omega)
            ·
              by_cases h224 : i.val < 224
              ·
                by_cases h220 : i.val < 220
                ·
                  exact finiteCheck_cover (lo := 216) (width := 4)
                    (by decide) basicFaceChecks_part0054 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 220) (width := 4)
                    (by decide) basicFaceChecks_part0055 i (by omega) (by omega)
              ·
                by_cases h228 : i.val < 228
                ·
                  exact finiteCheck_cover (lo := 224) (width := 4)
                    (by decide) basicFaceChecks_part0056 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 228) (width := 4)
                    (by decide) basicFaceChecks_part0057 i (by omega) (by omega)
          ·
            by_cases h248 : i.val < 248
            ·
              by_cases h240 : i.val < 240
              ·
                by_cases h236 : i.val < 236
                ·
                  exact finiteCheck_cover (lo := 232) (width := 4)
                    (by decide) basicFaceChecks_part0058 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 236) (width := 4)
                    (by decide) basicFaceChecks_part0059 i (by omega) (by omega)
              ·
                by_cases h244 : i.val < 244
                ·
                  exact finiteCheck_cover (lo := 240) (width := 4)
                    (by decide) basicFaceChecks_part0060 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 244) (width := 4)
                    (by decide) basicFaceChecks_part0061 i (by omega) (by omega)
            ·
              by_cases h256 : i.val < 256
              ·
                by_cases h252 : i.val < 252
                ·
                  exact finiteCheck_cover (lo := 248) (width := 4)
                    (by decide) basicFaceChecks_part0062 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 252) (width := 4)
                    (by decide) basicFaceChecks_part0063 i (by omega) (by omega)
              ·
                by_cases h260 : i.val < 260
                ·
                  exact finiteCheck_cover (lo := 256) (width := 4)
                    (by decide) basicFaceChecks_part0064 i (by omega) (by omega)
                ·
                  by_cases h264 : i.val < 264
                  ·
                    exact finiteCheck_cover (lo := 260) (width := 4)
                      (by decide) basicFaceChecks_part0065 i (by omega) (by omega)
                  ·
                    exact finiteCheck_cover (lo := 264) (width := 4)
                      (by decide) basicFaceChecks_part0066 i (by omega) (by omega)
    ·
      by_cases h400 : i.val < 400
      ·
        by_cases h332 : i.val < 332
        ·
          by_cases h300 : i.val < 300
          ·
            by_cases h284 : i.val < 284
            ·
              by_cases h276 : i.val < 276
              ·
                by_cases h272 : i.val < 272
                ·
                  exact finiteCheck_cover (lo := 268) (width := 4)
                    (by decide) basicFaceChecks_part0067 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 272) (width := 4)
                    (by decide) basicFaceChecks_part0068 i (by omega) (by omega)
              ·
                by_cases h280 : i.val < 280
                ·
                  exact finiteCheck_cover (lo := 276) (width := 4)
                    (by decide) basicFaceChecks_part0069 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 280) (width := 4)
                    (by decide) basicFaceChecks_part0070 i (by omega) (by omega)
            ·
              by_cases h292 : i.val < 292
              ·
                by_cases h288 : i.val < 288
                ·
                  exact finiteCheck_cover (lo := 284) (width := 4)
                    (by decide) basicFaceChecks_part0071 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 288) (width := 4)
                    (by decide) basicFaceChecks_part0072 i (by omega) (by omega)
              ·
                by_cases h296 : i.val < 296
                ·
                  exact finiteCheck_cover (lo := 292) (width := 4)
                    (by decide) basicFaceChecks_part0073 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 296) (width := 4)
                    (by decide) basicFaceChecks_part0074 i (by omega) (by omega)
          ·
            by_cases h316 : i.val < 316
            ·
              by_cases h308 : i.val < 308
              ·
                by_cases h304 : i.val < 304
                ·
                  exact finiteCheck_cover (lo := 300) (width := 4)
                    (by decide) basicFaceChecks_part0075 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 304) (width := 4)
                    (by decide) basicFaceChecks_part0076 i (by omega) (by omega)
              ·
                by_cases h312 : i.val < 312
                ·
                  exact finiteCheck_cover (lo := 308) (width := 4)
                    (by decide) basicFaceChecks_part0077 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 312) (width := 4)
                    (by decide) basicFaceChecks_part0078 i (by omega) (by omega)
            ·
              by_cases h324 : i.val < 324
              ·
                by_cases h320 : i.val < 320
                ·
                  exact finiteCheck_cover (lo := 316) (width := 4)
                    (by decide) basicFaceChecks_part0079 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 320) (width := 4)
                    (by decide) basicFaceChecks_part0080 i (by omega) (by omega)
              ·
                by_cases h328 : i.val < 328
                ·
                  exact finiteCheck_cover (lo := 324) (width := 4)
                    (by decide) basicFaceChecks_part0081 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 328) (width := 4)
                    (by decide) basicFaceChecks_part0082 i (by omega) (by omega)
        ·
          by_cases h364 : i.val < 364
          ·
            by_cases h348 : i.val < 348
            ·
              by_cases h340 : i.val < 340
              ·
                by_cases h336 : i.val < 336
                ·
                  exact finiteCheck_cover (lo := 332) (width := 4)
                    (by decide) basicFaceChecks_part0083 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 336) (width := 4)
                    (by decide) basicFaceChecks_part0084 i (by omega) (by omega)
              ·
                by_cases h344 : i.val < 344
                ·
                  exact finiteCheck_cover (lo := 340) (width := 4)
                    (by decide) basicFaceChecks_part0085 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 344) (width := 4)
                    (by decide) basicFaceChecks_part0086 i (by omega) (by omega)
            ·
              by_cases h356 : i.val < 356
              ·
                by_cases h352 : i.val < 352
                ·
                  exact finiteCheck_cover (lo := 348) (width := 4)
                    (by decide) basicFaceChecks_part0087 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 352) (width := 4)
                    (by decide) basicFaceChecks_part0088 i (by omega) (by omega)
              ·
                by_cases h360 : i.val < 360
                ·
                  exact finiteCheck_cover (lo := 356) (width := 4)
                    (by decide) basicFaceChecks_part0089 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 360) (width := 4)
                    (by decide) basicFaceChecks_part0090 i (by omega) (by omega)
          ·
            by_cases h380 : i.val < 380
            ·
              by_cases h372 : i.val < 372
              ·
                by_cases h368 : i.val < 368
                ·
                  exact finiteCheck_cover (lo := 364) (width := 4)
                    (by decide) basicFaceChecks_part0091 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 368) (width := 4)
                    (by decide) basicFaceChecks_part0092 i (by omega) (by omega)
              ·
                by_cases h376 : i.val < 376
                ·
                  exact finiteCheck_cover (lo := 372) (width := 4)
                    (by decide) basicFaceChecks_part0093 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 376) (width := 4)
                    (by decide) basicFaceChecks_part0094 i (by omega) (by omega)
            ·
              by_cases h388 : i.val < 388
              ·
                by_cases h384 : i.val < 384
                ·
                  exact finiteCheck_cover (lo := 380) (width := 4)
                    (by decide) basicFaceChecks_part0095 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 384) (width := 4)
                    (by decide) basicFaceChecks_part0096 i (by omega) (by omega)
              ·
                by_cases h392 : i.val < 392
                ·
                  exact finiteCheck_cover (lo := 388) (width := 4)
                    (by decide) basicFaceChecks_part0097 i (by omega) (by omega)
                ·
                  by_cases h396 : i.val < 396
                  ·
                    exact finiteCheck_cover (lo := 392) (width := 4)
                      (by decide) basicFaceChecks_part0098 i (by omega) (by omega)
                  ·
                    exact finiteCheck_cover (lo := 396) (width := 4)
                      (by decide) basicFaceChecks_part0099 i (by omega) (by omega)
      ·
        by_cases h468 : i.val < 468
        ·
          by_cases h432 : i.val < 432
          ·
            by_cases h416 : i.val < 416
            ·
              by_cases h408 : i.val < 408
              ·
                by_cases h404 : i.val < 404
                ·
                  exact finiteCheck_cover (lo := 400) (width := 4)
                    (by decide) basicFaceChecks_part0100 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 404) (width := 4)
                    (by decide) basicFaceChecks_part0101 i (by omega) (by omega)
              ·
                by_cases h412 : i.val < 412
                ·
                  exact finiteCheck_cover (lo := 408) (width := 4)
                    (by decide) basicFaceChecks_part0102 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 412) (width := 4)
                    (by decide) basicFaceChecks_part0103 i (by omega) (by omega)
            ·
              by_cases h424 : i.val < 424
              ·
                by_cases h420 : i.val < 420
                ·
                  exact finiteCheck_cover (lo := 416) (width := 4)
                    (by decide) basicFaceChecks_part0104 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 420) (width := 4)
                    (by decide) basicFaceChecks_part0105 i (by omega) (by omega)
              ·
                by_cases h428 : i.val < 428
                ·
                  exact finiteCheck_cover (lo := 424) (width := 4)
                    (by decide) basicFaceChecks_part0106 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 428) (width := 4)
                    (by decide) basicFaceChecks_part0107 i (by omega) (by omega)
          ·
            by_cases h448 : i.val < 448
            ·
              by_cases h440 : i.val < 440
              ·
                by_cases h436 : i.val < 436
                ·
                  exact finiteCheck_cover (lo := 432) (width := 4)
                    (by decide) basicFaceChecks_part0108 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 436) (width := 4)
                    (by decide) basicFaceChecks_part0109 i (by omega) (by omega)
              ·
                by_cases h444 : i.val < 444
                ·
                  exact finiteCheck_cover (lo := 440) (width := 4)
                    (by decide) basicFaceChecks_part0110 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 444) (width := 4)
                    (by decide) basicFaceChecks_part0111 i (by omega) (by omega)
            ·
              by_cases h456 : i.val < 456
              ·
                by_cases h452 : i.val < 452
                ·
                  exact finiteCheck_cover (lo := 448) (width := 4)
                    (by decide) basicFaceChecks_part0112 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 452) (width := 4)
                    (by decide) basicFaceChecks_part0113 i (by omega) (by omega)
              ·
                by_cases h460 : i.val < 460
                ·
                  exact finiteCheck_cover (lo := 456) (width := 4)
                    (by decide) basicFaceChecks_part0114 i (by omega) (by omega)
                ·
                  by_cases h464 : i.val < 464
                  ·
                    exact finiteCheck_cover (lo := 460) (width := 4)
                      (by decide) basicFaceChecks_part0115 i (by omega) (by omega)
                  ·
                    exact finiteCheck_cover (lo := 464) (width := 4)
                      (by decide) basicFaceChecks_part0116 i (by omega) (by omega)
        ·
          by_cases h500 : i.val < 500
          ·
            by_cases h484 : i.val < 484
            ·
              by_cases h476 : i.val < 476
              ·
                by_cases h472 : i.val < 472
                ·
                  exact finiteCheck_cover (lo := 468) (width := 4)
                    (by decide) basicFaceChecks_part0117 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 472) (width := 4)
                    (by decide) basicFaceChecks_part0118 i (by omega) (by omega)
              ·
                by_cases h480 : i.val < 480
                ·
                  exact finiteCheck_cover (lo := 476) (width := 4)
                    (by decide) basicFaceChecks_part0119 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 480) (width := 4)
                    (by decide) basicFaceChecks_part0120 i (by omega) (by omega)
            ·
              by_cases h492 : i.val < 492
              ·
                by_cases h488 : i.val < 488
                ·
                  exact finiteCheck_cover (lo := 484) (width := 4)
                    (by decide) basicFaceChecks_part0121 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 488) (width := 4)
                    (by decide) basicFaceChecks_part0122 i (by omega) (by omega)
              ·
                by_cases h496 : i.val < 496
                ·
                  exact finiteCheck_cover (lo := 492) (width := 4)
                    (by decide) basicFaceChecks_part0123 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 496) (width := 4)
                    (by decide) basicFaceChecks_part0124 i (by omega) (by omega)
          ·
            by_cases h516 : i.val < 516
            ·
              by_cases h508 : i.val < 508
              ·
                by_cases h504 : i.val < 504
                ·
                  exact finiteCheck_cover (lo := 500) (width := 4)
                    (by decide) basicFaceChecks_part0125 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 504) (width := 4)
                    (by decide) basicFaceChecks_part0126 i (by omega) (by omega)
              ·
                by_cases h512 : i.val < 512
                ·
                  exact finiteCheck_cover (lo := 508) (width := 4)
                    (by decide) basicFaceChecks_part0127 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 512) (width := 4)
                    (by decide) basicFaceChecks_part0128 i (by omega) (by omega)
            ·
              by_cases h524 : i.val < 524
              ·
                by_cases h520 : i.val < 520
                ·
                  exact finiteCheck_cover (lo := 516) (width := 4)
                    (by decide) basicFaceChecks_part0129 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 520) (width := 4)
                    (by decide) basicFaceChecks_part0130 i (by omega) (by omega)
              ·
                by_cases h528 : i.val < 528
                ·
                  exact finiteCheck_cover (lo := 524) (width := 4)
                    (by decide) basicFaceChecks_part0131 i (by omega) (by omega)
                ·
                  by_cases h532 : i.val < 532
                  ·
                    exact finiteCheck_cover (lo := 528) (width := 4)
                      (by decide) basicFaceChecks_part0132 i (by omega) (by omega)
                  ·
                    exact finiteCheck_cover (lo := 532) (width := 4)
                      (by decide) basicFaceChecks_part0133 i (by omega) (by omega)
  ·
    by_cases h804 : i.val < 804
    ·
      by_cases h668 : i.val < 668
      ·
        by_cases h600 : i.val < 600
        ·
          by_cases h568 : i.val < 568
          ·
            by_cases h552 : i.val < 552
            ·
              by_cases h544 : i.val < 544
              ·
                by_cases h540 : i.val < 540
                ·
                  exact finiteCheck_cover (lo := 536) (width := 4)
                    (by decide) basicFaceChecks_part0134 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 540) (width := 4)
                    (by decide) basicFaceChecks_part0135 i (by omega) (by omega)
              ·
                by_cases h548 : i.val < 548
                ·
                  exact finiteCheck_cover (lo := 544) (width := 4)
                    (by decide) basicFaceChecks_part0136 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 548) (width := 4)
                    (by decide) basicFaceChecks_part0137 i (by omega) (by omega)
            ·
              by_cases h560 : i.val < 560
              ·
                by_cases h556 : i.val < 556
                ·
                  exact finiteCheck_cover (lo := 552) (width := 4)
                    (by decide) basicFaceChecks_part0138 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 556) (width := 4)
                    (by decide) basicFaceChecks_part0139 i (by omega) (by omega)
              ·
                by_cases h564 : i.val < 564
                ·
                  exact finiteCheck_cover (lo := 560) (width := 4)
                    (by decide) basicFaceChecks_part0140 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 564) (width := 4)
                    (by decide) basicFaceChecks_part0141 i (by omega) (by omega)
          ·
            by_cases h584 : i.val < 584
            ·
              by_cases h576 : i.val < 576
              ·
                by_cases h572 : i.val < 572
                ·
                  exact finiteCheck_cover (lo := 568) (width := 4)
                    (by decide) basicFaceChecks_part0142 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 572) (width := 4)
                    (by decide) basicFaceChecks_part0143 i (by omega) (by omega)
              ·
                by_cases h580 : i.val < 580
                ·
                  exact finiteCheck_cover (lo := 576) (width := 4)
                    (by decide) basicFaceChecks_part0144 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 580) (width := 4)
                    (by decide) basicFaceChecks_part0145 i (by omega) (by omega)
            ·
              by_cases h592 : i.val < 592
              ·
                by_cases h588 : i.val < 588
                ·
                  exact finiteCheck_cover (lo := 584) (width := 4)
                    (by decide) basicFaceChecks_part0146 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 588) (width := 4)
                    (by decide) basicFaceChecks_part0147 i (by omega) (by omega)
              ·
                by_cases h596 : i.val < 596
                ·
                  exact finiteCheck_cover (lo := 592) (width := 4)
                    (by decide) basicFaceChecks_part0148 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 596) (width := 4)
                    (by decide) basicFaceChecks_part0149 i (by omega) (by omega)
        ·
          by_cases h632 : i.val < 632
          ·
            by_cases h616 : i.val < 616
            ·
              by_cases h608 : i.val < 608
              ·
                by_cases h604 : i.val < 604
                ·
                  exact finiteCheck_cover (lo := 600) (width := 4)
                    (by decide) basicFaceChecks_part0150 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 604) (width := 4)
                    (by decide) basicFaceChecks_part0151 i (by omega) (by omega)
              ·
                by_cases h612 : i.val < 612
                ·
                  exact finiteCheck_cover (lo := 608) (width := 4)
                    (by decide) basicFaceChecks_part0152 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 612) (width := 4)
                    (by decide) basicFaceChecks_part0153 i (by omega) (by omega)
            ·
              by_cases h624 : i.val < 624
              ·
                by_cases h620 : i.val < 620
                ·
                  exact finiteCheck_cover (lo := 616) (width := 4)
                    (by decide) basicFaceChecks_part0154 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 620) (width := 4)
                    (by decide) basicFaceChecks_part0155 i (by omega) (by omega)
              ·
                by_cases h628 : i.val < 628
                ·
                  exact finiteCheck_cover (lo := 624) (width := 4)
                    (by decide) basicFaceChecks_part0156 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 628) (width := 4)
                    (by decide) basicFaceChecks_part0157 i (by omega) (by omega)
          ·
            by_cases h648 : i.val < 648
            ·
              by_cases h640 : i.val < 640
              ·
                by_cases h636 : i.val < 636
                ·
                  exact finiteCheck_cover (lo := 632) (width := 4)
                    (by decide) basicFaceChecks_part0158 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 636) (width := 4)
                    (by decide) basicFaceChecks_part0159 i (by omega) (by omega)
              ·
                by_cases h644 : i.val < 644
                ·
                  exact finiteCheck_cover (lo := 640) (width := 4)
                    (by decide) basicFaceChecks_part0160 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 644) (width := 4)
                    (by decide) basicFaceChecks_part0161 i (by omega) (by omega)
            ·
              by_cases h656 : i.val < 656
              ·
                by_cases h652 : i.val < 652
                ·
                  exact finiteCheck_cover (lo := 648) (width := 4)
                    (by decide) basicFaceChecks_part0162 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 652) (width := 4)
                    (by decide) basicFaceChecks_part0163 i (by omega) (by omega)
              ·
                by_cases h660 : i.val < 660
                ·
                  exact finiteCheck_cover (lo := 656) (width := 4)
                    (by decide) basicFaceChecks_part0164 i (by omega) (by omega)
                ·
                  by_cases h664 : i.val < 664
                  ·
                    exact finiteCheck_cover (lo := 660) (width := 4)
                      (by decide) basicFaceChecks_part0165 i (by omega) (by omega)
                  ·
                    exact finiteCheck_cover (lo := 664) (width := 4)
                      (by decide) basicFaceChecks_part0166 i (by omega) (by omega)
      ·
        by_cases h736 : i.val < 736
        ·
          by_cases h700 : i.val < 700
          ·
            by_cases h684 : i.val < 684
            ·
              by_cases h676 : i.val < 676
              ·
                by_cases h672 : i.val < 672
                ·
                  exact finiteCheck_cover (lo := 668) (width := 4)
                    (by decide) basicFaceChecks_part0167 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 672) (width := 4)
                    (by decide) basicFaceChecks_part0168 i (by omega) (by omega)
              ·
                by_cases h680 : i.val < 680
                ·
                  exact finiteCheck_cover (lo := 676) (width := 4)
                    (by decide) basicFaceChecks_part0169 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 680) (width := 4)
                    (by decide) basicFaceChecks_part0170 i (by omega) (by omega)
            ·
              by_cases h692 : i.val < 692
              ·
                by_cases h688 : i.val < 688
                ·
                  exact finiteCheck_cover (lo := 684) (width := 4)
                    (by decide) basicFaceChecks_part0171 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 688) (width := 4)
                    (by decide) basicFaceChecks_part0172 i (by omega) (by omega)
              ·
                by_cases h696 : i.val < 696
                ·
                  exact finiteCheck_cover (lo := 692) (width := 4)
                    (by decide) basicFaceChecks_part0173 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 696) (width := 4)
                    (by decide) basicFaceChecks_part0174 i (by omega) (by omega)
          ·
            by_cases h716 : i.val < 716
            ·
              by_cases h708 : i.val < 708
              ·
                by_cases h704 : i.val < 704
                ·
                  exact finiteCheck_cover (lo := 700) (width := 4)
                    (by decide) basicFaceChecks_part0175 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 704) (width := 4)
                    (by decide) basicFaceChecks_part0176 i (by omega) (by omega)
              ·
                by_cases h712 : i.val < 712
                ·
                  exact finiteCheck_cover (lo := 708) (width := 4)
                    (by decide) basicFaceChecks_part0177 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 712) (width := 4)
                    (by decide) basicFaceChecks_part0178 i (by omega) (by omega)
            ·
              by_cases h724 : i.val < 724
              ·
                by_cases h720 : i.val < 720
                ·
                  exact finiteCheck_cover (lo := 716) (width := 4)
                    (by decide) basicFaceChecks_part0179 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 720) (width := 4)
                    (by decide) basicFaceChecks_part0180 i (by omega) (by omega)
              ·
                by_cases h728 : i.val < 728
                ·
                  exact finiteCheck_cover (lo := 724) (width := 4)
                    (by decide) basicFaceChecks_part0181 i (by omega) (by omega)
                ·
                  by_cases h732 : i.val < 732
                  ·
                    exact finiteCheck_cover (lo := 728) (width := 4)
                      (by decide) basicFaceChecks_part0182 i (by omega) (by omega)
                  ·
                    exact finiteCheck_cover (lo := 732) (width := 4)
                      (by decide) basicFaceChecks_part0183 i (by omega) (by omega)
        ·
          by_cases h768 : i.val < 768
          ·
            by_cases h752 : i.val < 752
            ·
              by_cases h744 : i.val < 744
              ·
                by_cases h740 : i.val < 740
                ·
                  exact finiteCheck_cover (lo := 736) (width := 4)
                    (by decide) basicFaceChecks_part0184 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 740) (width := 4)
                    (by decide) basicFaceChecks_part0185 i (by omega) (by omega)
              ·
                by_cases h748 : i.val < 748
                ·
                  exact finiteCheck_cover (lo := 744) (width := 4)
                    (by decide) basicFaceChecks_part0186 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 748) (width := 4)
                    (by decide) basicFaceChecks_part0187 i (by omega) (by omega)
            ·
              by_cases h760 : i.val < 760
              ·
                by_cases h756 : i.val < 756
                ·
                  exact finiteCheck_cover (lo := 752) (width := 4)
                    (by decide) basicFaceChecks_part0188 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 756) (width := 4)
                    (by decide) basicFaceChecks_part0189 i (by omega) (by omega)
              ·
                by_cases h764 : i.val < 764
                ·
                  exact finiteCheck_cover (lo := 760) (width := 4)
                    (by decide) basicFaceChecks_part0190 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 764) (width := 4)
                    (by decide) basicFaceChecks_part0191 i (by omega) (by omega)
          ·
            by_cases h784 : i.val < 784
            ·
              by_cases h776 : i.val < 776
              ·
                by_cases h772 : i.val < 772
                ·
                  exact finiteCheck_cover (lo := 768) (width := 4)
                    (by decide) basicFaceChecks_part0192 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 772) (width := 4)
                    (by decide) basicFaceChecks_part0193 i (by omega) (by omega)
              ·
                by_cases h780 : i.val < 780
                ·
                  exact finiteCheck_cover (lo := 776) (width := 4)
                    (by decide) basicFaceChecks_part0194 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 780) (width := 4)
                    (by decide) basicFaceChecks_part0195 i (by omega) (by omega)
            ·
              by_cases h792 : i.val < 792
              ·
                by_cases h788 : i.val < 788
                ·
                  exact finiteCheck_cover (lo := 784) (width := 4)
                    (by decide) basicFaceChecks_part0196 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 788) (width := 4)
                    (by decide) basicFaceChecks_part0197 i (by omega) (by omega)
              ·
                by_cases h796 : i.val < 796
                ·
                  exact finiteCheck_cover (lo := 792) (width := 4)
                    (by decide) basicFaceChecks_part0198 i (by omega) (by omega)
                ·
                  by_cases h800 : i.val < 800
                  ·
                    exact finiteCheck_cover (lo := 796) (width := 4)
                      (by decide) basicFaceChecks_part0199 i (by omega) (by omega)
                  ·
                    exact finiteCheck_cover (lo := 800) (width := 4)
                      (by decide) basicFaceChecks_part0200 i (by omega) (by omega)
    ·
      by_cases h936 : i.val < 936
      ·
        by_cases h868 : i.val < 868
        ·
          by_cases h836 : i.val < 836
          ·
            by_cases h820 : i.val < 820
            ·
              by_cases h812 : i.val < 812
              ·
                by_cases h808 : i.val < 808
                ·
                  exact finiteCheck_cover (lo := 804) (width := 4)
                    (by decide) basicFaceChecks_part0201 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 808) (width := 4)
                    (by decide) basicFaceChecks_part0202 i (by omega) (by omega)
              ·
                by_cases h816 : i.val < 816
                ·
                  exact finiteCheck_cover (lo := 812) (width := 4)
                    (by decide) basicFaceChecks_part0203 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 816) (width := 4)
                    (by decide) basicFaceChecks_part0204 i (by omega) (by omega)
            ·
              by_cases h828 : i.val < 828
              ·
                by_cases h824 : i.val < 824
                ·
                  exact finiteCheck_cover (lo := 820) (width := 4)
                    (by decide) basicFaceChecks_part0205 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 824) (width := 4)
                    (by decide) basicFaceChecks_part0206 i (by omega) (by omega)
              ·
                by_cases h832 : i.val < 832
                ·
                  exact finiteCheck_cover (lo := 828) (width := 4)
                    (by decide) basicFaceChecks_part0207 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 832) (width := 4)
                    (by decide) basicFaceChecks_part0208 i (by omega) (by omega)
          ·
            by_cases h852 : i.val < 852
            ·
              by_cases h844 : i.val < 844
              ·
                by_cases h840 : i.val < 840
                ·
                  exact finiteCheck_cover (lo := 836) (width := 4)
                    (by decide) basicFaceChecks_part0209 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 840) (width := 4)
                    (by decide) basicFaceChecks_part0210 i (by omega) (by omega)
              ·
                by_cases h848 : i.val < 848
                ·
                  exact finiteCheck_cover (lo := 844) (width := 4)
                    (by decide) basicFaceChecks_part0211 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 848) (width := 4)
                    (by decide) basicFaceChecks_part0212 i (by omega) (by omega)
            ·
              by_cases h860 : i.val < 860
              ·
                by_cases h856 : i.val < 856
                ·
                  exact finiteCheck_cover (lo := 852) (width := 4)
                    (by decide) basicFaceChecks_part0213 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 856) (width := 4)
                    (by decide) basicFaceChecks_part0214 i (by omega) (by omega)
              ·
                by_cases h864 : i.val < 864
                ·
                  exact finiteCheck_cover (lo := 860) (width := 4)
                    (by decide) basicFaceChecks_part0215 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 864) (width := 4)
                    (by decide) basicFaceChecks_part0216 i (by omega) (by omega)
        ·
          by_cases h900 : i.val < 900
          ·
            by_cases h884 : i.val < 884
            ·
              by_cases h876 : i.val < 876
              ·
                by_cases h872 : i.val < 872
                ·
                  exact finiteCheck_cover (lo := 868) (width := 4)
                    (by decide) basicFaceChecks_part0217 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 872) (width := 4)
                    (by decide) basicFaceChecks_part0218 i (by omega) (by omega)
              ·
                by_cases h880 : i.val < 880
                ·
                  exact finiteCheck_cover (lo := 876) (width := 4)
                    (by decide) basicFaceChecks_part0219 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 880) (width := 4)
                    (by decide) basicFaceChecks_part0220 i (by omega) (by omega)
            ·
              by_cases h892 : i.val < 892
              ·
                by_cases h888 : i.val < 888
                ·
                  exact finiteCheck_cover (lo := 884) (width := 4)
                    (by decide) basicFaceChecks_part0221 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 888) (width := 4)
                    (by decide) basicFaceChecks_part0222 i (by omega) (by omega)
              ·
                by_cases h896 : i.val < 896
                ·
                  exact finiteCheck_cover (lo := 892) (width := 4)
                    (by decide) basicFaceChecks_part0223 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 896) (width := 4)
                    (by decide) basicFaceChecks_part0224 i (by omega) (by omega)
          ·
            by_cases h916 : i.val < 916
            ·
              by_cases h908 : i.val < 908
              ·
                by_cases h904 : i.val < 904
                ·
                  exact finiteCheck_cover (lo := 900) (width := 4)
                    (by decide) basicFaceChecks_part0225 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 904) (width := 4)
                    (by decide) basicFaceChecks_part0226 i (by omega) (by omega)
              ·
                by_cases h912 : i.val < 912
                ·
                  exact finiteCheck_cover (lo := 908) (width := 4)
                    (by decide) basicFaceChecks_part0227 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 912) (width := 4)
                    (by decide) basicFaceChecks_part0228 i (by omega) (by omega)
            ·
              by_cases h924 : i.val < 924
              ·
                by_cases h920 : i.val < 920
                ·
                  exact finiteCheck_cover (lo := 916) (width := 4)
                    (by decide) basicFaceChecks_part0229 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 920) (width := 4)
                    (by decide) basicFaceChecks_part0230 i (by omega) (by omega)
              ·
                by_cases h928 : i.val < 928
                ·
                  exact finiteCheck_cover (lo := 924) (width := 4)
                    (by decide) basicFaceChecks_part0231 i (by omega) (by omega)
                ·
                  by_cases h932 : i.val < 932
                  ·
                    exact finiteCheck_cover (lo := 928) (width := 4)
                      (by decide) basicFaceChecks_part0232 i (by omega) (by omega)
                  ·
                    exact finiteCheck_cover (lo := 932) (width := 4)
                      (by decide) basicFaceChecks_part0233 i (by omega) (by omega)
      ·
        by_cases h1004 : i.val < 1004
        ·
          by_cases h968 : i.val < 968
          ·
            by_cases h952 : i.val < 952
            ·
              by_cases h944 : i.val < 944
              ·
                by_cases h940 : i.val < 940
                ·
                  exact finiteCheck_cover (lo := 936) (width := 4)
                    (by decide) basicFaceChecks_part0234 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 940) (width := 4)
                    (by decide) basicFaceChecks_part0235 i (by omega) (by omega)
              ·
                by_cases h948 : i.val < 948
                ·
                  exact finiteCheck_cover (lo := 944) (width := 4)
                    (by decide) basicFaceChecks_part0236 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 948) (width := 4)
                    (by decide) basicFaceChecks_part0237 i (by omega) (by omega)
            ·
              by_cases h960 : i.val < 960
              ·
                by_cases h956 : i.val < 956
                ·
                  exact finiteCheck_cover (lo := 952) (width := 4)
                    (by decide) basicFaceChecks_part0238 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 956) (width := 4)
                    (by decide) basicFaceChecks_part0239 i (by omega) (by omega)
              ·
                by_cases h964 : i.val < 964
                ·
                  exact finiteCheck_cover (lo := 960) (width := 4)
                    (by decide) basicFaceChecks_part0240 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 964) (width := 4)
                    (by decide) basicFaceChecks_part0241 i (by omega) (by omega)
          ·
            by_cases h984 : i.val < 984
            ·
              by_cases h976 : i.val < 976
              ·
                by_cases h972 : i.val < 972
                ·
                  exact finiteCheck_cover (lo := 968) (width := 4)
                    (by decide) basicFaceChecks_part0242 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 972) (width := 4)
                    (by decide) basicFaceChecks_part0243 i (by omega) (by omega)
              ·
                by_cases h980 : i.val < 980
                ·
                  exact finiteCheck_cover (lo := 976) (width := 4)
                    (by decide) basicFaceChecks_part0244 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 980) (width := 4)
                    (by decide) basicFaceChecks_part0245 i (by omega) (by omega)
            ·
              by_cases h992 : i.val < 992
              ·
                by_cases h988 : i.val < 988
                ·
                  exact finiteCheck_cover (lo := 984) (width := 4)
                    (by decide) basicFaceChecks_part0246 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 988) (width := 4)
                    (by decide) basicFaceChecks_part0247 i (by omega) (by omega)
              ·
                by_cases h996 : i.val < 996
                ·
                  exact finiteCheck_cover (lo := 992) (width := 4)
                    (by decide) basicFaceChecks_part0248 i (by omega) (by omega)
                ·
                  by_cases h1000 : i.val < 1000
                  ·
                    exact finiteCheck_cover (lo := 996) (width := 4)
                      (by decide) basicFaceChecks_part0249 i (by omega) (by omega)
                  ·
                    exact finiteCheck_cover (lo := 1000) (width := 4)
                      (by decide) basicFaceChecks_part0250 i (by omega) (by omega)
        ·
          by_cases h1036 : i.val < 1036
          ·
            by_cases h1020 : i.val < 1020
            ·
              by_cases h1012 : i.val < 1012
              ·
                by_cases h1008 : i.val < 1008
                ·
                  exact finiteCheck_cover (lo := 1004) (width := 4)
                    (by decide) basicFaceChecks_part0251 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 1008) (width := 4)
                    (by decide) basicFaceChecks_part0252 i (by omega) (by omega)
              ·
                by_cases h1016 : i.val < 1016
                ·
                  exact finiteCheck_cover (lo := 1012) (width := 4)
                    (by decide) basicFaceChecks_part0253 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 1016) (width := 4)
                    (by decide) basicFaceChecks_part0254 i (by omega) (by omega)
            ·
              by_cases h1028 : i.val < 1028
              ·
                by_cases h1024 : i.val < 1024
                ·
                  exact finiteCheck_cover (lo := 1020) (width := 4)
                    (by decide) basicFaceChecks_part0255 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 1024) (width := 4)
                    (by decide) basicFaceChecks_part0256 i (by omega) (by omega)
              ·
                by_cases h1032 : i.val < 1032
                ·
                  exact finiteCheck_cover (lo := 1028) (width := 4)
                    (by decide) basicFaceChecks_part0257 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 1032) (width := 4)
                    (by decide) basicFaceChecks_part0258 i (by omega) (by omega)
          ·
            by_cases h1052 : i.val < 1052
            ·
              by_cases h1044 : i.val < 1044
              ·
                by_cases h1040 : i.val < 1040
                ·
                  exact finiteCheck_cover (lo := 1036) (width := 4)
                    (by decide) basicFaceChecks_part0259 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 1040) (width := 4)
                    (by decide) basicFaceChecks_part0260 i (by omega) (by omega)
              ·
                by_cases h1048 : i.val < 1048
                ·
                  exact finiteCheck_cover (lo := 1044) (width := 4)
                    (by decide) basicFaceChecks_part0261 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 1048) (width := 4)
                    (by decide) basicFaceChecks_part0262 i (by omega) (by omega)
            ·
              by_cases h1060 : i.val < 1060
              ·
                by_cases h1056 : i.val < 1056
                ·
                  exact finiteCheck_cover (lo := 1052) (width := 4)
                    (by decide) basicFaceChecks_part0263 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 1056) (width := 4)
                    (by decide) basicFaceChecks_part0264 i (by omega) (by omega)
              ·
                by_cases h1064 : i.val < 1064
                ·
                  exact finiteCheck_cover (lo := 1060) (width := 4)
                    (by decide) basicFaceChecks_part0265 i (by omega) (by omega)
                ·
                  by_cases h1068 : i.val < 1068
                  ·
                    exact finiteCheck_cover (lo := 1064) (width := 4)
                      (by decide) basicFaceChecks_part0266 i (by omega) (by omega)
                  ·
                    exact finiteCheck_cover (lo := 1068) (width := 1)
                      (by decide) basicFaceChecks_part0267 i (by omega) (by omega)

theorem faceMask_nonempty : ∀ i : Fin 1069, (faceMask i).Nonempty :=
  fun i => (basicFaceChecks i).1

theorem faceMask_top : faceMask 1068 = Finset.univ := rfl

private theorem faceMask_vertex_part0000 : ∀ j : Fin 8,
    faceMask ((finiteCheckIndex (n := 144) (lo := 0) (width := 8) (by decide) j).castLE (by decide)) = {(finiteCheckIndex (n := 144) (lo := 0) (width := 8) (by decide) j)} := by decide +kernel

private theorem faceMask_vertex_part0001 : ∀ j : Fin 8,
    faceMask ((finiteCheckIndex (n := 144) (lo := 8) (width := 8) (by decide) j).castLE (by decide)) = {(finiteCheckIndex (n := 144) (lo := 8) (width := 8) (by decide) j)} := by decide +kernel

private theorem faceMask_vertex_part0002 : ∀ j : Fin 8,
    faceMask ((finiteCheckIndex (n := 144) (lo := 16) (width := 8) (by decide) j).castLE (by decide)) = {(finiteCheckIndex (n := 144) (lo := 16) (width := 8) (by decide) j)} := by decide +kernel

private theorem faceMask_vertex_part0003 : ∀ j : Fin 8,
    faceMask ((finiteCheckIndex (n := 144) (lo := 24) (width := 8) (by decide) j).castLE (by decide)) = {(finiteCheckIndex (n := 144) (lo := 24) (width := 8) (by decide) j)} := by decide +kernel

private theorem faceMask_vertex_part0004 : ∀ j : Fin 8,
    faceMask ((finiteCheckIndex (n := 144) (lo := 32) (width := 8) (by decide) j).castLE (by decide)) = {(finiteCheckIndex (n := 144) (lo := 32) (width := 8) (by decide) j)} := by decide +kernel

private theorem faceMask_vertex_part0005 : ∀ j : Fin 8,
    faceMask ((finiteCheckIndex (n := 144) (lo := 40) (width := 8) (by decide) j).castLE (by decide)) = {(finiteCheckIndex (n := 144) (lo := 40) (width := 8) (by decide) j)} := by decide +kernel

private theorem faceMask_vertex_part0006 : ∀ j : Fin 8,
    faceMask ((finiteCheckIndex (n := 144) (lo := 48) (width := 8) (by decide) j).castLE (by decide)) = {(finiteCheckIndex (n := 144) (lo := 48) (width := 8) (by decide) j)} := by decide +kernel

private theorem faceMask_vertex_part0007 : ∀ j : Fin 8,
    faceMask ((finiteCheckIndex (n := 144) (lo := 56) (width := 8) (by decide) j).castLE (by decide)) = {(finiteCheckIndex (n := 144) (lo := 56) (width := 8) (by decide) j)} := by decide +kernel

private theorem faceMask_vertex_part0008 : ∀ j : Fin 8,
    faceMask ((finiteCheckIndex (n := 144) (lo := 64) (width := 8) (by decide) j).castLE (by decide)) = {(finiteCheckIndex (n := 144) (lo := 64) (width := 8) (by decide) j)} := by decide +kernel

private theorem faceMask_vertex_part0009 : ∀ j : Fin 8,
    faceMask ((finiteCheckIndex (n := 144) (lo := 72) (width := 8) (by decide) j).castLE (by decide)) = {(finiteCheckIndex (n := 144) (lo := 72) (width := 8) (by decide) j)} := by decide +kernel

private theorem faceMask_vertex_part0010 : ∀ j : Fin 8,
    faceMask ((finiteCheckIndex (n := 144) (lo := 80) (width := 8) (by decide) j).castLE (by decide)) = {(finiteCheckIndex (n := 144) (lo := 80) (width := 8) (by decide) j)} := by decide +kernel

private theorem faceMask_vertex_part0011 : ∀ j : Fin 8,
    faceMask ((finiteCheckIndex (n := 144) (lo := 88) (width := 8) (by decide) j).castLE (by decide)) = {(finiteCheckIndex (n := 144) (lo := 88) (width := 8) (by decide) j)} := by decide +kernel

private theorem faceMask_vertex_part0012 : ∀ j : Fin 8,
    faceMask ((finiteCheckIndex (n := 144) (lo := 96) (width := 8) (by decide) j).castLE (by decide)) = {(finiteCheckIndex (n := 144) (lo := 96) (width := 8) (by decide) j)} := by decide +kernel

private theorem faceMask_vertex_part0013 : ∀ j : Fin 8,
    faceMask ((finiteCheckIndex (n := 144) (lo := 104) (width := 8) (by decide) j).castLE (by decide)) = {(finiteCheckIndex (n := 144) (lo := 104) (width := 8) (by decide) j)} := by decide +kernel

private theorem faceMask_vertex_part0014 : ∀ j : Fin 8,
    faceMask ((finiteCheckIndex (n := 144) (lo := 112) (width := 8) (by decide) j).castLE (by decide)) = {(finiteCheckIndex (n := 144) (lo := 112) (width := 8) (by decide) j)} := by decide +kernel

private theorem faceMask_vertex_part0015 : ∀ j : Fin 8,
    faceMask ((finiteCheckIndex (n := 144) (lo := 120) (width := 8) (by decide) j).castLE (by decide)) = {(finiteCheckIndex (n := 144) (lo := 120) (width := 8) (by decide) j)} := by decide +kernel

private theorem faceMask_vertex_part0016 : ∀ j : Fin 8,
    faceMask ((finiteCheckIndex (n := 144) (lo := 128) (width := 8) (by decide) j).castLE (by decide)) = {(finiteCheckIndex (n := 144) (lo := 128) (width := 8) (by decide) j)} := by decide +kernel

private theorem faceMask_vertex_part0017 : ∀ j : Fin 8,
    faceMask ((finiteCheckIndex (n := 144) (lo := 136) (width := 8) (by decide) j).castLE (by decide)) = {(finiteCheckIndex (n := 144) (lo := 136) (width := 8) (by decide) j)} := by decide +kernel

theorem faceMask_vertex : ∀ v : Fin 144, faceMask (v.castLE (by decide)) = {v} := by
  intro i
  have hi_bound := i.isLt
  by_cases h72 : i.val < 72
  ·
    by_cases h32 : i.val < 32
    ·
      by_cases h16 : i.val < 16
      ·
        by_cases h8 : i.val < 8
        ·
          exact finiteCheck_cover (lo := 0) (width := 8)
            (P := fun checkedIndex : Fin 144 => faceMask (checkedIndex.castLE (by decide)) = {checkedIndex})
            (by decide) faceMask_vertex_part0000 i (by omega) (by omega)
        ·
          exact finiteCheck_cover (lo := 8) (width := 8)
            (P := fun checkedIndex : Fin 144 => faceMask (checkedIndex.castLE (by decide)) = {checkedIndex})
            (by decide) faceMask_vertex_part0001 i (by omega) (by omega)
      ·
        by_cases h24 : i.val < 24
        ·
          exact finiteCheck_cover (lo := 16) (width := 8)
            (P := fun checkedIndex : Fin 144 => faceMask (checkedIndex.castLE (by decide)) = {checkedIndex})
            (by decide) faceMask_vertex_part0002 i (by omega) (by omega)
        ·
          exact finiteCheck_cover (lo := 24) (width := 8)
            (P := fun checkedIndex : Fin 144 => faceMask (checkedIndex.castLE (by decide)) = {checkedIndex})
            (by decide) faceMask_vertex_part0003 i (by omega) (by omega)
    ·
      by_cases h48 : i.val < 48
      ·
        by_cases h40 : i.val < 40
        ·
          exact finiteCheck_cover (lo := 32) (width := 8)
            (P := fun checkedIndex : Fin 144 => faceMask (checkedIndex.castLE (by decide)) = {checkedIndex})
            (by decide) faceMask_vertex_part0004 i (by omega) (by omega)
        ·
          exact finiteCheck_cover (lo := 40) (width := 8)
            (P := fun checkedIndex : Fin 144 => faceMask (checkedIndex.castLE (by decide)) = {checkedIndex})
            (by decide) faceMask_vertex_part0005 i (by omega) (by omega)
      ·
        by_cases h56 : i.val < 56
        ·
          exact finiteCheck_cover (lo := 48) (width := 8)
            (P := fun checkedIndex : Fin 144 => faceMask (checkedIndex.castLE (by decide)) = {checkedIndex})
            (by decide) faceMask_vertex_part0006 i (by omega) (by omega)
        ·
          by_cases h64 : i.val < 64
          ·
            exact finiteCheck_cover (lo := 56) (width := 8)
              (P := fun checkedIndex : Fin 144 => faceMask (checkedIndex.castLE (by decide)) = {checkedIndex})
              (by decide) faceMask_vertex_part0007 i (by omega) (by omega)
          ·
            exact finiteCheck_cover (lo := 64) (width := 8)
              (P := fun checkedIndex : Fin 144 => faceMask (checkedIndex.castLE (by decide)) = {checkedIndex})
              (by decide) faceMask_vertex_part0008 i (by omega) (by omega)
  ·
    by_cases h104 : i.val < 104
    ·
      by_cases h88 : i.val < 88
      ·
        by_cases h80 : i.val < 80
        ·
          exact finiteCheck_cover (lo := 72) (width := 8)
            (P := fun checkedIndex : Fin 144 => faceMask (checkedIndex.castLE (by decide)) = {checkedIndex})
            (by decide) faceMask_vertex_part0009 i (by omega) (by omega)
        ·
          exact finiteCheck_cover (lo := 80) (width := 8)
            (P := fun checkedIndex : Fin 144 => faceMask (checkedIndex.castLE (by decide)) = {checkedIndex})
            (by decide) faceMask_vertex_part0010 i (by omega) (by omega)
      ·
        by_cases h96 : i.val < 96
        ·
          exact finiteCheck_cover (lo := 88) (width := 8)
            (P := fun checkedIndex : Fin 144 => faceMask (checkedIndex.castLE (by decide)) = {checkedIndex})
            (by decide) faceMask_vertex_part0011 i (by omega) (by omega)
        ·
          exact finiteCheck_cover (lo := 96) (width := 8)
            (P := fun checkedIndex : Fin 144 => faceMask (checkedIndex.castLE (by decide)) = {checkedIndex})
            (by decide) faceMask_vertex_part0012 i (by omega) (by omega)
    ·
      by_cases h120 : i.val < 120
      ·
        by_cases h112 : i.val < 112
        ·
          exact finiteCheck_cover (lo := 104) (width := 8)
            (P := fun checkedIndex : Fin 144 => faceMask (checkedIndex.castLE (by decide)) = {checkedIndex})
            (by decide) faceMask_vertex_part0013 i (by omega) (by omega)
        ·
          exact finiteCheck_cover (lo := 112) (width := 8)
            (P := fun checkedIndex : Fin 144 => faceMask (checkedIndex.castLE (by decide)) = {checkedIndex})
            (by decide) faceMask_vertex_part0014 i (by omega) (by omega)
      ·
        by_cases h128 : i.val < 128
        ·
          exact finiteCheck_cover (lo := 120) (width := 8)
            (P := fun checkedIndex : Fin 144 => faceMask (checkedIndex.castLE (by decide)) = {checkedIndex})
            (by decide) faceMask_vertex_part0015 i (by omega) (by omega)
        ·
          by_cases h136 : i.val < 136
          ·
            exact finiteCheck_cover (lo := 128) (width := 8)
              (P := fun checkedIndex : Fin 144 => faceMask (checkedIndex.castLE (by decide)) = {checkedIndex})
              (by decide) faceMask_vertex_part0016 i (by omega) (by omega)
          ·
            exact finiteCheck_cover (lo := 136) (width := 8)
              (P := fun checkedIndex : Fin 144 => faceMask (checkedIndex.castLE (by decide)) = {checkedIndex})
              (by decide) faceMask_vertex_part0017 i (by omega) (by omega)

theorem faceFlag_self : ∀ i : Fin 1069, faceFlag i (faceRank i) = i :=
  fun i => (basicFaceChecks i).2.1

theorem faceFlag_strict : ∀ (i : Fin 1069) (k : Fin 4),
    faceMask (faceFlag i k.castSucc) ⊂ faceMask (faceFlag i k.succ) :=
  fun i => (basicFaceChecks i).2.2.1

theorem faceFlag_rank : ∀ (i : Fin 1069) (k : Fin 5),
    faceRank (faceFlag i k) = k :=
  fun i => (basicFaceChecks i).2.2.2.1

theorem lowerFacets_nonempty : ∀ i : Fin 1069,
    1 ≤ (faceRank i).val → (lowerFacets i).Nonempty :=
  fun i => (basicFaceChecks i).2.2.2.2.1

theorem faceRank_zero : ∀ i : Fin 1069, faceRank i = 0 →
    ∃ v : Fin 144, v.castLE (by decide) = i :=
  fun i => (basicFaceChecks i).2.2.2.2.2.1

theorem faceRank_three : ∀ i : Fin 1069, faceRank i = 3 →
    ∃ f : Fin 130, codeFace f 0 = i :=
  fun i => (basicFaceChecks i).2.2.2.2.2.2.1

theorem faceRank_four : ∀ i : Fin 1069, faceRank i = 4 ↔ i = 1068 :=
  fun i => (basicFaceChecks i).2.2.2.2.2.2.2

private theorem codeFace_rank_zero_part0000 : ∀ j : Fin 8,
    faceRank (codeFace (finiteCheckIndex (n := 130) (lo := 0) (width := 8) (by decide) j) 0) = 3 := by decide +kernel

private theorem codeFace_rank_zero_part0001 : ∀ j : Fin 8,
    faceRank (codeFace (finiteCheckIndex (n := 130) (lo := 8) (width := 8) (by decide) j) 0) = 3 := by decide +kernel

private theorem codeFace_rank_zero_part0002 : ∀ j : Fin 8,
    faceRank (codeFace (finiteCheckIndex (n := 130) (lo := 16) (width := 8) (by decide) j) 0) = 3 := by decide +kernel

private theorem codeFace_rank_zero_part0003 : ∀ j : Fin 8,
    faceRank (codeFace (finiteCheckIndex (n := 130) (lo := 24) (width := 8) (by decide) j) 0) = 3 := by decide +kernel

private theorem codeFace_rank_zero_part0004 : ∀ j : Fin 8,
    faceRank (codeFace (finiteCheckIndex (n := 130) (lo := 32) (width := 8) (by decide) j) 0) = 3 := by decide +kernel

private theorem codeFace_rank_zero_part0005 : ∀ j : Fin 8,
    faceRank (codeFace (finiteCheckIndex (n := 130) (lo := 40) (width := 8) (by decide) j) 0) = 3 := by decide +kernel

private theorem codeFace_rank_zero_part0006 : ∀ j : Fin 8,
    faceRank (codeFace (finiteCheckIndex (n := 130) (lo := 48) (width := 8) (by decide) j) 0) = 3 := by decide +kernel

private theorem codeFace_rank_zero_part0007 : ∀ j : Fin 8,
    faceRank (codeFace (finiteCheckIndex (n := 130) (lo := 56) (width := 8) (by decide) j) 0) = 3 := by decide +kernel

private theorem codeFace_rank_zero_part0008 : ∀ j : Fin 8,
    faceRank (codeFace (finiteCheckIndex (n := 130) (lo := 64) (width := 8) (by decide) j) 0) = 3 := by decide +kernel

private theorem codeFace_rank_zero_part0009 : ∀ j : Fin 8,
    faceRank (codeFace (finiteCheckIndex (n := 130) (lo := 72) (width := 8) (by decide) j) 0) = 3 := by decide +kernel

private theorem codeFace_rank_zero_part0010 : ∀ j : Fin 8,
    faceRank (codeFace (finiteCheckIndex (n := 130) (lo := 80) (width := 8) (by decide) j) 0) = 3 := by decide +kernel

private theorem codeFace_rank_zero_part0011 : ∀ j : Fin 8,
    faceRank (codeFace (finiteCheckIndex (n := 130) (lo := 88) (width := 8) (by decide) j) 0) = 3 := by decide +kernel

private theorem codeFace_rank_zero_part0012 : ∀ j : Fin 8,
    faceRank (codeFace (finiteCheckIndex (n := 130) (lo := 96) (width := 8) (by decide) j) 0) = 3 := by decide +kernel

private theorem codeFace_rank_zero_part0013 : ∀ j : Fin 8,
    faceRank (codeFace (finiteCheckIndex (n := 130) (lo := 104) (width := 8) (by decide) j) 0) = 3 := by decide +kernel

private theorem codeFace_rank_zero_part0014 : ∀ j : Fin 8,
    faceRank (codeFace (finiteCheckIndex (n := 130) (lo := 112) (width := 8) (by decide) j) 0) = 3 := by decide +kernel

private theorem codeFace_rank_zero_part0015 : ∀ j : Fin 8,
    faceRank (codeFace (finiteCheckIndex (n := 130) (lo := 120) (width := 8) (by decide) j) 0) = 3 := by decide +kernel

private theorem codeFace_rank_zero_part0016 : ∀ j : Fin 2,
    faceRank (codeFace (finiteCheckIndex (n := 130) (lo := 128) (width := 2) (by decide) j) 0) = 3 := by decide +kernel

theorem codeFace_rank_zero : ∀ f : Fin 130, faceRank (codeFace f 0) = 3 := by
  intro i
  have hi_bound := i.isLt
  by_cases h64 : i.val < 64
  ·
    by_cases h32 : i.val < 32
    ·
      by_cases h16 : i.val < 16
      ·
        by_cases h8 : i.val < 8
        ·
          exact finiteCheck_cover (lo := 0) (width := 8)
            (P := fun checkedIndex : Fin 130 => faceRank (codeFace checkedIndex 0) = 3)
            (by decide) codeFace_rank_zero_part0000 i (by omega) (by omega)
        ·
          exact finiteCheck_cover (lo := 8) (width := 8)
            (P := fun checkedIndex : Fin 130 => faceRank (codeFace checkedIndex 0) = 3)
            (by decide) codeFace_rank_zero_part0001 i (by omega) (by omega)
      ·
        by_cases h24 : i.val < 24
        ·
          exact finiteCheck_cover (lo := 16) (width := 8)
            (P := fun checkedIndex : Fin 130 => faceRank (codeFace checkedIndex 0) = 3)
            (by decide) codeFace_rank_zero_part0002 i (by omega) (by omega)
        ·
          exact finiteCheck_cover (lo := 24) (width := 8)
            (P := fun checkedIndex : Fin 130 => faceRank (codeFace checkedIndex 0) = 3)
            (by decide) codeFace_rank_zero_part0003 i (by omega) (by omega)
    ·
      by_cases h48 : i.val < 48
      ·
        by_cases h40 : i.val < 40
        ·
          exact finiteCheck_cover (lo := 32) (width := 8)
            (P := fun checkedIndex : Fin 130 => faceRank (codeFace checkedIndex 0) = 3)
            (by decide) codeFace_rank_zero_part0004 i (by omega) (by omega)
        ·
          exact finiteCheck_cover (lo := 40) (width := 8)
            (P := fun checkedIndex : Fin 130 => faceRank (codeFace checkedIndex 0) = 3)
            (by decide) codeFace_rank_zero_part0005 i (by omega) (by omega)
      ·
        by_cases h56 : i.val < 56
        ·
          exact finiteCheck_cover (lo := 48) (width := 8)
            (P := fun checkedIndex : Fin 130 => faceRank (codeFace checkedIndex 0) = 3)
            (by decide) codeFace_rank_zero_part0006 i (by omega) (by omega)
        ·
          exact finiteCheck_cover (lo := 56) (width := 8)
            (P := fun checkedIndex : Fin 130 => faceRank (codeFace checkedIndex 0) = 3)
            (by decide) codeFace_rank_zero_part0007 i (by omega) (by omega)
  ·
    by_cases h96 : i.val < 96
    ·
      by_cases h80 : i.val < 80
      ·
        by_cases h72 : i.val < 72
        ·
          exact finiteCheck_cover (lo := 64) (width := 8)
            (P := fun checkedIndex : Fin 130 => faceRank (codeFace checkedIndex 0) = 3)
            (by decide) codeFace_rank_zero_part0008 i (by omega) (by omega)
        ·
          exact finiteCheck_cover (lo := 72) (width := 8)
            (P := fun checkedIndex : Fin 130 => faceRank (codeFace checkedIndex 0) = 3)
            (by decide) codeFace_rank_zero_part0009 i (by omega) (by omega)
      ·
        by_cases h88 : i.val < 88
        ·
          exact finiteCheck_cover (lo := 80) (width := 8)
            (P := fun checkedIndex : Fin 130 => faceRank (codeFace checkedIndex 0) = 3)
            (by decide) codeFace_rank_zero_part0010 i (by omega) (by omega)
        ·
          exact finiteCheck_cover (lo := 88) (width := 8)
            (P := fun checkedIndex : Fin 130 => faceRank (codeFace checkedIndex 0) = 3)
            (by decide) codeFace_rank_zero_part0011 i (by omega) (by omega)
    ·
      by_cases h112 : i.val < 112
      ·
        by_cases h104 : i.val < 104
        ·
          exact finiteCheck_cover (lo := 96) (width := 8)
            (P := fun checkedIndex : Fin 130 => faceRank (codeFace checkedIndex 0) = 3)
            (by decide) codeFace_rank_zero_part0012 i (by omega) (by omega)
        ·
          exact finiteCheck_cover (lo := 104) (width := 8)
            (P := fun checkedIndex : Fin 130 => faceRank (codeFace checkedIndex 0) = 3)
            (by decide) codeFace_rank_zero_part0013 i (by omega) (by omega)
      ·
        by_cases h120 : i.val < 120
        ·
          exact finiteCheck_cover (lo := 112) (width := 8)
            (P := fun checkedIndex : Fin 130 => faceRank (codeFace checkedIndex 0) = 3)
            (by decide) codeFace_rank_zero_part0014 i (by omega) (by omega)
        ·
          by_cases h128 : i.val < 128
          ·
            exact finiteCheck_cover (lo := 120) (width := 8)
              (P := fun checkedIndex : Fin 130 => faceRank (codeFace checkedIndex 0) = 3)
              (by decide) codeFace_rank_zero_part0015 i (by omega) (by omega)
          ·
            exact finiteCheck_cover (lo := 128) (width := 2)
              (P := fun checkedIndex : Fin 130 => faceRank (codeFace checkedIndex 0) = 3)
              (by decide) codeFace_rank_zero_part0016 i (by omega) (by omega)

private theorem faceRank_cardinality_part0000 : ∀ j : Fin 1,
    (Finset.univ.filter (fun i : Fin 1069 => faceRank i = (finiteCheckIndex (n := 5) (lo := 0) (width := 1) (by decide) j))).card =
      (![144, 404, 390, 130, 1] : Fin 5 → ℕ) (finiteCheckIndex (n := 5) (lo := 0) (width := 1) (by decide) j) := by decide +kernel

private theorem faceRank_cardinality_part0001 : ∀ j : Fin 1,
    (Finset.univ.filter (fun i : Fin 1069 => faceRank i = (finiteCheckIndex (n := 5) (lo := 1) (width := 1) (by decide) j))).card =
      (![144, 404, 390, 130, 1] : Fin 5 → ℕ) (finiteCheckIndex (n := 5) (lo := 1) (width := 1) (by decide) j) := by decide +kernel

private theorem faceRank_cardinality_part0002 : ∀ j : Fin 1,
    (Finset.univ.filter (fun i : Fin 1069 => faceRank i = (finiteCheckIndex (n := 5) (lo := 2) (width := 1) (by decide) j))).card =
      (![144, 404, 390, 130, 1] : Fin 5 → ℕ) (finiteCheckIndex (n := 5) (lo := 2) (width := 1) (by decide) j) := by decide +kernel

private theorem faceRank_cardinality_part0003 : ∀ j : Fin 1,
    (Finset.univ.filter (fun i : Fin 1069 => faceRank i = (finiteCheckIndex (n := 5) (lo := 3) (width := 1) (by decide) j))).card =
      (![144, 404, 390, 130, 1] : Fin 5 → ℕ) (finiteCheckIndex (n := 5) (lo := 3) (width := 1) (by decide) j) := by decide +kernel

private theorem faceRank_cardinality_part0004 : ∀ j : Fin 1,
    (Finset.univ.filter (fun i : Fin 1069 => faceRank i = (finiteCheckIndex (n := 5) (lo := 4) (width := 1) (by decide) j))).card =
      (![144, 404, 390, 130, 1] : Fin 5 → ℕ) (finiteCheckIndex (n := 5) (lo := 4) (width := 1) (by decide) j) := by decide +kernel

theorem faceRank_cardinality : ∀ k : Fin 5,
    (Finset.univ.filter (fun i : Fin 1069 => faceRank i = k)).card =
      (![144, 404, 390, 130, 1] : Fin 5 → ℕ) k := by
  intro i
  have hi_bound := i.isLt
  by_cases h2 : i.val < 2
  ·
    by_cases h1 : i.val < 1
    ·
      exact finiteCheck_cover (lo := 0) (width := 1)
        (P := fun checkedIndex : Fin 5 => (Finset.univ.filter (fun i : Fin 1069 => faceRank i = checkedIndex)).card =
                (![144, 404, 390, 130, 1] : Fin 5 → ℕ) checkedIndex)
        (by decide) faceRank_cardinality_part0000 i (by omega) (by omega)
    ·
      exact finiteCheck_cover (lo := 1) (width := 1)
        (P := fun checkedIndex : Fin 5 => (Finset.univ.filter (fun i : Fin 1069 => faceRank i = checkedIndex)).card =
                (![144, 404, 390, 130, 1] : Fin 5 → ℕ) checkedIndex)
        (by decide) faceRank_cardinality_part0001 i (by omega) (by omega)
  ·
    by_cases h3 : i.val < 3
    ·
      exact finiteCheck_cover (lo := 2) (width := 1)
        (P := fun checkedIndex : Fin 5 => (Finset.univ.filter (fun i : Fin 1069 => faceRank i = checkedIndex)).card =
                (![144, 404, 390, 130, 1] : Fin 5 → ℕ) checkedIndex)
        (by decide) faceRank_cardinality_part0002 i (by omega) (by omega)
    ·
      by_cases h4 : i.val < 4
      ·
        exact finiteCheck_cover (lo := 3) (width := 1)
          (P := fun checkedIndex : Fin 5 => (Finset.univ.filter (fun i : Fin 1069 => faceRank i = checkedIndex)).card =
                  (![144, 404, 390, 130, 1] : Fin 5 → ℕ) checkedIndex)
          (by decide) faceRank_cardinality_part0003 i (by omega) (by omega)
      ·
        exact finiteCheck_cover (lo := 4) (width := 1)
          (P := fun checkedIndex : Fin 5 => (Finset.univ.filter (fun i : Fin 1069 => faceRank i = checkedIndex)).card =
                  (![144, 404, 390, 130, 1] : Fin 5 → ℕ) checkedIndex)
          (by decide) faceRank_cardinality_part0004 i (by omega) (by omega)

private theorem edgeMask_part0000 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 0) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 0) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 0) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 0) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0001 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 4) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 4) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 4) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 4) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0002 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 8) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 8) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 8) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 8) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0003 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 12) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 12) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 12) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 12) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0004 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 16) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 16) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 16) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 16) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0005 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 20) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 20) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 20) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 20) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0006 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 24) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 24) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 24) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 24) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0007 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 28) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 28) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 28) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 28) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0008 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 32) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 32) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 32) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 32) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0009 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 36) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 36) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 36) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 36) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0010 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 40) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 40) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 40) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 40) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0011 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 44) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 44) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 44) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 44) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0012 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 48) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 48) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 48) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 48) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0013 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 52) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 52) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 52) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 52) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0014 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 56) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 56) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 56) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 56) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0015 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 60) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 60) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 60) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 60) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0016 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 64) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 64) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 64) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 64) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0017 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 68) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 68) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 68) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 68) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0018 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 72) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 72) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 72) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 72) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0019 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 76) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 76) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 76) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 76) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0020 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 80) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 80) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 80) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 80) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0021 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 84) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 84) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 84) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 84) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0022 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 88) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 88) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 88) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 88) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0023 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 92) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 92) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 92) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 92) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0024 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 96) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 96) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 96) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 96) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0025 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 100) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 100) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 100) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 100) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0026 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 104) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 104) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 104) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 104) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0027 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 108) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 108) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 108) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 108) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0028 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 112) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 112) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 112) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 112) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0029 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 116) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 116) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 116) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 116) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0030 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 120) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 120) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 120) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 120) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0031 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 124) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 124) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 124) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 124) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0032 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 128) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 128) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 128) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 128) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0033 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 132) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 132) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 132) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 132) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0034 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 136) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 136) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 136) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 136) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0035 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 140) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 140) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 140) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 140) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0036 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 144) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 144) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 144) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 144) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0037 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 148) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 148) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 148) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 148) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0038 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 152) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 152) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 152) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 152) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0039 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 156) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 156) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 156) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 156) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0040 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 160) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 160) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 160) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 160) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0041 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 164) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 164) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 164) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 164) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0042 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 168) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 168) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 168) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 168) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0043 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 172) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 172) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 172) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 172) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0044 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 176) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 176) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 176) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 176) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0045 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 180) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 180) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 180) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 180) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0046 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 184) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 184) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 184) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 184) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0047 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 188) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 188) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 188) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 188) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0048 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 192) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 192) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 192) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 192) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0049 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 196) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 196) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 196) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 196) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0050 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 200) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 200) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 200) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 200) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0051 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 204) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 204) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 204) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 204) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0052 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 208) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 208) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 208) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 208) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0053 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 212) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 212) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 212) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 212) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0054 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 216) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 216) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 216) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 216) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0055 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 220) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 220) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 220) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 220) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0056 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 224) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 224) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 224) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 224) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0057 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 228) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 228) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 228) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 228) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0058 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 232) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 232) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 232) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 232) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0059 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 236) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 236) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 236) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 236) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0060 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 240) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 240) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 240) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 240) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0061 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 244) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 244) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 244) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 244) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0062 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 248) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 248) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 248) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 248) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0063 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 252) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 252) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 252) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 252) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0064 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 256) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 256) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 256) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 256) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0065 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 260) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 260) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 260) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 260) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0066 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 264) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 264) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 264) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 264) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0067 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 268) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 268) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 268) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 268) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0068 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 272) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 272) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 272) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 272) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0069 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 276) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 276) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 276) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 276) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0070 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 280) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 280) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 280) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 280) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0071 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 284) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 284) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 284) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 284) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0072 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 288) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 288) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 288) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 288) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0073 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 292) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 292) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 292) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 292) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0074 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 296) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 296) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 296) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 296) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0075 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 300) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 300) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 300) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 300) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0076 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 304) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 304) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 304) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 304) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0077 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 308) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 308) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 308) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 308) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0078 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 312) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 312) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 312) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 312) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0079 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 316) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 316) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 316) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 316) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0080 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 320) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 320) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 320) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 320) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0081 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 324) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 324) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 324) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 324) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0082 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 328) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 328) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 328) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 328) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0083 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 332) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 332) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 332) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 332) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0084 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 336) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 336) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 336) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 336) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0085 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 340) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 340) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 340) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 340) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0086 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 344) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 344) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 344) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 344) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0087 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 348) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 348) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 348) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 348) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0088 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 352) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 352) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 352) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 352) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0089 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 356) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 356) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 356) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 356) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0090 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 360) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 360) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 360) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 360) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0091 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 364) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 364) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 364) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 364) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0092 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 368) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 368) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 368) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 368) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0093 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 372) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 372) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 372) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 372) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0094 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 376) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 376) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 376) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 376) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0095 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 380) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 380) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 380) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 380) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0096 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 384) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 384) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 384) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 384) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0097 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 388) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 388) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 388) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 388) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0098 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 392) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 392) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 392) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 392) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0099 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 396) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 396) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 396) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 396) (width := 4) (by decide) j) 1} := by decide +kernel

private theorem edgeMask_part0100 : ∀ j : Fin 4,
    faceMask ⟨144 + (finiteCheckIndex (n := 404) (lo := 400) (width := 4) (by decide) j).val, by have := (finiteCheckIndex (n := 404) (lo := 400) (width := 4) (by decide) j).isLt; omega⟩ =
      {edgeVertex (finiteCheckIndex (n := 404) (lo := 400) (width := 4) (by decide) j) 0, edgeVertex (finiteCheckIndex (n := 404) (lo := 400) (width := 4) (by decide) j) 1} := by decide +kernel

theorem edgeMask : ∀ e : Fin 404,
    faceMask ⟨144 + e.val, by omega⟩ = {edgeVertex e 0, edgeVertex e 1} := by
  intro i
  have hi_bound := i.isLt
  by_cases h200 : i.val < 200
  ·
    by_cases h100 : i.val < 100
    ·
      by_cases h48 : i.val < 48
      ·
        by_cases h24 : i.val < 24
        ·
          by_cases h12 : i.val < 12
          ·
            by_cases h4 : i.val < 4
            ·
              exact finiteCheck_cover (lo := 0) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0000 i (by omega) (by omega)
            ·
              by_cases h8 : i.val < 8
              ·
                exact finiteCheck_cover (lo := 4) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0001 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 8) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0002 i (by omega) (by omega)
          ·
            by_cases h16 : i.val < 16
            ·
              exact finiteCheck_cover (lo := 12) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0003 i (by omega) (by omega)
            ·
              by_cases h20 : i.val < 20
              ·
                exact finiteCheck_cover (lo := 16) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0004 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 20) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0005 i (by omega) (by omega)
        ·
          by_cases h36 : i.val < 36
          ·
            by_cases h28 : i.val < 28
            ·
              exact finiteCheck_cover (lo := 24) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0006 i (by omega) (by omega)
            ·
              by_cases h32 : i.val < 32
              ·
                exact finiteCheck_cover (lo := 28) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0007 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 32) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0008 i (by omega) (by omega)
          ·
            by_cases h40 : i.val < 40
            ·
              exact finiteCheck_cover (lo := 36) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0009 i (by omega) (by omega)
            ·
              by_cases h44 : i.val < 44
              ·
                exact finiteCheck_cover (lo := 40) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0010 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 44) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0011 i (by omega) (by omega)
      ·
        by_cases h72 : i.val < 72
        ·
          by_cases h60 : i.val < 60
          ·
            by_cases h52 : i.val < 52
            ·
              exact finiteCheck_cover (lo := 48) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0012 i (by omega) (by omega)
            ·
              by_cases h56 : i.val < 56
              ·
                exact finiteCheck_cover (lo := 52) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0013 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 56) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0014 i (by omega) (by omega)
          ·
            by_cases h64 : i.val < 64
            ·
              exact finiteCheck_cover (lo := 60) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0015 i (by omega) (by omega)
            ·
              by_cases h68 : i.val < 68
              ·
                exact finiteCheck_cover (lo := 64) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0016 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 68) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0017 i (by omega) (by omega)
        ·
          by_cases h84 : i.val < 84
          ·
            by_cases h76 : i.val < 76
            ·
              exact finiteCheck_cover (lo := 72) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0018 i (by omega) (by omega)
            ·
              by_cases h80 : i.val < 80
              ·
                exact finiteCheck_cover (lo := 76) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0019 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 80) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0020 i (by omega) (by omega)
          ·
            by_cases h92 : i.val < 92
            ·
              by_cases h88 : i.val < 88
              ·
                exact finiteCheck_cover (lo := 84) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0021 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 88) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0022 i (by omega) (by omega)
            ·
              by_cases h96 : i.val < 96
              ·
                exact finiteCheck_cover (lo := 92) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0023 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 96) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0024 i (by omega) (by omega)
    ·
      by_cases h148 : i.val < 148
      ·
        by_cases h124 : i.val < 124
        ·
          by_cases h112 : i.val < 112
          ·
            by_cases h104 : i.val < 104
            ·
              exact finiteCheck_cover (lo := 100) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0025 i (by omega) (by omega)
            ·
              by_cases h108 : i.val < 108
              ·
                exact finiteCheck_cover (lo := 104) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0026 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 108) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0027 i (by omega) (by omega)
          ·
            by_cases h116 : i.val < 116
            ·
              exact finiteCheck_cover (lo := 112) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0028 i (by omega) (by omega)
            ·
              by_cases h120 : i.val < 120
              ·
                exact finiteCheck_cover (lo := 116) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0029 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 120) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0030 i (by omega) (by omega)
        ·
          by_cases h136 : i.val < 136
          ·
            by_cases h128 : i.val < 128
            ·
              exact finiteCheck_cover (lo := 124) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0031 i (by omega) (by omega)
            ·
              by_cases h132 : i.val < 132
              ·
                exact finiteCheck_cover (lo := 128) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0032 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 132) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0033 i (by omega) (by omega)
          ·
            by_cases h140 : i.val < 140
            ·
              exact finiteCheck_cover (lo := 136) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0034 i (by omega) (by omega)
            ·
              by_cases h144 : i.val < 144
              ·
                exact finiteCheck_cover (lo := 140) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0035 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 144) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0036 i (by omega) (by omega)
      ·
        by_cases h172 : i.val < 172
        ·
          by_cases h160 : i.val < 160
          ·
            by_cases h152 : i.val < 152
            ·
              exact finiteCheck_cover (lo := 148) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0037 i (by omega) (by omega)
            ·
              by_cases h156 : i.val < 156
              ·
                exact finiteCheck_cover (lo := 152) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0038 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 156) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0039 i (by omega) (by omega)
          ·
            by_cases h164 : i.val < 164
            ·
              exact finiteCheck_cover (lo := 160) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0040 i (by omega) (by omega)
            ·
              by_cases h168 : i.val < 168
              ·
                exact finiteCheck_cover (lo := 164) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0041 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 168) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0042 i (by omega) (by omega)
        ·
          by_cases h184 : i.val < 184
          ·
            by_cases h176 : i.val < 176
            ·
              exact finiteCheck_cover (lo := 172) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0043 i (by omega) (by omega)
            ·
              by_cases h180 : i.val < 180
              ·
                exact finiteCheck_cover (lo := 176) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0044 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 180) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0045 i (by omega) (by omega)
          ·
            by_cases h192 : i.val < 192
            ·
              by_cases h188 : i.val < 188
              ·
                exact finiteCheck_cover (lo := 184) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0046 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 188) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0047 i (by omega) (by omega)
            ·
              by_cases h196 : i.val < 196
              ·
                exact finiteCheck_cover (lo := 192) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0048 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 196) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0049 i (by omega) (by omega)
  ·
    by_cases h300 : i.val < 300
    ·
      by_cases h248 : i.val < 248
      ·
        by_cases h224 : i.val < 224
        ·
          by_cases h212 : i.val < 212
          ·
            by_cases h204 : i.val < 204
            ·
              exact finiteCheck_cover (lo := 200) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0050 i (by omega) (by omega)
            ·
              by_cases h208 : i.val < 208
              ·
                exact finiteCheck_cover (lo := 204) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0051 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 208) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0052 i (by omega) (by omega)
          ·
            by_cases h216 : i.val < 216
            ·
              exact finiteCheck_cover (lo := 212) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0053 i (by omega) (by omega)
            ·
              by_cases h220 : i.val < 220
              ·
                exact finiteCheck_cover (lo := 216) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0054 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 220) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0055 i (by omega) (by omega)
        ·
          by_cases h236 : i.val < 236
          ·
            by_cases h228 : i.val < 228
            ·
              exact finiteCheck_cover (lo := 224) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0056 i (by omega) (by omega)
            ·
              by_cases h232 : i.val < 232
              ·
                exact finiteCheck_cover (lo := 228) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0057 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 232) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0058 i (by omega) (by omega)
          ·
            by_cases h240 : i.val < 240
            ·
              exact finiteCheck_cover (lo := 236) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0059 i (by omega) (by omega)
            ·
              by_cases h244 : i.val < 244
              ·
                exact finiteCheck_cover (lo := 240) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0060 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 244) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0061 i (by omega) (by omega)
      ·
        by_cases h272 : i.val < 272
        ·
          by_cases h260 : i.val < 260
          ·
            by_cases h252 : i.val < 252
            ·
              exact finiteCheck_cover (lo := 248) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0062 i (by omega) (by omega)
            ·
              by_cases h256 : i.val < 256
              ·
                exact finiteCheck_cover (lo := 252) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0063 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 256) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0064 i (by omega) (by omega)
          ·
            by_cases h264 : i.val < 264
            ·
              exact finiteCheck_cover (lo := 260) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0065 i (by omega) (by omega)
            ·
              by_cases h268 : i.val < 268
              ·
                exact finiteCheck_cover (lo := 264) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0066 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 268) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0067 i (by omega) (by omega)
        ·
          by_cases h284 : i.val < 284
          ·
            by_cases h276 : i.val < 276
            ·
              exact finiteCheck_cover (lo := 272) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0068 i (by omega) (by omega)
            ·
              by_cases h280 : i.val < 280
              ·
                exact finiteCheck_cover (lo := 276) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0069 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 280) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0070 i (by omega) (by omega)
          ·
            by_cases h292 : i.val < 292
            ·
              by_cases h288 : i.val < 288
              ·
                exact finiteCheck_cover (lo := 284) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0071 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 288) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0072 i (by omega) (by omega)
            ·
              by_cases h296 : i.val < 296
              ·
                exact finiteCheck_cover (lo := 292) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0073 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 296) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0074 i (by omega) (by omega)
    ·
      by_cases h352 : i.val < 352
      ·
        by_cases h324 : i.val < 324
        ·
          by_cases h312 : i.val < 312
          ·
            by_cases h304 : i.val < 304
            ·
              exact finiteCheck_cover (lo := 300) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0075 i (by omega) (by omega)
            ·
              by_cases h308 : i.val < 308
              ·
                exact finiteCheck_cover (lo := 304) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0076 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 308) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0077 i (by omega) (by omega)
          ·
            by_cases h316 : i.val < 316
            ·
              exact finiteCheck_cover (lo := 312) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0078 i (by omega) (by omega)
            ·
              by_cases h320 : i.val < 320
              ·
                exact finiteCheck_cover (lo := 316) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0079 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 320) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0080 i (by omega) (by omega)
        ·
          by_cases h336 : i.val < 336
          ·
            by_cases h328 : i.val < 328
            ·
              exact finiteCheck_cover (lo := 324) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0081 i (by omega) (by omega)
            ·
              by_cases h332 : i.val < 332
              ·
                exact finiteCheck_cover (lo := 328) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0082 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 332) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0083 i (by omega) (by omega)
          ·
            by_cases h344 : i.val < 344
            ·
              by_cases h340 : i.val < 340
              ·
                exact finiteCheck_cover (lo := 336) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0084 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 340) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0085 i (by omega) (by omega)
            ·
              by_cases h348 : i.val < 348
              ·
                exact finiteCheck_cover (lo := 344) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0086 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 348) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0087 i (by omega) (by omega)
      ·
        by_cases h376 : i.val < 376
        ·
          by_cases h364 : i.val < 364
          ·
            by_cases h356 : i.val < 356
            ·
              exact finiteCheck_cover (lo := 352) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0088 i (by omega) (by omega)
            ·
              by_cases h360 : i.val < 360
              ·
                exact finiteCheck_cover (lo := 356) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0089 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 360) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0090 i (by omega) (by omega)
          ·
            by_cases h368 : i.val < 368
            ·
              exact finiteCheck_cover (lo := 364) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0091 i (by omega) (by omega)
            ·
              by_cases h372 : i.val < 372
              ·
                exact finiteCheck_cover (lo := 368) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0092 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 372) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0093 i (by omega) (by omega)
        ·
          by_cases h388 : i.val < 388
          ·
            by_cases h380 : i.val < 380
            ·
              exact finiteCheck_cover (lo := 376) (width := 4)
                (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                        {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                (by decide) edgeMask_part0094 i (by omega) (by omega)
            ·
              by_cases h384 : i.val < 384
              ·
                exact finiteCheck_cover (lo := 380) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0095 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 384) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0096 i (by omega) (by omega)
          ·
            by_cases h396 : i.val < 396
            ·
              by_cases h392 : i.val < 392
              ·
                exact finiteCheck_cover (lo := 388) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0097 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 392) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0098 i (by omega) (by omega)
            ·
              by_cases h400 : i.val < 400
              ·
                exact finiteCheck_cover (lo := 396) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0099 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 400) (width := 4)
                  (P := fun checkedIndex : Fin 404 => faceMask ⟨144 + checkedIndex.val, by have := checkedIndex.isLt; omega⟩ =
                          {edgeVertex checkedIndex 0, edgeVertex checkedIndex 1})
                  (by decide) edgeMask_part0100 i (by omega) (by omega)

/-- Three ordinary base-three coordinate-face digits. -/
def codeOfFin27 (c : Fin 27) : Cubical.Cube.FaceCode 3 := fun k =>
  match c.val / 3 ^ k.val % 3 with
  | 0 => .free
  | 1 => .fixed false
  | _ => .fixed true

/-- The eight ordinary binary vertex labels. -/
def bitsOfFin8 (b : Fin 8) : Cubical.Cube.Vertex 3 := fun k =>
  b.val / 2 ^ k.val % 2 == 1

local instance (a b : Cubical.Cube.FaceCoordinate) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (b = .free ∨ a = b))

local instance (c : Cubical.Cube.FaceCode 3) (b : Cubical.Cube.Vertex 3) :
    Decidable (Cubical.Cube.Matches c b) :=
  inferInstanceAs (Decidable (∀ k, c k = .free ∨ c k = .fixed (b k)))

def cubeCodeVertices (c : Fin 27) : Finset (Fin 8) :=
  Finset.univ.filter (fun b => Cubical.Cube.Matches (codeOfFin27 c) (bitsOfFin8 b))

theorem codeOfFin27_bijective : Function.Bijective codeOfFin27 := by decide +kernel

theorem bitsOfFin8_bijective : Function.Bijective bitsOfFin8 := by decide +kernel

private theorem cubeCodeVertices_zero : cubeCodeVertices 0 = Finset.univ := by
  decide +kernel

/-- Order of coordinate faces is exactly inclusion of their matching vertices. -/
private theorem cubeCodeVertices_le_iff (c d : Fin 27) :
    cubeCodeVertices c ⊆ cubeCodeVertices d ↔ codeOfFin27 c ≤ codeOfFin27 d := by
  rw [Cubical.Cube.faceCode_le_iff]
  constructor
  · intro h s hs
    obtain ⟨b, rfl⟩ := bitsOfFin8_bijective.2 s
    have hb : b ∈ cubeCodeVertices c := by simpa [cubeCodeVertices] using hs
    have hd := h hb
    simpa [cubeCodeVertices] using hd
  · intro h b hb
    have hs : Cubical.Cube.Matches (codeOfFin27 c) (bitsOfFin8 b) := by
      simpa [cubeCodeVertices] using hb
    have hd := h (bitsOfFin8 b) hs
    simpa [cubeCodeVertices] using hd

private theorem codeFace_mask_part0000 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 0) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 0) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0001 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 1) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 1) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0002 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 2) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 2) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0003 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 3) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 3) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0004 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 4) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 4) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0005 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 5) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 5) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0006 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 6) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 6) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0007 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 7) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 7) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0008 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 8) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 8) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0009 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 9) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 9) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0010 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 10) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 10) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0011 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 11) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 11) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0012 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 12) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 12) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0013 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 13) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 13) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0014 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 14) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 14) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0015 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 15) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 15) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0016 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 16) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 16) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0017 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 17) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 17) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0018 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 18) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 18) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0019 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 19) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 19) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0020 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 20) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 20) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0021 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 21) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 21) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0022 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 22) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 22) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0023 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 23) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 23) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0024 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 24) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 24) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0025 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 25) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 25) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0026 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 26) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 26) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0027 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 27) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 27) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0028 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 28) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 28) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0029 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 29) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 29) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0030 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 30) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 30) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0031 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 31) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 31) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0032 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 32) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 32) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0033 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 33) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 33) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0034 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 34) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 34) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0035 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 35) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 35) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0036 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 36) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 36) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0037 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 37) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 37) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0038 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 38) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 38) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0039 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 39) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 39) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0040 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 40) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 40) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0041 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 41) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 41) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0042 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 42) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 42) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0043 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 43) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 43) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0044 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 44) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 44) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0045 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 45) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 45) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0046 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 46) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 46) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0047 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 47) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 47) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0048 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 48) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 48) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0049 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 49) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 49) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0050 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 50) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 50) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0051 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 51) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 51) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0052 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 52) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 52) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0053 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 53) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 53) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0054 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 54) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 54) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0055 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 55) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 55) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0056 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 56) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 56) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0057 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 57) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 57) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0058 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 58) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 58) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0059 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 59) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 59) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0060 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 60) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 60) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0061 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 61) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 61) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0062 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 62) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 62) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0063 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 63) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 63) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0064 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 64) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 64) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0065 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 65) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 65) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0066 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 66) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 66) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0067 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 67) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 67) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0068 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 68) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 68) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0069 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 69) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 69) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0070 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 70) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 70) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0071 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 71) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 71) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0072 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 72) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 72) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0073 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 73) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 73) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0074 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 74) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 74) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0075 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 75) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 75) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0076 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 76) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 76) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0077 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 77) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 77) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0078 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 78) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 78) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0079 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 79) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 79) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0080 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 80) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 80) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0081 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 81) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 81) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0082 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 82) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 82) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0083 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 83) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 83) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0084 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 84) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 84) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0085 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 85) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 85) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0086 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 86) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 86) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0087 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 87) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 87) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0088 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 88) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 88) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0089 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 89) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 89) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0090 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 90) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 90) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0091 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 91) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 91) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0092 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 92) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 92) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0093 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 93) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 93) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0094 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 94) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 94) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0095 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 95) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 95) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0096 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 96) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 96) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0097 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 97) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 97) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0098 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 98) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 98) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0099 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 99) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 99) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0100 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 100) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 100) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0101 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 101) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 101) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0102 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 102) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 102) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0103 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 103) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 103) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0104 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 104) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 104) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0105 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 105) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 105) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0106 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 106) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 106) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0107 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 107) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 107) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0108 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 108) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 108) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0109 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 109) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 109) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0110 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 110) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 110) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0111 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 111) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 111) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0112 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 112) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 112) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0113 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 113) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 113) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0114 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 114) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 114) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0115 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 115) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 115) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0116 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 116) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 116) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0117 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 117) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 117) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0118 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 118) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 118) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0119 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 119) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 119) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0120 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 120) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 120) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0121 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 121) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 121) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0122 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 122) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 122) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0123 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 123) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 123) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0124 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 124) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 124) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0125 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 125) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 125) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0126 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 126) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 126) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0127 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 127) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 127) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0128 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 128) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 128) (width := 1) (by decide) j)) := by decide +kernel

private theorem codeFace_mask_part0129 : ∀ j : Fin 1,
    ∀ c : Fin 27, faceMask (codeFace (finiteCheckIndex (n := 130) (lo := 129) (width := 1) (by decide) j) c) =
      (cubeCodeVertices c).image (cubeVertex (finiteCheckIndex (n := 130) (lo := 129) (width := 1) (by decide) j)) := by decide +kernel

theorem codeFace_mask : ∀ (f : Fin 130) (c : Fin 27),
    faceMask (codeFace f c) = (cubeCodeVertices c).image (cubeVertex f) := by
  intro i
  have hi_bound := i.isLt
  by_cases h65 : i.val < 65
  ·
    by_cases h32 : i.val < 32
    ·
      by_cases h16 : i.val < 16
      ·
        by_cases h8 : i.val < 8
        ·
          by_cases h4 : i.val < 4
          ·
            by_cases h2 : i.val < 2
            ·
              by_cases h1 : i.val < 1
              ·
                exact finiteCheck_cover (lo := 0) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0000 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 1) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0001 i (by omega) (by omega)
            ·
              by_cases h3 : i.val < 3
              ·
                exact finiteCheck_cover (lo := 2) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0002 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 3) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0003 i (by omega) (by omega)
          ·
            by_cases h6 : i.val < 6
            ·
              by_cases h5 : i.val < 5
              ·
                exact finiteCheck_cover (lo := 4) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0004 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 5) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0005 i (by omega) (by omega)
            ·
              by_cases h7 : i.val < 7
              ·
                exact finiteCheck_cover (lo := 6) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0006 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 7) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0007 i (by omega) (by omega)
        ·
          by_cases h12 : i.val < 12
          ·
            by_cases h10 : i.val < 10
            ·
              by_cases h9 : i.val < 9
              ·
                exact finiteCheck_cover (lo := 8) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0008 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 9) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0009 i (by omega) (by omega)
            ·
              by_cases h11 : i.val < 11
              ·
                exact finiteCheck_cover (lo := 10) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0010 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 11) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0011 i (by omega) (by omega)
          ·
            by_cases h14 : i.val < 14
            ·
              by_cases h13 : i.val < 13
              ·
                exact finiteCheck_cover (lo := 12) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0012 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 13) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0013 i (by omega) (by omega)
            ·
              by_cases h15 : i.val < 15
              ·
                exact finiteCheck_cover (lo := 14) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0014 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 15) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0015 i (by omega) (by omega)
      ·
        by_cases h24 : i.val < 24
        ·
          by_cases h20 : i.val < 20
          ·
            by_cases h18 : i.val < 18
            ·
              by_cases h17 : i.val < 17
              ·
                exact finiteCheck_cover (lo := 16) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0016 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 17) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0017 i (by omega) (by omega)
            ·
              by_cases h19 : i.val < 19
              ·
                exact finiteCheck_cover (lo := 18) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0018 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 19) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0019 i (by omega) (by omega)
          ·
            by_cases h22 : i.val < 22
            ·
              by_cases h21 : i.val < 21
              ·
                exact finiteCheck_cover (lo := 20) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0020 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 21) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0021 i (by omega) (by omega)
            ·
              by_cases h23 : i.val < 23
              ·
                exact finiteCheck_cover (lo := 22) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0022 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 23) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0023 i (by omega) (by omega)
        ·
          by_cases h28 : i.val < 28
          ·
            by_cases h26 : i.val < 26
            ·
              by_cases h25 : i.val < 25
              ·
                exact finiteCheck_cover (lo := 24) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0024 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 25) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0025 i (by omega) (by omega)
            ·
              by_cases h27 : i.val < 27
              ·
                exact finiteCheck_cover (lo := 26) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0026 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 27) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0027 i (by omega) (by omega)
          ·
            by_cases h30 : i.val < 30
            ·
              by_cases h29 : i.val < 29
              ·
                exact finiteCheck_cover (lo := 28) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0028 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 29) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0029 i (by omega) (by omega)
            ·
              by_cases h31 : i.val < 31
              ·
                exact finiteCheck_cover (lo := 30) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0030 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 31) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0031 i (by omega) (by omega)
    ·
      by_cases h48 : i.val < 48
      ·
        by_cases h40 : i.val < 40
        ·
          by_cases h36 : i.val < 36
          ·
            by_cases h34 : i.val < 34
            ·
              by_cases h33 : i.val < 33
              ·
                exact finiteCheck_cover (lo := 32) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0032 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 33) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0033 i (by omega) (by omega)
            ·
              by_cases h35 : i.val < 35
              ·
                exact finiteCheck_cover (lo := 34) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0034 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 35) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0035 i (by omega) (by omega)
          ·
            by_cases h38 : i.val < 38
            ·
              by_cases h37 : i.val < 37
              ·
                exact finiteCheck_cover (lo := 36) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0036 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 37) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0037 i (by omega) (by omega)
            ·
              by_cases h39 : i.val < 39
              ·
                exact finiteCheck_cover (lo := 38) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0038 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 39) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0039 i (by omega) (by omega)
        ·
          by_cases h44 : i.val < 44
          ·
            by_cases h42 : i.val < 42
            ·
              by_cases h41 : i.val < 41
              ·
                exact finiteCheck_cover (lo := 40) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0040 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 41) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0041 i (by omega) (by omega)
            ·
              by_cases h43 : i.val < 43
              ·
                exact finiteCheck_cover (lo := 42) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0042 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 43) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0043 i (by omega) (by omega)
          ·
            by_cases h46 : i.val < 46
            ·
              by_cases h45 : i.val < 45
              ·
                exact finiteCheck_cover (lo := 44) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0044 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 45) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0045 i (by omega) (by omega)
            ·
              by_cases h47 : i.val < 47
              ·
                exact finiteCheck_cover (lo := 46) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0046 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 47) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0047 i (by omega) (by omega)
      ·
        by_cases h56 : i.val < 56
        ·
          by_cases h52 : i.val < 52
          ·
            by_cases h50 : i.val < 50
            ·
              by_cases h49 : i.val < 49
              ·
                exact finiteCheck_cover (lo := 48) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0048 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 49) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0049 i (by omega) (by omega)
            ·
              by_cases h51 : i.val < 51
              ·
                exact finiteCheck_cover (lo := 50) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0050 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 51) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0051 i (by omega) (by omega)
          ·
            by_cases h54 : i.val < 54
            ·
              by_cases h53 : i.val < 53
              ·
                exact finiteCheck_cover (lo := 52) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0052 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 53) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0053 i (by omega) (by omega)
            ·
              by_cases h55 : i.val < 55
              ·
                exact finiteCheck_cover (lo := 54) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0054 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 55) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0055 i (by omega) (by omega)
        ·
          by_cases h60 : i.val < 60
          ·
            by_cases h58 : i.val < 58
            ·
              by_cases h57 : i.val < 57
              ·
                exact finiteCheck_cover (lo := 56) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0056 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 57) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0057 i (by omega) (by omega)
            ·
              by_cases h59 : i.val < 59
              ·
                exact finiteCheck_cover (lo := 58) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0058 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 59) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0059 i (by omega) (by omega)
          ·
            by_cases h62 : i.val < 62
            ·
              by_cases h61 : i.val < 61
              ·
                exact finiteCheck_cover (lo := 60) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0060 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 61) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0061 i (by omega) (by omega)
            ·
              by_cases h63 : i.val < 63
              ·
                exact finiteCheck_cover (lo := 62) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0062 i (by omega) (by omega)
              ·
                by_cases h64 : i.val < 64
                ·
                  exact finiteCheck_cover (lo := 63) (width := 1)
                    (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                            (cubeCodeVertices c).image (cubeVertex checkedIndex))
                    (by decide) codeFace_mask_part0063 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 64) (width := 1)
                    (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                            (cubeCodeVertices c).image (cubeVertex checkedIndex))
                    (by decide) codeFace_mask_part0064 i (by omega) (by omega)
  ·
    by_cases h97 : i.val < 97
    ·
      by_cases h81 : i.val < 81
      ·
        by_cases h73 : i.val < 73
        ·
          by_cases h69 : i.val < 69
          ·
            by_cases h67 : i.val < 67
            ·
              by_cases h66 : i.val < 66
              ·
                exact finiteCheck_cover (lo := 65) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0065 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 66) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0066 i (by omega) (by omega)
            ·
              by_cases h68 : i.val < 68
              ·
                exact finiteCheck_cover (lo := 67) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0067 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 68) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0068 i (by omega) (by omega)
          ·
            by_cases h71 : i.val < 71
            ·
              by_cases h70 : i.val < 70
              ·
                exact finiteCheck_cover (lo := 69) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0069 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 70) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0070 i (by omega) (by omega)
            ·
              by_cases h72 : i.val < 72
              ·
                exact finiteCheck_cover (lo := 71) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0071 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 72) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0072 i (by omega) (by omega)
        ·
          by_cases h77 : i.val < 77
          ·
            by_cases h75 : i.val < 75
            ·
              by_cases h74 : i.val < 74
              ·
                exact finiteCheck_cover (lo := 73) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0073 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 74) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0074 i (by omega) (by omega)
            ·
              by_cases h76 : i.val < 76
              ·
                exact finiteCheck_cover (lo := 75) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0075 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 76) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0076 i (by omega) (by omega)
          ·
            by_cases h79 : i.val < 79
            ·
              by_cases h78 : i.val < 78
              ·
                exact finiteCheck_cover (lo := 77) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0077 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 78) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0078 i (by omega) (by omega)
            ·
              by_cases h80 : i.val < 80
              ·
                exact finiteCheck_cover (lo := 79) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0079 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 80) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0080 i (by omega) (by omega)
      ·
        by_cases h89 : i.val < 89
        ·
          by_cases h85 : i.val < 85
          ·
            by_cases h83 : i.val < 83
            ·
              by_cases h82 : i.val < 82
              ·
                exact finiteCheck_cover (lo := 81) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0081 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 82) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0082 i (by omega) (by omega)
            ·
              by_cases h84 : i.val < 84
              ·
                exact finiteCheck_cover (lo := 83) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0083 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 84) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0084 i (by omega) (by omega)
          ·
            by_cases h87 : i.val < 87
            ·
              by_cases h86 : i.val < 86
              ·
                exact finiteCheck_cover (lo := 85) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0085 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 86) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0086 i (by omega) (by omega)
            ·
              by_cases h88 : i.val < 88
              ·
                exact finiteCheck_cover (lo := 87) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0087 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 88) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0088 i (by omega) (by omega)
        ·
          by_cases h93 : i.val < 93
          ·
            by_cases h91 : i.val < 91
            ·
              by_cases h90 : i.val < 90
              ·
                exact finiteCheck_cover (lo := 89) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0089 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 90) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0090 i (by omega) (by omega)
            ·
              by_cases h92 : i.val < 92
              ·
                exact finiteCheck_cover (lo := 91) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0091 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 92) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0092 i (by omega) (by omega)
          ·
            by_cases h95 : i.val < 95
            ·
              by_cases h94 : i.val < 94
              ·
                exact finiteCheck_cover (lo := 93) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0093 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 94) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0094 i (by omega) (by omega)
            ·
              by_cases h96 : i.val < 96
              ·
                exact finiteCheck_cover (lo := 95) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0095 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 96) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0096 i (by omega) (by omega)
    ·
      by_cases h113 : i.val < 113
      ·
        by_cases h105 : i.val < 105
        ·
          by_cases h101 : i.val < 101
          ·
            by_cases h99 : i.val < 99
            ·
              by_cases h98 : i.val < 98
              ·
                exact finiteCheck_cover (lo := 97) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0097 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 98) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0098 i (by omega) (by omega)
            ·
              by_cases h100 : i.val < 100
              ·
                exact finiteCheck_cover (lo := 99) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0099 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 100) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0100 i (by omega) (by omega)
          ·
            by_cases h103 : i.val < 103
            ·
              by_cases h102 : i.val < 102
              ·
                exact finiteCheck_cover (lo := 101) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0101 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 102) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0102 i (by omega) (by omega)
            ·
              by_cases h104 : i.val < 104
              ·
                exact finiteCheck_cover (lo := 103) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0103 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 104) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0104 i (by omega) (by omega)
        ·
          by_cases h109 : i.val < 109
          ·
            by_cases h107 : i.val < 107
            ·
              by_cases h106 : i.val < 106
              ·
                exact finiteCheck_cover (lo := 105) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0105 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 106) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0106 i (by omega) (by omega)
            ·
              by_cases h108 : i.val < 108
              ·
                exact finiteCheck_cover (lo := 107) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0107 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 108) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0108 i (by omega) (by omega)
          ·
            by_cases h111 : i.val < 111
            ·
              by_cases h110 : i.val < 110
              ·
                exact finiteCheck_cover (lo := 109) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0109 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 110) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0110 i (by omega) (by omega)
            ·
              by_cases h112 : i.val < 112
              ·
                exact finiteCheck_cover (lo := 111) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0111 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 112) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0112 i (by omega) (by omega)
      ·
        by_cases h121 : i.val < 121
        ·
          by_cases h117 : i.val < 117
          ·
            by_cases h115 : i.val < 115
            ·
              by_cases h114 : i.val < 114
              ·
                exact finiteCheck_cover (lo := 113) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0113 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 114) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0114 i (by omega) (by omega)
            ·
              by_cases h116 : i.val < 116
              ·
                exact finiteCheck_cover (lo := 115) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0115 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 116) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0116 i (by omega) (by omega)
          ·
            by_cases h119 : i.val < 119
            ·
              by_cases h118 : i.val < 118
              ·
                exact finiteCheck_cover (lo := 117) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0117 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 118) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0118 i (by omega) (by omega)
            ·
              by_cases h120 : i.val < 120
              ·
                exact finiteCheck_cover (lo := 119) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0119 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 120) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0120 i (by omega) (by omega)
        ·
          by_cases h125 : i.val < 125
          ·
            by_cases h123 : i.val < 123
            ·
              by_cases h122 : i.val < 122
              ·
                exact finiteCheck_cover (lo := 121) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0121 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 122) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0122 i (by omega) (by omega)
            ·
              by_cases h124 : i.val < 124
              ·
                exact finiteCheck_cover (lo := 123) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0123 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 124) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0124 i (by omega) (by omega)
          ·
            by_cases h127 : i.val < 127
            ·
              by_cases h126 : i.val < 126
              ·
                exact finiteCheck_cover (lo := 125) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0125 i (by omega) (by omega)
              ·
                exact finiteCheck_cover (lo := 126) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0126 i (by omega) (by omega)
            ·
              by_cases h128 : i.val < 128
              ·
                exact finiteCheck_cover (lo := 127) (width := 1)
                  (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                          (cubeCodeVertices c).image (cubeVertex checkedIndex))
                  (by decide) codeFace_mask_part0127 i (by omega) (by omega)
              ·
                by_cases h129 : i.val < 129
                ·
                  exact finiteCheck_cover (lo := 128) (width := 1)
                    (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                            (cubeCodeVertices c).image (cubeVertex checkedIndex))
                    (by decide) codeFace_mask_part0128 i (by omega) (by omega)
                ·
                  exact finiteCheck_cover (lo := 129) (width := 1)
                    (P := fun checkedIndex : Fin 130 => ∀ c : Fin 27, faceMask (codeFace checkedIndex c) =
                            (cubeCodeVertices c).image (cubeVertex checkedIndex))
                    (by decide) codeFace_mask_part0129 i (by omega) (by omega)

theorem codeFace_top : ∀ f : Fin 130,
    faceMask (codeFace f 0) = facetLabels f := by
  intro f
  rw [codeFace_mask, cubeCodeVertices_zero, cubeVertex_image]

theorem codeFace_subset_facet : ∀ (f : Fin 130) (c : Fin 27),
    faceMask (codeFace f c) ⊆ facetLabels f := by
  intro f c
  rw [codeFace_mask, ← cubeVertex_image f]
  exact Finset.image_subset_image (Finset.subset_univ _)

theorem codeFace_le_iff : ∀ (f : Fin 130) (c d : Fin 27),
    faceMask (codeFace f c) ⊆ faceMask (codeFace f d) ↔ codeOfFin27 c ≤ codeOfFin27 d := by
  intro f c d
  rw [codeFace_mask, codeFace_mask,
    Finset.image_subset_image_iff (cubeVertex_injective f)]
  exact cubeCodeVertices_le_iff c d

theorem codeFace_injective : ∀ f : Fin 130, Function.Injective (codeFace f) := by
  intro f c d h
  apply codeOfFin27_bijective.1
  apply le_antisymm
  · apply (codeFace_le_iff f c d).mp
    intro v hv
    simpa only [h] using hv
  · apply (codeFace_le_iff f d c).mp
    intro v hv
    simpa only [h] using hv

end CubicalIndecomposability
