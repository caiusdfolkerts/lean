module

public import Unimodular.RankThreeGeometry
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.LinearAlgebra.Basis.SMul

@[expose] public section

/-! ## RankThreeRoots -/

namespace Unimodular.RankThree

open scoped BigOperators

/-- The six unoriented lines of the rank-three complete-graphic system, in a
fixed integral coordinate basis. -/
def baseRoot : Fin 6 → Lattice 3 :=
  ![![1, 0, 0],
    ![0, 1, 0],
    ![0, 0, 1],
    ![1, -1, 0],
    ![1, 0, -1],
    ![0, 1, -1]]

abbrev RootTag := Fin 6 × Bool

def root (r : RootTag) : Lattice 3 :=
  if r.2 then -baseRoot r.1 else baseRoot r.1

/-- An orientation value 0 selects only the positive root, 1 only the negative
root, and 2 both roots. Hence every one of the six lines occurs. -/
def selected (s : Fin 6 → Fin 3) (r : RootTag) : Bool :=
  if r.2 then decide (s r.1 ≠ 0) else decide (s r.1 ≠ 1)

def dot (h u : Lattice 3) : ℤ := ∑ i, h i * u i

/-- Integral supporting functionals for the square and diamond faces in the
rank-three obstruction. Their four root labels are recorded below. -/
def faceNormal : Fin 18 → Lattice 3 :=
  ![![0, 1, 1],
    ![1, 0, 1],
    ![1, 1, 0],
    ![1, 1, 2],
    ![1, 2, 1],
    ![2, 1, 1],
    ![-1, -1, 0],
    ![-1, 0, -1],
    ![-1, 0, 1],
    ![-1, 1, 0],
    ![0, -1, -1],
    ![0, -1, 1],
    ![0, 1, -1],
    ![1, -1, 0],
    ![1, 0, -1],
    ![-2, -1, -1],
    ![-1, -2, -1],
    ![-1, -1, -2]]

def faceRoot : Fin 18 → Fin 4 → RootTag :=
  ![![(1, false), (2, false), (3, true), (4, true)],
    ![(0, false), (2, false), (3, false), (5, true)],
    ![(0, false), (1, false), (4, false), (5, false)],
    ![(0, false), (1, false), (4, true), (5, true)],
    ![(0, false), (2, false), (5, false), (3, true)],
    ![(1, false), (2, false), (3, false), (4, false)],
    ![(0, true), (1, true), (4, true), (5, true)],
    ![(5, false), (0, true), (2, true), (3, true)],
    ![(2, false), (0, true), (3, true), (5, true)],
    ![(1, false), (5, false), (0, true), (4, true)],
    ![(3, false), (4, false), (1, true), (2, true)],
    ![(2, false), (3, false), (1, true), (4, true)],
    ![(1, false), (4, false), (2, true), (3, true)],
    ![(0, false), (4, false), (1, true), (5, true)],
    ![(0, false), (3, false), (5, false), (2, true)],
    ![(1, true), (2, true), (3, true), (4, true)],
    ![(3, false), (0, true), (2, true), (5, true)],
    ![(4, false), (5, false), (0, true), (1, true)]]

/-- Nonzero cut functionals, used for orientations that do not positively
span. There are only fourteen nontrivial directed cuts on four vertices. -/
def separator : Fin 14 → Lattice 3 :=
  ![![0, 0, 1],
    ![0, 1, 0],
    ![0, 1, 1],
    ![1, 0, 0],
    ![1, 0, 1],
    ![1, 1, 0],
    ![1, 1, 1],
    ![-1, -1, -1],
    ![-1, -1, 0],
    ![-1, 0, -1],
    ![-1, 0, 0],
    ![0, -1, -1],
    ![0, -1, 0],
    ![0, 0, -1]]

theorem root_injective : Function.Injective root := by decide

theorem root_ne_zero : ∀ r, root r ≠ 0 := by decide

theorem separator_ne_zero : ∀ i, separator i ≠ 0 := by decide

theorem faceRoot_injective : ∀ i, Function.Injective (fun j => root (faceRoot i j)) := by
  decide

theorem faceRoot_pairing : ∀ i j, dot (faceNormal i) (root (faceRoot i j)) = 1 := by
  decide

/- An exact finite lemma about all 729 possible orientations of the six lines.
It does not enumerate fans. Every orientation either has a nonzero separating
cut, or exposes four distinct rays on one support plane. The proof is ordinary
kernel reduction (`decide`), with no native-evaluation axiom. -/
section OrientationCertificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The first two coordinates partition the same exhaustive orientation
certificate into nine separately kernel-checked blocks. -/
private def orientationBlock (a b : Fin 3) : Prop :=
  ∀ c d e f : Fin 3,
    let s : Fin 6 → Fin 3 := ![a, b, c, d, e, f]
    (∃ i : Fin 14, ∀ r, selected s r → dot (separator i) (root r) ≤ 0) ∨
    (∃ i : Fin 18, (∀ r, selected s r → dot (faceNormal i) (root r) ≤ 1) ∧
      ∀ j, selected s (faceRoot i j))

/- The third coordinate splits each original 81-tuple block into three
closed 27-tuple certificates. The disjunction and all finite data are unchanged. -/
private def orientationBlockThird (a b c : Fin 3) : Prop :=
  ∀ d e f : Fin 3,
    let s : Fin 6 → Fin 3 := ![a, b, c, d, e, f]
    (∃ i : Fin 14, ∀ r, selected s r → dot (separator i) (root r) ≤ 0) ∨
    (∃ i : Fin 18, (∀ r, selected s r → dot (faceNormal i) (root r) ≤ 1) ∧
      ∀ j, selected s (faceRoot i j))

private theorem orientationBlockThird_000 :
    orientationBlockThird 0 0 0 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_001 :
    orientationBlockThird 0 0 1 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_002 :
    orientationBlockThird 0 0 2 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_010 :
    orientationBlockThird 0 1 0 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_011 :
    orientationBlockThird 0 1 1 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_012 :
    orientationBlockThird 0 1 2 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_020 :
    orientationBlockThird 0 2 0 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_021 :
    orientationBlockThird 0 2 1 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_022 :
    orientationBlockThird 0 2 2 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_100 :
    orientationBlockThird 1 0 0 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_101 :
    orientationBlockThird 1 0 1 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_102 :
    orientationBlockThird 1 0 2 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_110 :
    orientationBlockThird 1 1 0 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_111 :
    orientationBlockThird 1 1 1 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_112 :
    orientationBlockThird 1 1 2 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_120 :
    orientationBlockThird 1 2 0 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_121 :
    orientationBlockThird 1 2 1 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_122 :
    orientationBlockThird 1 2 2 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_200 :
    orientationBlockThird 2 0 0 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_201 :
    orientationBlockThird 2 0 1 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_202 :
    orientationBlockThird 2 0 2 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_210 :
    orientationBlockThird 2 1 0 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_211 :
    orientationBlockThird 2 1 1 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_212 :
    orientationBlockThird 2 1 2 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_220 :
    orientationBlockThird 2 2 0 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_221 :
    orientationBlockThird 2 2 1 := by
  unfold orientationBlockThird
  decide
private theorem orientationBlockThird_222 :
    orientationBlockThird 2 2 2 := by
  unfold orientationBlockThird
  decide

private theorem orientationBlock_00 : orientationBlock 0 0 := by
  unfold orientationBlock
  intro c
  fin_cases c
  · exact orientationBlockThird_000
  · exact orientationBlockThird_001
  · exact orientationBlockThird_002
private theorem orientationBlock_01 : orientationBlock 0 1 := by
  unfold orientationBlock
  intro c
  fin_cases c
  · exact orientationBlockThird_010
  · exact orientationBlockThird_011
  · exact orientationBlockThird_012
private theorem orientationBlock_02 : orientationBlock 0 2 := by
  unfold orientationBlock
  intro c
  fin_cases c
  · exact orientationBlockThird_020
  · exact orientationBlockThird_021
  · exact orientationBlockThird_022
private theorem orientationBlock_10 : orientationBlock 1 0 := by
  unfold orientationBlock
  intro c
  fin_cases c
  · exact orientationBlockThird_100
  · exact orientationBlockThird_101
  · exact orientationBlockThird_102
private theorem orientationBlock_11 : orientationBlock 1 1 := by
  unfold orientationBlock
  intro c
  fin_cases c
  · exact orientationBlockThird_110
  · exact orientationBlockThird_111
  · exact orientationBlockThird_112
private theorem orientationBlock_12 : orientationBlock 1 2 := by
  unfold orientationBlock
  intro c
  fin_cases c
  · exact orientationBlockThird_120
  · exact orientationBlockThird_121
  · exact orientationBlockThird_122
private theorem orientationBlock_20 : orientationBlock 2 0 := by
  unfold orientationBlock
  intro c
  fin_cases c
  · exact orientationBlockThird_200
  · exact orientationBlockThird_201
  · exact orientationBlockThird_202
private theorem orientationBlock_21 : orientationBlock 2 1 := by
  unfold orientationBlock
  intro c
  fin_cases c
  · exact orientationBlockThird_210
  · exact orientationBlockThird_211
  · exact orientationBlockThird_212
private theorem orientationBlock_22 : orientationBlock 2 2 := by
  unfold orientationBlock
  intro c
  fin_cases c
  · exact orientationBlockThird_220
  · exact orientationBlockThird_221
  · exact orientationBlockThird_222

private theorem oriented_roots_obstruction_six : ∀ a b c d e f : Fin 3,
    let s : Fin 6 → Fin 3 := ![a, b, c, d, e, f]
    (∃ i : Fin 14, ∀ r, selected s r → dot (separator i) (root r) ≤ 0) ∨
    (∃ i : Fin 18, (∀ r, selected s r → dot (faceNormal i) (root r) ≤ 1) ∧
      ∀ j, selected s (faceRoot i j)) := by
  intro a b
  fin_cases a <;> fin_cases b
  · exact orientationBlock_00
  · exact orientationBlock_01
  · exact orientationBlock_02
  · exact orientationBlock_10
  · exact orientationBlock_11
  · exact orientationBlock_12
  · exact orientationBlock_20
  · exact orientationBlock_21
  · exact orientationBlock_22

end OrientationCertificates

theorem oriented_roots_obstruction (s : Fin 6 → Fin 3) :
    (∃ i : Fin 14, ∀ r, selected s r → dot (separator i) (root r) ≤ 0) ∨
    (∃ i : Fin 18, (∀ r, selected s r → dot (faceNormal i) (root r) ≤ 1) ∧
      ∀ j, selected s (faceRoot i j)) := by
  have he : ![s 0, s 1, s 2, s 3, s 4, s 5] = s := by
    ext i
    fin_cases i <;> rfl
  exact he ▸ oriented_roots_obstruction_six (s 0) (s 1) (s 2) (s 3) (s 4) (s 5)

end Unimodular.RankThree

/-! ## RankThree -/

noncomputable section

namespace Unimodular.RankThree

open scoped BigOperators

/-- Integer dot products are exactly the lattice pairings in the real ambient space. -/
theorem pairing_embed (h u : Lattice 3) : pairing (embed h) u = (dot h u : ℤ) := by
  simp [pairing, embed, dot, Int.cast_sum, Int.cast_mul]

theorem embed_ne_zero {u : Lattice 3} (hu : u ≠ 0) : embed u ≠ 0 := by
  intro h
  apply hu
  ext i
  have hi : (u i : ℝ) = 0 := congrFun h i
  exact_mod_cast hi

/-- No complete positive-coordinate fan exists on a subset of the twelve signed
A3 roots that uses every one of the six unoriented lines. The conclusion is about
actual complete lattice fans and their coordinate criterion; the finite lemma only
supplies a separating cut or a genuine four-ray exposed face. -/
theorem no_positiveCriterion_of_root_system
    (fan : SmoothCompleteFan 3) (hfan : fan.PositiveCoordinateCriterion)
    (hlines : ∀ i, baseRoot i ∈ fan.rays ∨ -baseRoot i ∈ fan.rays)
    (hrays : ∀ u ∈ fan.rays, ∃ r, root r = u) : False := by
  classical
  let s : Fin 6 → Fin 3 := fun i =>
    if baseRoot i ∈ fan.rays then (if -baseRoot i ∈ fan.rays then 2 else 0) else 1
  have hs (r : RootTag) : selected s r ↔ root r ∈ fan.rays := by
    obtain ⟨i, e⟩ := r
    have hi := hlines i
    cases e <;> by_cases hp : baseRoot i ∈ fan.rays <;>
      by_cases hn : -baseRoot i ∈ fan.rays <;> simp_all [s, selected, root]
  rcases oriented_roots_obstruction s with hsep | hface
  · obtain ⟨i, hi⟩ := hsep
    apply fan.no_separating_functional (embed (separator i)) _
      (embed_ne_zero (separator_ne_zero i))
    intro u hu
    obtain ⟨r, rfl⟩ := hrays u hu
    rw [pairing_embed]
    exact_mod_cast hi r ((hs r).2 hu)
  · obtain ⟨i, hi, hselected⟩ := hface
    have hc := fan.support_rays_card_le hfan (fun j => root (faceRoot i j))
      (fun j => (hs _).1 (hselected j)) (faceRoot_injective i)
      (embed (faceNormal i))
      (by
        intro u hu
        obtain ⟨r, rfl⟩ := hrays u hu
        rw [pairing_embed]
        exact_mod_cast hi r ((hs r).2 hu))
      (by intro j; rw [pairing_embed, faceRoot_pairing]; norm_num)
    norm_num at hc

/-- The absolute determinant of every three primitive rays is at most one. -/
theorem ray_det_bound (fan : SmoothCompleteFan 3) (hfan : fan.PositiveCoordinateCriterion)
    (u v w : Lattice 3) (hu : u ∈ fan.rays) (hv : v ∈ fan.rays) (hw : w ∈ fan.rays) :
    |(Matrix.of ![u, v, w]).det| ≤ 1 := by
  have hU := fan.uniformlyUnimodular_of_positiveCoordinateCriterion hfan
  have h := hU ![⟨u, hu⟩, ⟨v, hv⟩, ⟨w, hw⟩]
  have hvec : (fun i : Fin 3 =>
      (![⟨u, hu⟩, ⟨v, hv⟩, ⟨w, hw⟩] i : fan.rays).val) = ![u, v, w] := by
    funext i
    fin_cases i <;> rfl
  change |(Pi.basisFun ℤ (Fin 3)).det
    (fun i => (![⟨u, hu⟩, ⟨v, hv⟩, ⟨w, hw⟩] i : fan.rays).val)| ≤ 1 at h
  rw [hvec] at h
  have heq : (Pi.basisFun ℤ (Fin 3)).det ![u, v, w] =
      (Matrix.of ![u, v, w]).det := by
    rw [Module.Basis.det_apply, ← Matrix.det_transpose]
    congr 1 <;> ext i j <;> simp [Module.Basis.toMatrix_apply]
  rwa [heq] at h

/-- Sign choices on the two specified lines do not change an absolute minor. -/
theorem signed_ray_det_bound (fan : SmoothCompleteFan 3)
    (hfan : fan.PositiveCoordinateCriterion) (u v w : Lattice 3)
    (hu : u ∈ fan.rays) (hv : v ∈ fan.rays ∨ -v ∈ fan.rays)
    (hw : w ∈ fan.rays ∨ -w ∈ fan.rays) : |(Matrix.of ![u, v, w]).det| ≤ 1 := by
  have hn₂ : (Matrix.of ![u, -v, w]).det = -(Matrix.of ![u, v, w]).det := by
    simp [Matrix.det_fin_three] <;> ring
  have hn₃ : (Matrix.of ![u, v, -w]).det = -(Matrix.of ![u, v, w]).det := by
    simp [Matrix.det_fin_three] <;> ring
  have hn₂₃ : (Matrix.of ![u, -v, -w]).det = (Matrix.of ![u, v, w]).det := by
    simp [Matrix.det_fin_three] <;> ring
  rcases hv with hv | hv <;> rcases hw with hw | hw
  · exact ray_det_bound fan hfan u v w hu hv hw
  · simpa only [hn₃, abs_neg] using ray_det_bound fan hfan u v (-w) hu hv hw
  · simpa only [hn₂, abs_neg] using ray_det_bound fan hfan u (-v) w hu hv hw
  · simpa only [hn₂₃] using ray_det_bound fan hfan u (-v) (-w) hu hv hw

set_option maxHeartbeats 1000000 in
/-- Any further unimodular ray in a rank-three configuration already containing
all six A3 lines lies on one of those same lines. This is the determinant step at
the beginning of Lemma 6.5, with arbitrary additional rays allowed. -/
theorem every_ray_is_root (fan : SmoothCompleteFan 3)
    (hfan : fan.PositiveCoordinateCriterion)
    (hlines : ∀ i, baseRoot i ∈ fan.rays ∨ -baseRoot i ∈ fan.rays)
    (u : Lattice 3) (hu : u ∈ fan.rays) : ∃ r, root r = u := by
  have minor (i j : Fin 6) := signed_ray_det_bound fan hfan u
    (baseRoot i) (baseRoot j) hu (hlines i) (hlines j)
  have h₀ : |u 0| ≤ 1 := by simpa [baseRoot, Matrix.det_fin_three] using minor 1 2
  have h₁ : |u 1| ≤ 1 := by simpa [baseRoot, Matrix.det_fin_three, abs_neg] using minor 0 2
  have h₂ : |u 2| ≤ 1 := by simpa [baseRoot, Matrix.det_fin_three] using minor 0 1
  have h₀₁ : |u 0 + u 1| ≤ 1 := by
    have h : |-u 0 - u 1| ≤ 1 := by
      simpa [baseRoot, Matrix.det_fin_three] using minor 3 2
    have hh := abs_le.mp h
    exact abs_le.mpr (by constructor <;> omega)
  have h₀₂ : |u 0 + u 2| ≤ 1 := by
    simpa [baseRoot, Matrix.det_fin_three] using minor 4 1
  have h₁₂ : |u 1 + u 2| ≤ 1 := by
    have h : |-u 1 - u 2| ≤ 1 := by
      simpa [baseRoot, Matrix.det_fin_three] using minor 5 0
    have hh := abs_le.mp h
    exact abs_le.mpr (by constructor <;> omega)
  have hne : u ≠ 0 := by
    obtain ⟨b, hb, i, rfl⟩ := hu
    exact b.ne_zero i
  have hcoords : u 0 ≠ 0 ∨ u 1 ≠ 0 ∨ u 2 ≠ 0 := by
    by_contra! hzero
    apply hne
    ext i
    fin_cases i <;> simp_all
  have bounds := abs_le.1 h₀
  have bounds' := abs_le.1 h₁
  have bounds'' := abs_le.1 h₂
  have sums := abs_le.1 h₀₁
  have sums' := abs_le.1 h₀₂
  have sums'' := abs_le.1 h₁₂
  have hc :
      (u 0 = 1 ∧ u 1 = 0 ∧ u 2 = 0) ∨
      (u 0 = 0 ∧ u 1 = 1 ∧ u 2 = 0) ∨
      (u 0 = 0 ∧ u 1 = 0 ∧ u 2 = 1) ∨
      (u 0 = 1 ∧ u 1 = -1 ∧ u 2 = 0) ∨
      (u 0 = 1 ∧ u 1 = 0 ∧ u 2 = -1) ∨
      (u 0 = 0 ∧ u 1 = 1 ∧ u 2 = -1) ∨
      (u 0 = -1 ∧ u 1 = 0 ∧ u 2 = 0) ∨
      (u 0 = 0 ∧ u 1 = -1 ∧ u 2 = 0) ∨
      (u 0 = 0 ∧ u 1 = 0 ∧ u 2 = -1) ∨
      (u 0 = -1 ∧ u 1 = 1 ∧ u 2 = 0) ∨
      (u 0 = -1 ∧ u 1 = 0 ∧ u 2 = 1) ∨
      (u 0 = 0 ∧ u 1 = -1 ∧ u 2 = 1) := by
    rcases bounds with ⟨h0lo, h0hi⟩
    rcases bounds' with ⟨h1lo, h1hi⟩
    rcases bounds'' with ⟨h2lo, h2hi⟩
    generalize hu0 : u 0 = x0 at *
    generalize hu1 : u 1 = x1 at *
    generalize hu2 : u 2 = x2 at *
    interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> omega
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h
  · refine ⟨(0, false), ?_⟩; ext i; fin_cases i <;> simp_all [root, baseRoot]
  · refine ⟨(1, false), ?_⟩; ext i; fin_cases i <;> simp_all [root, baseRoot]
  · refine ⟨(2, false), ?_⟩; ext i; fin_cases i <;> simp_all [root, baseRoot]
  · refine ⟨(3, false), ?_⟩; ext i; fin_cases i <;> simp_all [root, baseRoot]
  · refine ⟨(4, false), ?_⟩; ext i; fin_cases i <;> simp_all [root, baseRoot]
  · refine ⟨(5, false), ?_⟩; ext i; fin_cases i <;> simp_all [root, baseRoot]
  · refine ⟨(0, true), ?_⟩; ext i; fin_cases i <;> simp_all [root, baseRoot]
  · refine ⟨(1, true), ?_⟩; ext i; fin_cases i <;> simp_all [root, baseRoot]
  · refine ⟨(2, true), ?_⟩; ext i; fin_cases i <;> simp_all [root, baseRoot]
  · refine ⟨(3, true), ?_⟩; ext i; fin_cases i <;> simp_all [root, baseRoot]
  · refine ⟨(4, true), ?_⟩; ext i; fin_cases i <;> simp_all [root, baseRoot]
  · refine ⟨(5, true), ?_⟩; ext i; fin_cases i <;> simp_all [root, baseRoot]

/-- The rank-three K4 obstruction in its integral normal form: a complete smooth
fan satisfying the corner criterion cannot contain the six complete-graphic lines.
No restriction is placed on the other rays; they are proved to be A3 roots. -/
theorem no_normalized_K4_restriction (fan : SmoothCompleteFan 3)
    (hfan : fan.PositiveCoordinateCriterion)
    (hlines : ∀ i, baseRoot i ∈ fan.rays ∨ -baseRoot i ∈ fan.rays) : False :=
  no_positiveCriterion_of_root_system fan hfan hlines
    (every_ray_is_root fan hfan hlines)

end Unimodular.RankThree

/-! ## RankThreeTransport -/

noncomputable section

namespace Unimodular

open scoped BigOperators

variable {n : ℕ}

/-- Real coordinates in an integral basis, as an actual real linear equivalence. -/
def realCoordinateEquiv (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    Ambient n ≃ₗ[ℝ] Ambient n :=
  LinearEquiv.ofBijective (realCoordinates b) (by
    have hs : Function.Surjective (realCoordinates b) := fun c =>
      ⟨∑ i, c i • embed (b i), realCoordinates_sum_basis b c⟩
    exact ⟨LinearMap.injective_iff_surjective.mpr hs, hs⟩)

@[simp] theorem realCoordinateEquiv_embed
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (u : Lattice n) :
    realCoordinateEquiv b (embed u) = embed (b.equivFun u) := by
  ext i
  exact realCoordinates_embed b u i

section Transport

variable (e : Lattice n ≃ₗ[ℤ] Lattice n) (f : Ambient n ≃ₗ[ℝ] Ambient n)
    (hcompat : ∀ u, f (embed u) = embed (e u))

include hcompat

/-- The coordinate change sends the entire nonnegative cone, not just its rays. -/
theorem basisCone_map_iff (b : Module.Basis (Fin n) ℤ (Lattice n)) (x : Ambient n) :
    x ∈ basisCone (b.map e) ↔ f.symm x ∈ basisCone b := by
  constructor
  · rintro ⟨c, hc, he⟩
    refine ⟨c, hc, ?_⟩
    apply f.injective
    simpa only [map_sum, map_smul, hcompat, Module.Basis.map_apply,
      f.apply_symm_apply] using he
  · rintro ⟨c, hc, he⟩
    refine ⟨c, hc, ?_⟩
    have hh := congrArg f he
    simpa only [map_sum, map_smul, hcompat, Module.Basis.map_apply,
      f.apply_symm_apply] using hh

/-- Coordinate transport also respects every indexed face. -/
theorem basisFace_map_iff (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (x : Ambient n) :
    x ∈ basisFace (b.map e) I ↔ f.symm x ∈ basisFace b I := by
  constructor
  · rintro ⟨c, hc, hz, he⟩
    refine ⟨c, hc, hz, ?_⟩
    apply f.injective
    simpa only [map_sum, map_smul, hcompat, Module.Basis.map_apply,
      f.apply_symm_apply] using he
  · rintro ⟨c, hc, hz, he⟩
    refine ⟨c, hc, hz, ?_⟩
    have hh := congrArg f he
    simpa only [map_sum, map_smul, hcompat, Module.Basis.map_apply,
      f.apply_symm_apply] using hh

namespace SmoothCompleteFan

attribute [local instance] Classical.propDecidable

/-- Transport an actual smooth complete fan through compatible integral and real
linear equivalences. Face-to-face intersections and completeness are transported. -/
def mapEquiv (fan : SmoothCompleteFan n) : SmoothCompleteFan n where
  maximal := fan.maximal.image (fun b => b.map e)
  complete x := by
    obtain ⟨b, hb, hx⟩ := fan.complete (f.symm x)
    exact ⟨b.map e, Finset.mem_image.2 ⟨b, hb, rfl⟩,
      (basisCone_map_iff e f hcompat b x).2 hx⟩
  intersection := by
    intro b hb c hc
    obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨I, J, hI, hJ⟩ := fan.intersection b₀ hb₀ c₀ hc₀
    refine ⟨I, J, ?_, ?_⟩
    · ext x
      change (x ∈ basisCone (b₀.map e) ∧ x ∈ basisCone (c₀.map e)) ↔ _
      rw [basisCone_map_iff e f hcompat, basisCone_map_iff e f hcompat,
        basisFace_map_iff e f hcompat]
      exact Set.ext_iff.1 hI (f.symm x)
    · ext x
      change (x ∈ basisCone (b₀.map e) ∧ x ∈ basisCone (c₀.map e)) ↔ _
      rw [basisCone_map_iff e f hcompat, basisCone_map_iff e f hcompat,
        basisFace_map_iff e f hcompat]
      exact Set.ext_iff.1 hJ (f.symm x)

theorem mem_rays_mapEquiv (fan : SmoothCompleteFan n) (u : Lattice n) :
    u ∈ (fan.mapEquiv e f hcompat).rays ↔ e.symm u ∈ fan.rays := by
  constructor
  · rintro ⟨b, hb, i, he⟩
    obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.1 hb
    refine ⟨b₀, hb₀, i, ?_⟩
    have h := congrArg e.symm he
    simpa only [Module.Basis.map_apply, e.symm_apply_apply] using h
  · rintro ⟨b, hb, i, he⟩
    refine ⟨b.map e, Finset.mem_image.2 ⟨b, hb, rfl⟩, i, ?_⟩
    simp only [Module.Basis.map_apply, he, e.apply_symm_apply]

theorem positiveCriterion_mapEquiv (fan : SmoothCompleteFan n)
    (hfan : fan.PositiveCoordinateCriterion) :
    (fan.mapEquiv e f hcompat).PositiveCoordinateCriterion := by
  intro b hb u hu
  obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.1 hb
  have hv := (mem_rays_mapEquiv e f hcompat fan u).1 hu
  exact hfan b₀ hb₀ (e.symm u) hv

end SmoothCompleteFan
end Transport

namespace RankThree

/-- Integral normalization in an arbitrary lattice basis. The six displayed
complete-graphic lines are forbidden in every integral coordinate system, and
all unlisted rays are allowed. -/
theorem no_K4_lines_in_basis (fan : SmoothCompleteFan 3)
    (hfan : fan.PositiveCoordinateCriterion)
    (b : Module.Basis (Fin 3) ℤ (Lattice 3))
    (hlines : ∀ i, b.equivFun.symm (baseRoot i) ∈ fan.rays ∨
      -b.equivFun.symm (baseRoot i) ∈ fan.rays) : False := by
  let Ψ := fan.mapEquiv b.equivFun (realCoordinateEquiv b) (realCoordinateEquiv_embed b)
  have hΨ := fan.positiveCriterion_mapEquiv b.equivFun (realCoordinateEquiv b)
    (realCoordinateEquiv_embed b) hfan
  apply no_normalized_K4_restriction Ψ hΨ
  intro i
  have hm (u : Lattice 3) : u ∈ Ψ.rays ↔ b.equivFun.symm u ∈ fan.rays :=
    fan.mem_rays_mapEquiv b.equivFun (realCoordinateEquiv b) (realCoordinateEquiv_embed b) u
  rcases hlines i with hi | hi
  · exact Or.inl ((hm _).2 hi)
  · apply Or.inr
    apply (hm _).2
    simpa using hi

end RankThree
end Unimodular

/-! ## RankThreeNormalization -/

namespace Unimodular.RankThree

open scoped BigOperators

def signUnit (s : Bool) : ℤˣ := if s then -1 else 1

def signedColumns (s : Fin 6 → Bool) : Fin 6 → Lattice 3 :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1],
    ![(signUnit (s 0) : ℤ), (signUnit (s 1) : ℤ), 0],
    ![(signUnit (s 2) : ℤ), 0, (signUnit (s 3) : ℤ)],
    ![0, (signUnit (s 4) : ℤ), (signUnit (s 5) : ℤ)]]

def reorientation (s : Fin 6 → Bool) : Fin 3 → ℤˣ :=
  ![1, -(signUnit (s 0) * signUnit (s 1)), -(signUnit (s 2) * signUnit (s 3))]

/- The only sign compatibility required to normalize a rank-three K4 matrix
is the dependence of its three nonbasis columns. This checks all 64 sign choices
by kernel reduction and records the actual diagonal basis reorientation. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem signs_normalize : ∀ s : Fin 6 → Bool,
    (Matrix.of ![signedColumns s 3, signedColumns s 4, signedColumns s 5]).det = 0 →
    ∀ i,
      (fun j => (reorientation s j : ℤ) * baseRoot i j) = signedColumns s i ∨
      -(fun j => (reorientation s j : ℤ) * baseRoot i j) = signedColumns s i := by
  decide

noncomputable section

/-- The basis determinant is the ordinary determinant of the coordinate rows. -/
theorem det_eq_coordinate_rows {N : Type*} [AddCommGroup N] [Module ℤ N]
    (b : Module.Basis (Fin 3) ℤ N) (u : Fin 3 → N) :
    b.det u = (Matrix.of (fun i => b.equivFun (u i))).det := by
  rw [Module.Basis.det_apply, ← Matrix.det_transpose]
  congr 1

/-- Uniform unimodularity does not depend on the integral basis used to compute
maximal minors. The proof uses the actual unit transition determinant. -/
theorem uniform_in_basis {E : Type*} (U : E → Lattice 3)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin 3)) U)
    (b : Module.Basis (Fin 3) ℤ (Lattice 3)) : IntegralRigidity.Uniform b U := by
  intro a
  have h := hU a
  have he := congrArg (fun f => f (U ∘ a))
    ((Pi.basisFun ℤ (Fin 3)).det.eq_smul_basis_det b)
  have hb : |(Pi.basisFun ℤ (Fin 3)).det b| = 1 :=
    Int.isUnit_iff_abs_eq.mp ((Pi.basisFun ℤ (Fin 3)).isUnit_det b)
  change (Pi.basisFun ℤ (Fin 3)).det (U ∘ a) =
    (Pi.basisFun ℤ (Fin 3)).det b * b.det (U ∘ a) at he
  rw [he, abs_mul, hb, one_mul] at h
  exact h

/-- A uniformly unimodular rank-three representation with the same dependent
triples as the six K4 incidence columns is integrally equivalent to those six
lines, with independent choices of signs retained. This proves the normalization
used in the rank-three obstruction from actual determinant data. -/
theorem integral_K4_normal_form (U : Fin 6 → Lattice 3)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin 3)) U)
    (hpattern : ∀ a : Fin 3 → Fin 6,
      (Pi.basisFun ℤ (Fin 3)).det (U ∘ a) = 0 ↔
        (Pi.basisFun ℤ (Fin 3)).det (baseRoot ∘ a) = 0) :
    ∃ b : Module.Basis (Fin 3) ℤ (Lattice 3),
      ∀ i, b.equivFun.symm (baseRoot i) = U i ∨
        -b.equivFun.symm (baseRoot i) = U i := by
  let a : Fin 3 → Fin 6 := ![0, 1, 2]
  have hd : (Pi.basisFun ℤ (Fin 3)).det (U ∘ a) ≠ 0 := by
    intro h
    have hc := (hpattern a).1 h
    rw [det_eq_coordinate_rows] at hc
    norm_num [a, Pi.basisFun_equivFun, Function.comp_def, baseRoot,
      Matrix.det_fin_three] at hc
  have hu : IsUnit ((Pi.basisFun ℤ (Fin 3)).det (U ∘ a)) := by
    apply Int.isUnit_iff_abs_eq.mpr
    have hb := hU a
    have hp := abs_pos.mpr hd
    omega
  have hbase := (Pi.basisFun ℤ (Fin 3)).is_basis_iff_det.mpr hu
  let b := Module.Basis.mk hbase.1 hbase.2.ge
  have hb (i : Fin 3) : b i = U (a i) := Module.Basis.mk_apply _ _ i
  have hUb := uniform_in_basis U hU b
  let v : Fin 6 → Lattice 3 := fun i => b.equivFun (U i)
  have hcoords (j : Fin 6) (i : Fin 3) : |v j i| ≤ 1 := by
    have hf : U ∘ Function.update a i j = Function.update b i (U j) := by
      ext k
      by_cases hki : k = i
      · subst k
        simp
      · simp [Function.comp_def, hki, hb]
    have hh := hUb (Function.update a i j)
    rw [hf, IntegralRigidity.det_replace_basis] at hh
    exact hh
  have hv₀ : v 0 = ![1, 0, 0] := by
    have hh := congrArg b.equivFun (hb 0)
    ext j
    have h := congrFun hh j
    fin_cases j <;> simpa [a, v] using h.symm
  have hv₁ : v 1 = ![0, 1, 0] := by
    have hh := congrArg b.equivFun (hb 1)
    ext j
    have h := congrFun hh j
    fin_cases j <;> simpa [a, v] using h.symm
  have hv₂ : v 2 = ![0, 0, 1] := by
    have hh := congrArg b.equivFun (hb 2)
    ext j
    have h := congrFun hh j
    fin_cases j <;> simpa [a, v] using h.symm
  have hp (c : Fin 3 → Fin 6) :
      (Matrix.of (v ∘ c)).det = 0 ↔ (Matrix.of (baseRoot ∘ c)).det = 0 := by
    have he := congrArg (fun f => f (U ∘ c))
      ((Pi.basisFun ℤ (Fin 3)).det.eq_smul_basis_det b)
    change (Pi.basisFun ℤ (Fin 3)).det (U ∘ c) =
      (Pi.basisFun ℤ (Fin 3)).det b * b.det (U ∘ c) at he
    have hbn : (Pi.basisFun ℤ (Fin 3)).det b ≠ 0 :=
      ((Pi.basisFun ℤ (Fin 3)).isUnit_det b).ne_zero
    have ht := hpattern c
    rw [he, mul_eq_zero, or_iff_right hbn, det_eq_coordinate_rows,
      Pi.basisFun_det_apply] at ht
    exact ht
  have h₃₂ : v 3 2 = 0 := by
    have hh := hp ![0, 1, 3]
    simpa [Function.comp_def, Matrix.det_fin_three, hv₀, hv₁, baseRoot] using hh.mpr (by decide)
  have h₄₁ : v 4 1 = 0 := by
    have hh := hp ![0, 2, 4]
    simpa [Function.comp_def, Matrix.det_fin_three, hv₀, hv₂, baseRoot] using hh.mpr (by decide)
  have h₅₀ : v 5 0 = 0 := by
    have hh := hp ![1, 2, 5]
    simpa [Function.comp_def, Matrix.det_fin_three, hv₁, hv₂, baseRoot] using hh.mpr (by decide)
  have h₃₀ : v 3 0 ≠ 0 := by
    have hh := not_congr (hp ![1, 2, 3])
    simpa [Function.comp_def, Matrix.det_fin_three, hv₁, hv₂, baseRoot] using hh.mpr (by decide)
  have h₃₁ : v 3 1 ≠ 0 := by
    have hh := not_congr (hp ![0, 2, 3])
    simpa [Function.comp_def, Matrix.det_fin_three, hv₀, hv₂, baseRoot] using hh.mpr (by decide)
  have h₄₀ : v 4 0 ≠ 0 := by
    have hh := not_congr (hp ![1, 2, 4])
    simpa [Function.comp_def, Matrix.det_fin_three, hv₁, hv₂, baseRoot] using hh.mpr (by decide)
  have h₄₂ : v 4 2 ≠ 0 := by
    have hh := not_congr (hp ![0, 1, 4])
    simpa [Function.comp_def, Matrix.det_fin_three, hv₀, hv₁, baseRoot] using hh.mpr (by decide)
  have h₅₁ : v 5 1 ≠ 0 := by
    have hh := not_congr (hp ![0, 2, 5])
    simpa [Function.comp_def, Matrix.det_fin_three, hv₀, hv₂, baseRoot] using hh.mpr (by decide)
  have h₅₂ : v 5 2 ≠ 0 := by
    have hh := not_congr (hp ![0, 1, 5])
    simpa [Function.comp_def, Matrix.det_fin_three, hv₀, hv₁, baseRoot] using hh.mpr (by decide)
  let coeff : Fin 6 → ℤ := ![v 3 0, v 3 1, v 4 0, v 4 2, v 5 1, v 5 2]
  have hc (i : Fin 6) : coeff i = -1 ∨ coeff i = 1 := by
    have h30 := abs_le.1 (hcoords 3 0)
    have h31 := abs_le.1 (hcoords 3 1)
    have h40 := abs_le.1 (hcoords 4 0)
    have h42 := abs_le.1 (hcoords 4 2)
    have h51 := abs_le.1 (hcoords 5 1)
    have h52 := abs_le.1 (hcoords 5 2)
    fin_cases i <;> simp [coeff] <;> omega
  let s : Fin 6 → Bool := fun i => decide (coeff i = -1)
  have hs (i : Fin 6) : (signUnit (s i) : ℤ) = coeff i := by
    rcases hc i with hi | hi <;> simp [signUnit, s, hi]
  have hv : signedColumns s = v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [signedColumns, hs, coeff, hv₀, hv₁, hv₂, h₃₂, h₄₁, h₅₀]
  have hedge : (Matrix.of ![signedColumns s 3, signedColumns s 4, signedColumns s 5]).det = 0 := by
    have hh := (hp ![3, 4, 5]).mpr (by decide)
    simpa [hv, Function.comp_def, Matrix.det_fin_three] using hh
  let b' := b.unitsSMul (reorientation s)
  have hchange (x : Lattice 3) : b.equivFun (b'.equivFun.symm x) =
      fun j => (reorientation s j : ℤ) * x j := by
    rw [Module.Basis.equivFun_symm_apply]
    simp only [b', Module.Basis.unitsSMul_apply, Units.smul_def, map_sum, map_smul]
    ext j
    simp [Finset.sum_apply, Pi.smul_apply, Module.Basis.equivFun_apply,
      Module.Basis.repr_self_apply, Finsupp.single_apply, smul_eq_mul, mul_comm]
  refine ⟨b', fun i => ?_⟩
  rcases signs_normalize s hedge i with hi | hi
  · apply Or.inl
    apply b.equivFun.injective
    rw [hchange]
    simpa [hv, v] using hi
  · apply Or.inr
    apply b.equivFun.injective
    rw [map_neg, hchange]
    simpa [hv, v] using hi

/-- A complete positive-coordinate fan cannot have a six-ray restriction whose
linear dependence pattern is that of K4. Integral normalization is proved above,
not assumed as an extra hypothesis. -/
theorem no_K4_dependence_pattern (fan : SmoothCompleteFan 3)
    (hfan : fan.PositiveCoordinateCriterion) (U : Fin 6 → Lattice 3)
    (hrays : ∀ i, U i ∈ fan.rays)
    (hpattern : ∀ a : Fin 3 → Fin 6,
      (Pi.basisFun ℤ (Fin 3)).det (U ∘ a) = 0 ↔
        (Pi.basisFun ℤ (Fin 3)).det (baseRoot ∘ a) = 0) : False := by
  have hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin 3)) U := by
    intro a
    exact fan.uniformlyUnimodular_of_positiveCoordinateCriterion hfan
      (fun i => ⟨U (a i), hrays (a i)⟩)
  obtain ⟨b, hb⟩ := integral_K4_normal_form U hU hpattern
  apply no_K4_lines_in_basis fan hfan b
  intro i
  rcases hb i with hi | hi
  · exact Or.inl (hi.symm ▸ hrays i)
  · exact Or.inr (hi.symm ▸ hrays i)

end
end Unimodular.RankThree

#print axioms Unimodular.RankThree.oriented_roots_obstruction
#print axioms Unimodular.RankThree.no_normalized_K4_restriction
#print axioms Unimodular.RankThree.no_K4_lines_in_basis
#print axioms Unimodular.RankThree.integral_K4_normal_form
#print axioms Unimodular.RankThree.no_K4_dependence_pattern
