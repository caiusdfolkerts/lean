module

public import Unimodular.RankThree
public import Unimodular.HellerCoordinates

@[expose] public section

/-!
# Integral bridges for fundamental-graph pruning

Equal supports are not treated as equal integer vectors. The two-by-two minor
bounds prove the necessary common sign. The domino calculation is an exact
six-column lemma, to be combined with the arbitrary-rank quotient construction.
-/

namespace Unimodular.SeriesParallel

open scoped BigOperators

/-- Two ternary integer vectors with the same support and bounded two-by-two
minors agree up to one global sign. -/
theorem signed_eq_of_same_support {I : Type*} (x y : I → ℤ)
    (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1)
    (hs : ∀ i, x i = 0 ↔ y i = 0)
    (hminor : ∀ i j, |x i * y j - x j * y i| ≤ 1) :
    x = y ∨ x = -y := by
  classical
  by_cases hx0 : x = 0
  · left
    have hy0 : y = 0 := by
      funext i
      exact (hs i).mp (congrFun hx0 i)
    exact hx0.trans hy0.symm
  have hxi : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (funext h)
  obtain ⟨i, hi⟩ := hxi
  have hiy : y i ≠ 0 := fun h => hi ((hs i).mpr h)
  have hix : x i = 1 ∨ x i = -1 := by
    have := abs_le.mp (hx i)
    omega
  have hiy' : y i = 1 ∨ y i = -1 := by
    have := abs_le.mp (hy i)
    omega
  have hrelation : ∀ j, x i * y j - x j * y i = 0 := by
    intro j
    by_cases hj : x j = 0
    · simp [hj, (hs j).mp hj]
    have hjy : y j ≠ 0 := fun h => hj ((hs j).mpr h)
    have hjx : x j = 1 ∨ x j = -1 := by
      have := abs_le.mp (hx j)
      omega
    have hjy' : y j = 1 ∨ y j = -1 := by
      have := abs_le.mp (hy j)
      omega
    have hm := hminor i j
    rcases hix with hix | hix <;> rcases hiy' with hiy' | hiy' <;>
      rcases hjx with hjx | hjx <;> rcases hjy' with hjy' | hjy' <;>
      norm_num [hix, hiy', hjx, hjy'] at hm <;>
      norm_num [hix, hiy', hjx, hjy']
  rcases hix with hix | hix <;> rcases hiy' with hiy' | hiy'
  · left
    funext j
    have := hrelation j
    simp only [hix, hiy', one_mul, mul_one] at this
    omega
  · right
    funext j
    have := hrelation j
    simp only [Pi.neg_apply]
    simp only [hix, hiy', one_mul, mul_neg_one] at this
    omega
  · right
    funext j
    have := hrelation j
    simp only [Pi.neg_apply]
    simp only [hix, hiy', neg_one_mul, mul_one] at this
    omega
  · left
    funext j
    have := hrelation j
    simp only [hix, hiy', neg_one_mul, mul_neg_one] at this
    omega

/-- Consequently column twins in an integral fundamental graph are actual
parallel vectors, including their coherent global sign. -/
theorem column_twins_are_signed {I M : Type*} [Fintype I] [DecidableEq I]
    [AddCommGroup M] [Module ℤ M]
    (b : Module.Basis I ℤ M) (U : Set M)
    (hU : IntegralRigidity.Uniform b (fun u : U => u.val))
    (hb : ∀ i, b i ∈ U) {x y : M} (hx : x ∈ U) (hy : y ∈ U)
    (hs : ∀ i, b.repr x i = 0 ↔ b.repr y i = 0) : x = y ∨ x = -y := by
  have hm : ∀ i j,
      |b.repr x i * b.repr y j - b.repr x j * b.repr y i| ≤ 1 := by
    intro i j
    by_cases hij : i = j
    · simp [hij]
    · exact Heller.two_coordinate_minor_abs_le_one b U hU hb hx hy hij
  rcases signed_eq_of_same_support (fun i => b.repr x i) (fun i => b.repr y i)
    (Heller.coordinate_abs_le_one b U hU hb hx)
    (Heller.coordinate_abs_le_one b U hU hb hy) hs hm with h | h
  · left
    apply b.repr.injective
    exact Finsupp.ext (congrFun h)
  · right
    apply b.repr.injective
    ext i
    simpa using congrFun h i

/-- The transposed statement gives the coherent row sign required by a series
extension. This applies to any chosen family of nonbasis columns. -/
theorem row_twins_are_signed {I J : Type*} (A : I → J → ℤ)
    (hentry : ∀ i j, |A i j| ≤ 1)
    (hminor : ∀ i i' j j', |A i j * A i' j' - A i j' * A i' j| ≤ 1)
    {i i' : I} (hs : ∀ j, A i j = 0 ↔ A i' j = 0) :
    A i = A i' ∨ A i = -A i' :=
  signed_eq_of_same_support (A i) (A i') (hentry i) (hentry i') hs
    (fun j j' => by simpa [mul_comm] using hminor i i' j j')

/-- A transparent three-by-three determinant polynomial used only in the
finite domino lemma; it is proved equal to Mathlib's determinant below. -/
def detThree (u v w : Lattice 3) : ℤ :=
  u 0 * (v 1 * w 2 - v 2 * w 1) -
  u 1 * (v 0 * w 2 - v 2 * w 0) +
  u 2 * (v 0 * w 1 - v 1 * w 0)

lemma detThree_eq (u v w : Lattice 3) :
    detThree u v w = (Matrix.of ![u, v, w]).det := by
  simp [detThree, Matrix.det_fin_three]
  <;> ring

/-- The exact seven signed nonzero entries of an induced domino. -/
def dominoColumns (s : Fin 7 → Bool) : Fin 6 → Lattice 3 :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1],
    ![(RankThree.signUnit (s 0) : ℤ), (RankThree.signUnit (s 1) : ℤ), 0],
    ![(RankThree.signUnit (s 2) : ℤ), (RankThree.signUnit (s 3) : ℤ), (RankThree.signUnit (s 4) : ℤ)],
    ![0, (RankThree.signUnit (s 5) : ℤ), (RankThree.signUnit (s 6) : ℤ)]]

/-- The graph's natural basis is changed by exchanging column 0 with column3.
This is an actual permutation of the six original vectors. -/
def dominoReindex : Fin 6 → Fin 6 := ![3, 1, 2, 0, 4, 5]

section DominoCertificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Split the exhaustive sign certificate into eight small kernel checks. -/
private def dominoBlock (s₀ s₁ s₂ : Bool) : Prop :=
  ∀ s₃ s₄ s₅ s₆ : Bool,
    let D := dominoColumns ![s₀, s₁, s₂, s₃, s₄, s₅, s₆]
    (∀ i j k, |detThree (D i) (D j) (D k)| ≤ 1) →
    ∀ i j k,
      detThree (D (dominoReindex i)) (D (dominoReindex j))
        (D (dominoReindex k)) = 0 ↔
      detThree (RankThree.baseRoot i) (RankThree.baseRoot j)
        (RankThree.baseRoot k) = 0

private theorem dominoBlock_000 : dominoBlock false false false := by
  unfold dominoBlock
  decide
private theorem dominoBlock_001 : dominoBlock false false true := by
  unfold dominoBlock
  decide
private theorem dominoBlock_010 : dominoBlock false true false := by
  unfold dominoBlock
  decide
private theorem dominoBlock_011 : dominoBlock false true true := by
  unfold dominoBlock
  decide
private theorem dominoBlock_100 : dominoBlock true false false := by
  unfold dominoBlock
  decide
private theorem dominoBlock_101 : dominoBlock true false true := by
  unfold dominoBlock
  decide
private theorem dominoBlock_110 : dominoBlock true true false := by
  unfold dominoBlock
  decide
private theorem dominoBlock_111 : dominoBlock true true true := by
  unfold dominoBlock
  decide

private theorem domino_finite_certificate :
    ∀ s₀ s₁ s₂ s₃ s₄ s₅ s₆ : Bool,
    let D := dominoColumns ![s₀, s₁, s₂, s₃, s₄, s₅, s₆]
    (∀ i j k, |detThree (D i) (D j) (D k)| ≤ 1) →
    ∀ i j k,
      detThree (D (dominoReindex i)) (D (dominoReindex j))
        (D (dominoReindex k)) = 0 ↔
      detThree (RankThree.baseRoot i) (RankThree.baseRoot j)
        (RankThree.baseRoot k) = 0 := by
  intro s₀ s₁ s₂
  cases s₀ <;> cases s₁ <;> cases s₂
  · exact dominoBlock_000
  · exact dominoBlock_001
  · exact dominoBlock_010
  · exact dominoBlock_011
  · exact dominoBlock_100
  · exact dominoBlock_101
  · exact dominoBlock_110
  · exact dominoBlock_111

end DominoCertificates

/-- Every uniformly unimodular signed lift of the domino has exactly the K4
rank-three dependence pattern, after the displayed column permutation. -/
theorem domino_uniform_has_K4_pattern (s : Fin 7 → Bool)
    (hD : ∀ i j k, |detThree (dominoColumns s i) (dominoColumns s j)
      (dominoColumns s k)| ≤ 1) :
    ∀ i j k,
      detThree (dominoColumns s (dominoReindex i))
        (dominoColumns s (dominoReindex j)) (dominoColumns s (dominoReindex k)) = 0 ↔
      detThree (RankThree.baseRoot i) (RankThree.baseRoot j)
        (RankThree.baseRoot k) = 0 := by
  have hs : s = ![s 0, s 1, s 2, s 3, s 4, s 5, s 6] := by
    funext i
    fin_cases i <;> rfl
  simpa only [← hs] using
    domino_finite_certificate (s 0) (s 1) (s 2) (s 3) (s 4) (s 5) (s 6) hD

/- A triangle of two-coordinate columns is either the complete-graphic K4
pattern or has a three-by-three minor of absolute value two. Uniformity excludes
the latter possibility. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem triangle_finite_certificate :
    ∀ s₀ s₁ s₂ s₃ s₄ s₅ : Bool,
    let C := RankThree.signedColumns ![s₀, s₁, s₂, s₃, s₄, s₅]
    |detThree (C 3) (C 4) (C 5)| ≤ 1 →
    ∀ i j k,
      detThree (C i) (C j) (C k) = 0 ↔
      detThree (RankThree.baseRoot i) (RankThree.baseRoot j)
        (RankThree.baseRoot k) = 0 := by
  decide

/-- The rank-three endpoint of an arbitrary-length induced-cycle contraction. -/
theorem triangle_uniform_has_K4_pattern (s : Fin 6 → Bool)
    (hC : |detThree (RankThree.signedColumns s 3)
      (RankThree.signedColumns s 4) (RankThree.signedColumns s 5)| ≤ 1) :
    ∀ i j k,
      detThree (RankThree.signedColumns s i) (RankThree.signedColumns s j)
        (RankThree.signedColumns s k) = 0 ↔
      detThree (RankThree.baseRoot i) (RankThree.baseRoot j)
        (RankThree.baseRoot k) = 0 := by
  have hs : s = ![s 0, s 1, s 2, s 3, s 4, s 5] := by
    funext i
    fin_cases i <;> rfl
  simpa only [← hs] using
    triangle_finite_certificate (s 0) (s 1) (s 2) (s 3) (s 4) (s 5) hC

#print axioms Unimodular.SeriesParallel.signed_eq_of_same_support
#print axioms Unimodular.SeriesParallel.domino_uniform_has_K4_pattern

end Unimodular.SeriesParallel
