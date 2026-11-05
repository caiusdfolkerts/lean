module

public import PaperVerification.FermionGaussGrading

/-!
# The rank-one trace identity from odd contractions

The prefix argument only needs the first-order rank-one coefficient of the Gauss
identity. It can be obtained directly by applying two odd contractions to the
proved diagonal normal order and projecting to the original exterior degree.
This avoids any diagonalization or density argument.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion

open scoped BigOperators

section Ring

variable {B J : Type*} [Ring B]

 theorem even_pair_odd_commute (a b c : B)
    (hac : a * c = -(c * a)) (hbc : b * c = -(c * b)) : Commute (a * b) c := by
  change (a * b) * c = c * (a * b)
  rw [mul_assoc, hbc, mul_neg, ← mul_assoc, hac, neg_mul, neg_neg, mul_assoc]

 theorem odd_pair_mul_left_eq_zero (a b : B)
    (ha : a * a = 0) (hba : b * a = -(a * b)) : (a * b) * a = 0 := by
  rw [mul_assoc, hba, mul_neg, ← mul_assoc, ha, zero_mul, neg_zero]

/-- Exact normal ordering through a finite product of square-zero raising
factors. The square-zero consequence needed here is stated as `fᵢ cᵢ = 0`. -/
theorem annihilator_product_normal_order (l : List J) (A : B) (f c : J → B)
    (hcomm : ∀ i, A * f i = f i * A + c i)
    (hzero : ∀ i, f i * c i = 0)
    (hcross : ∀ i j, Commute (c i) (f j)) :
    A * (l.map (fun i ↦ 1 + f i)).prod =
      (l.map (fun i ↦ 1 + f i)).prod * (A + (l.map c).sum) := by
  have hstep (i : J) : A * (1 + f i) = (1 + f i) * (A + c i) := by
    rw [mul_add, mul_one, hcomm]
    simp only [add_mul, one_mul, mul_add, hzero, add_zero]
    abel
  induction l with
  | nil => simp
  | cons i l ih =>
    have hc : Commute (c i) (l.map (fun j ↦ 1 + f j)).prod := by
      apply Commute.list_prod_right
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      exact (Commute.one_right _).add_right (hcross i j)
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    calc
      A * ((1 + f i) * (l.map (fun j ↦ 1 + f j)).prod) =
          (1 + f i) * ((A + c i) * (l.map (fun j ↦ 1 + f j)).prod) := by
        rw [← mul_assoc, hstep, mul_assoc]
      _ = (1 + f i) * ((l.map (fun j ↦ 1 + f j)).prod * (A + (l.map c).sum) +
          (l.map (fun j ↦ 1 + f j)).prod * c i) := by
        congr 1
        rw [add_mul, ih, hc.eq]
      _ = _ := by
        rw [← mul_add, mul_assoc]
        congr 2
        abel

end Ring

namespace Exterior

variable {R V I : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [Fintype I] [DecidableEq I]

local notation "E" => ExteriorAlgebra R V

variable (b : Module.Basis (I ⊕ I) R V)

/-- The odd creation obtained by commuting one contraction past one pair. -/
def pairRaiseCorrection (l : Module.Dual R V) (i : I) : V :=
  l (b (.inl i)) • b (.inr i) - l (b (.inr i)) • b (.inl i)

 theorem annihilation_pairRaise (l : Module.Dual R V) (i : I) :
    annihilation l * pairRaise b i = pairRaise b i * annihilation l +
      creation (pairRaiseCorrection b l i) := by
  have hθ : annihilation l * creation (b (.inl i)) =
      l (b (.inl i)) • 1 - creation (b (.inl i)) * annihilation l :=
    eq_sub_of_add_eq (annihilation_creation l (b (.inl i)))
  have hξ : annihilation l * creation (b (.inr i)) =
      l (b (.inr i)) • 1 - creation (b (.inr i)) * annihilation l :=
    eq_sub_of_add_eq (annihilation_creation l (b (.inr i)))
  simp only [pairRaise, pairRaiseCorrection, map_sub, map_smul]
  rw [← mul_assoc, hθ, sub_mul, smul_mul_assoc, one_mul, mul_assoc, hξ,
    mul_sub, mul_smul_comm, mul_one]
  abel

 theorem pairRaise_mul_correction (l : Module.Dual R V) (i : I) :
    pairRaise b i * creation (pairRaiseCorrection b l i) = 0 := by
  have hθ : pairRaise b i * creation (b (.inl i)) = 0 :=
    odd_pair_mul_left_eq_zero _ _ (creation_square _) (creation_anticomm_eq _ _)
  have hξ : pairRaise b i * creation (b (.inr i)) = 0 := by
    change (creation (b (.inl i)) * creation (b (.inr i))) * creation (b (.inr i)) = 0
    rw [mul_assoc, creation_square, mul_zero]
  simp only [pairRaiseCorrection, map_sub, map_smul, mul_sub, mul_smul_comm,
    hθ, hξ, smul_zero, sub_self]

 theorem creation_pairRaise_commute (v : V) (i : I) :
    Commute (creation (R := R) v) (pairRaise b i) :=
  (even_pair_odd_commute _ _ _ (creation_anticomm_eq _ _) (creation_anticomm_eq _ _)).symm

/-- The full odd correction for a diagonal raising product. -/
def raisingCorrection (a : I → R) (l : Module.Dual R V) : V :=
  ∑ i, a i • pairRaiseCorrection b l i

 theorem annihilation_raising_product (a : I → R) (l : Module.Dual R V) :
    annihilation l * (Finset.univ.toList.map (fun i ↦ 1 + a i • pairRaise b i)).prod =
      (Finset.univ.toList.map (fun i ↦ 1 + a i • pairRaise b i)).prod *
        (annihilation l + creation (raisingCorrection b a l)) := by
  have h := annihilator_product_normal_order Finset.univ.toList (annihilation l)
    (fun i ↦ a i • pairRaise b i)
    (fun i ↦ a i • creation (pairRaiseCorrection b l i))
    (fun i ↦ by
      rw [mul_smul_comm, annihilation_pairRaise, smul_add, smul_mul_assoc])
    (fun i ↦ by
      rw [smul_mul_assoc, mul_smul_comm, pairRaise_mul_correction, smul_zero, smul_zero])
    (fun i j ↦ commute_smul_right_of_commute (R := R)
      (commute_smul_left_of_commute (R := R)
        (creation_pairRaise_commute b (pairRaiseCorrection b l i) j) (a i)) (a j))
  simpa only [raisingCorrection, map_sum, map_smul, Finset.sum_map_toList] using h

/-- A raising product cannot contribute to a degree below the input degree. -/
theorem degreeProjection_raising_product_zero (a : I → R)
    {j k : ℕ} {w : E} (hw : w ∈ ⋀[R]^j V) (hkj : k < j) :
    exteriorDegreeProjection k
      ((Finset.univ.toList.map fun i ↦ 1 + a i • pairRaise b i).prod w) = 0 := by
  have hexp := prod_one_add_eq_sum_elementary
    (Finset.univ.toList.map (fun i ↦ a i • pairRaise b i))
  simp only [List.map_map, Function.comp_def] at hexp
  rw [hexp, LinearMap.sum_apply, map_sum]
  apply Finset.sum_eq_zero
  intro r hr
  exact exteriorDegreeProjection_zero
    (elementary_raising_mem b Finset.univ.toList a r j w hw) (by omega)

/-- Two odd contractions of a raising product have a single surviving
same-degree term. Its coefficient is their literal contraction pairing. -/
theorem degreeProjection_two_annihilations_raising_product
    (a : I → R) (l m : Module.Dual R V)
    {k : ℕ} (w : E) (hw : w ∈ ⋀[R]^k V)
    (hl : annihilation l w = 0) (hm : annihilation m w = 0) :
    exteriorDegreeProjection k
      (annihilation l (annihilation m
        ((Finset.univ.toList.map fun i ↦ 1 + a i • pairRaise b i).prod w))) =
      l (raisingCorrection b a m) • w := by
  let T : Module.End R E :=
    (Finset.univ.toList.map fun i ↦ 1 + a i • pairRaise b i).prod
  have hlT : annihilation l * T =
      T * (annihilation l + creation (raisingCorrection b a l)) :=
    annihilation_raising_product b a l
  have hmT : annihilation m * T =
      T * (annihilation m + creation (raisingCorrection b a m)) :=
    annihilation_raising_product b a m
  have hcar := congrArg (fun f : Module.End R E ↦ f w)
    (annihilation_creation l (raisingCorrection b a m))
  have hpair : annihilation l (creation (raisingCorrection b a m) w) =
      l (raisingCorrection b a m) • w := by
    simpa only [Module.End.mul_apply, LinearMap.add_apply, hl, map_zero, add_zero,
      LinearMap.smul_apply, Module.End.one_apply] using hcar
  have hcalc : annihilation l (annihilation m (T w)) =
      T (l (raisingCorrection b a m) • w +
        creation (raisingCorrection b a l) (creation (raisingCorrection b a m) w)) := by
    have hml := congrArg (fun f : Module.End R E ↦ f w) hmT
    have hll := congrArg (fun f : Module.End R E ↦ f (creation (raisingCorrection b a m) w)) hlT
    simp only [Module.End.mul_apply, LinearMap.add_apply, hm, zero_add] at hml
    simp only [Module.End.mul_apply, LinearMap.add_apply, hpair] at hll
    rw [hml, hll]
  rw [hcalc, map_add, map_add, map_smul, map_smul,
    degreeProjection_raising_product b Finset.univ.toList a hw]
  have hhigh : creation (raisingCorrection b a l) (creation (raisingCorrection b a m) w) ∈
      ⋀[R]^(k + 2) V :=
    creation_mem_succ _ (creation_mem_succ _ hw)
  rw [degreeProjection_raising_product_zero b a hhigh (by omega), add_zero]

/-- The same-degree rank-one term of the diagonal Gauss product. The two
pulled-back odd equations are exactly those supplied by polynomial odd
currents when the inverse coefficients are the geometric polynomials. -/
theorem diagonal_gauss_rankone_projection [LinearOrder (I ⊕ I)]
    (y : I → R) (u v : R) (N : ℕ) (hy : ∀ i, ((-u * v) * y i) ^ N = 0)
    (hfac : IsUnit ((Fintype.card I).factorial : R))
    (l m : Module.Dual R V) (k : ℕ) (w : E) (hwdegree : w ∈ ⋀[R]^k V)
    (hw : ∀ p : Polynomial R, (∑ i, p.eval (y i) • pairLower b i) w = 0)
    (hl : annihilation (l.comp (modeScaling b (fun i ↦ gaussNilpotentInverse u v (y i) N))) w = 0)
    (hm : annihilation (m.comp (modeScaling b (fun i ↦ gaussNilpotentInverse u v (y i) N))) w = 0) :
    exteriorDegreeProjection k
      (annihilation l (annihilation m
        (((Finset.univ.toList.map fun i ↦ 1 + (u * y i) • pairLower b i).prod)
          (((Finset.univ.toList.map fun i ↦ 1 + v • pairRaise b i).prod) w)))) =
      l (raisingCorrection b (fun i ↦ v * gaussNilpotentInverse u v (y i) N) m) •
        (((Finset.univ.toList.map fun i ↦
          pairGaussDiagonal (u * y i) v (gaussNilpotentInverse u v (y i) N)
            (pairLower b i) (pairRaise b i)).prod) w) := by
  rw [diagonal_gauss_apply_primitive b y u v N hy hfac w hw]
  apply degreeProjection_two_annihilations_raising_product b
    (fun i ↦ v * gaussNilpotentInverse u v (y i) N) l m _
    (diagonalProduct_mem b _ _ _ _ hwdegree)
  · rw [annihilation_diagonalProduct b _ _ _
      (fun i ↦ gaussNilpotentInverse_mul_of_product_pow_eq_zero u v (y i) N (hy i)), hl, map_zero, smul_zero]
  · rw [annihilation_diagonalProduct b _ _ _
      (fun i ↦ gaussNilpotentInverse_mul_of_product_pow_eq_zero u v (y i) N (hy i)), hm, map_zero, smul_zero]

/-- The two odd functionals used in the rank-one perturbation. -/
def rankOneThetaDual (v : I → R) : Module.Dual R V :=
  ∑ i, v i • b.coord (.inl i)

def rankOneXiDual (U : I → R) : Module.Dual R V :=
  ∑ i, U i • b.coord (.inr i)

@[simp] theorem rankOneThetaDual_inl (v : I → R) (i : I) :
    rankOneThetaDual b v (b (.inl i)) = v i := by
  simp [rankOneThetaDual, Module.Basis.coord_apply, Finsupp.single_apply]

@[simp] theorem rankOneThetaDual_inr (v : I → R) (i : I) :
    rankOneThetaDual b v (b (.inr i)) = 0 := by
  simp [rankOneThetaDual, Module.Basis.coord_apply, Finsupp.single_apply]

@[simp] theorem rankOneXiDual_inl (v : I → R) (i : I) :
    rankOneXiDual b v (b (.inl i)) = 0 := by
  simp [rankOneXiDual, Module.Basis.coord_apply, Finsupp.single_apply]

@[simp] theorem rankOneXiDual_inr (v : I → R) (i : I) :
    rankOneXiDual b v (b (.inr i)) = v i := by
  simp [rankOneXiDual, Module.Basis.coord_apply, Finsupp.single_apply]

 theorem rankOneThetaDual_comp_modeScaling (v d : I → R) :
    (rankOneThetaDual b v).comp (modeScaling b d) =
      rankOneThetaDual b (fun i ↦ v i * d i) := by
  apply LinearMap.ext
  intro w
  simp only [rankOneThetaDual, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  have h := LinearMap.congr_fun (coord_modeScaling b d (.inl i)) w
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, Sum.elim_inl] at h
  rw [h, smul_smul]

 theorem rankOneXiDual_comp_modeScaling (v d : I → R) :
    (rankOneXiDual b v).comp (modeScaling b d) =
      rankOneXiDual b (fun i ↦ v i * d i) := by
  apply LinearMap.ext
  intro w
  simp only [rankOneXiDual, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  have h := LinearMap.congr_fun (coord_modeScaling b d (.inr i)) w
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, Sum.elim_inr] at h
  rw [h, smul_smul]

/-- The surviving contraction pairing is precisely the diagonal rank-one trace. -/
theorem rankOne_raisingCorrection_trace (U vcoeff d : I → R) (v : R) :
    rankOneXiDual b U
      (raisingCorrection b (fun i ↦ v * d i) (rankOneThetaDual b vcoeff)) =
      v * ∑ i, U i * vcoeff i * d i := by
  simp only [raisingCorrection, pairRaiseCorrection, rankOneThetaDual_inl,
    rankOneThetaDual_inr, zero_smul, sub_zero, map_sum, map_smul,
    rankOneXiDual_inr, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The exact rank-one trace identity under the paper's mixed and odd polynomial
current hypotheses. The pulled-back equations in the preceding lemma are
proved here from the common inverse polynomial, rather than assumed. -/
theorem diagonal_gauss_rankone_trace_identity [LinearOrder (I ⊕ I)]
    (y U vcoeff : I → R) (u v : R) (N : ℕ) (hy : ∀ i, ((-u * v) * y i) ^ N = 0)
    (hfac : IsUnit ((Fintype.card I).factorial : R))
    (k : ℕ) (w : E) (hwdegree : w ∈ ⋀[R]^k V)
    (hw : ∀ p : Polynomial R, (∑ i, p.eval (y i) • pairLower b i) w = 0)
    (hθ : ∀ p : Polynomial R,
      annihilation (rankOneThetaDual b (fun i ↦ vcoeff i * p.eval (y i))) w = 0)
    (hξ : ∀ p : Polynomial R,
      annihilation (rankOneXiDual b (fun i ↦ U i * p.eval (y i))) w = 0) :
    exteriorDegreeProjection k
      (annihilation (rankOneXiDual b U) (annihilation (rankOneThetaDual b vcoeff)
        (((Finset.univ.toList.map fun i ↦ 1 + (u * y i) • pairLower b i).prod)
          (((Finset.univ.toList.map fun i ↦ 1 + v • pairRaise b i).prod) w)))) =
      (v * ∑ i, U i * vcoeff i * gaussNilpotentInverse u v (y i) N) •
        (((Finset.univ.toList.map fun i ↦
          pairGaussDiagonal (u * y i) v (gaussNilpotentInverse u v (y i) N)
            (pairLower b i) (pairRaise b i)).prod) w) := by
  have hl : annihilation
      ((rankOneXiDual b U).comp (modeScaling b (fun i ↦ gaussNilpotentInverse u v (y i) N))) w = 0 := by
    rw [rankOneXiDual_comp_modeScaling]
    simpa only [gaussInversePolynomial_eval] using hξ (gaussInversePolynomial u v N)
  have hm : annihilation
      ((rankOneThetaDual b vcoeff).comp (modeScaling b (fun i ↦ gaussNilpotentInverse u v (y i) N))) w = 0 := by
    rw [rankOneThetaDual_comp_modeScaling]
    simpa only [gaussInversePolynomial_eval] using hθ (gaussInversePolynomial u v N)
  simpa only [rankOne_raisingCorrection_trace] using
    diagonal_gauss_rankone_projection b y u v N hy hfac
      (rankOneXiDual b U) (rankOneThetaDual b vcoeff) k w hwdegree hw hl hm

/-- The coefficient in the direct rank-one expansion. It contains no occurrence
of the varying scalar `v`. -/
def diagonalRankOneCoefficient (y U vcoeff : I → R) (u : R) (k : ℕ) (w : E) (j : ℕ) : E :=
  exteriorDegreeProjection k
    (annihilation (rankOneXiDual b U) (annihilation (rankOneThetaDual b vcoeff)
      (((Finset.univ.toList.map fun i ↦ 1 + (u * y i) • pairLower b i).prod)
        (elementaryOperator (Finset.univ.toList.map (pairRaise b)) j w))))

/-- The rank-one trace expression has the same primitive cutoff as the scalar
Gauss expression. This is the finite algebraic formula needed for the second
prefix equation. -/
theorem diagonal_gauss_rankone_bounded_expression [LinearOrder (I ⊕ I)]
    (y U vcoeff : I → R) (u v : R) (N : ℕ) (hy : ∀ i, ((-u * v) * y i) ^ N = 0)
    (hfac : IsUnit ((Fintype.card I).factorial : R))
    (k : ℕ) (w : E) (hwdegree : w ∈ ⋀[R]^k V) (hk : k ≤ Fintype.card I)
    (hw : ∀ p : Polynomial R, (∑ i, p.eval (y i) • pairLower b i) w = 0)
    (hθ : ∀ p : Polynomial R,
      annihilation (rankOneThetaDual b (fun i ↦ vcoeff i * p.eval (y i))) w = 0)
    (hξ : ∀ p : Polynomial R,
      annihilation (rankOneXiDual b (fun i ↦ U i * p.eval (y i))) w = 0) :
    (v * ∑ i, U i * vcoeff i * gaussNilpotentInverse u v (y i) N) •
      (((Finset.univ.toList.map fun i ↦
        pairGaussDiagonal (u * y i) v (gaussNilpotentInverse u v (y i) N)
          (pairLower b i) (pairRaise b i)).prod) w) =
      ∑ j ∈ Finset.range (Fintype.card I - k + 1),
        v ^ j • diagonalRankOneCoefficient b y U vcoeff u k w j := by
  have he : lowering b w = 0 := by
    simpa only [Polynomial.eval_one, one_smul, lowering] using hw 1
  rw [← diagonal_gauss_rankone_trace_identity b y U vcoeff u v N hy hfac k w hwdegree hw hθ hξ]
  have hexp := prod_one_add_smul_eq_sum
    (Finset.univ.toList.map (pairRaise b)) v
  simp only [List.map_map, Function.comp_def, List.length_map,
    Finset.length_toList, Finset.card_univ] at hexp
  rw [hexp, LinearMap.sum_apply, map_sum, map_sum, map_sum, map_sum]
  simp only [LinearMap.smul_apply, map_smul]
  change (∑ j ∈ Finset.range (Fintype.card I + 1),
    v ^ j • diagonalRankOneCoefficient b y U vcoeff u k w j) = _
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro j hj hnot
  have hj' : Fintype.card I - k < j := by
    simp only [Finset.mem_range] at hnot
    omega
  simp only [diagonalRankOneCoefficient,
    primitive_elementary_raising_eq_zero b hfac k w hwdegree he hk j hj', map_zero, smul_zero]

/-- The constant coefficient in the rank-one expansion is actually zero. -/
theorem diagonalRankOneCoefficient_zero
    (y U vcoeff : I → R) (u : R)
    (hfac : IsUnit ((Fintype.card I).factorial : R))
    (k : ℕ) (w : E)
    (hw : ∀ p : Polynomial R, (∑ i, p.eval (y i) • pairLower b i) w = 0)
    (hθ : annihilation (rankOneThetaDual b vcoeff) w = 0) :
    diagonalRankOneCoefficient b y U vcoeff u k w 0 = 0 := by
  have hfix : ((Finset.univ.toList.map fun i ↦ 1 + (u * y i) • pairLower b i).prod) w = w := by
    simpa [gaussNilpotentInverse] using diagonal_gauss_right_fixes b y u 0 1 hfac w hw
  simp only [diagonalRankOneCoefficient, elementaryOperator_zero,
    Module.End.one_apply, hfix, hθ, map_zero]


end Exterior

end PaperVerification.Fermion
