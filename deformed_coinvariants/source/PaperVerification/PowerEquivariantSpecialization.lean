module

public import PaperVerification.PowerDegreePresentation

/-!
# The full equivariant specialization bound for the actual power tail

The group is any subgroup of permutations fixing the actual coefficient tuple.
The group order is proved invertible from nonresonance. There is one generic
coefficient for every actual coefficient class, so the universal family is
group invariant and retains an exact zero-slope fiber in every characteristic.
The endpoint concerns actual homogeneous quotient representations and an
arbitrary finite-coordinate test representation. No rank, exactness,
regularity, semisimplicity, or multiplicity assumption is added.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Representation
open PaperVerification.EquivariantHomMatrices

namespace PaperVerification.PowerOperators

variable {K : Type*} [Field K] {n : ℕ}

theorem tailQuotientDegree_intertwiner_finrank_ge_grouped_zero_of_regular
    (c : Fin n → K) (lam : K) (m d : ℕ) (hm : 0 < m)
    (G : Subgroup (Equiv.Perm (Fin n)))
    (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i)
    (hcard : IsUnit (Nat.card G : K))
    (hregular : RingTheory.Sequence.IsWeaklyRegular
      (MvPolynomial (Fin n) (GroupedCoefficientField c))
      (List.ofFn fun i : Fin n => weightedPower (groupedCoefficient c) (m+i.val)))
    {l : Type*} [Fintype l] (τ : Representation K G (l → K)) :
    Module.finrank (GroupedCoefficientField c)
      (IntertwiningMap (mapRepresentation (algebraMap K (GroupedCoefficientField c)) τ)
        (tailQuotientDegreeRepresentation G (groupedCoefficient c) 0 m
          (fun g i => groupedCoefficient_permutation c g (hfix g) i) d)) ≤
      Module.finrank K (IntertwiningMap τ (tailQuotientDegreeRepresentation G c lam m hfix d)) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let U := MvPolynomial (Option (CoefficientClass c)) K
  let E := GroupedCoefficientField c
  have hunit : IsUnit (Fintype.card G : K) := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  letI : Invertible (Fintype.card G : K) := hunit.invertible
  have hunitU : IsUnit (Fintype.card G : U) := by
    simpa only [map_natCast] using hunit.map (algebraMap K U)
  letI : Invertible (Fintype.card G : U) := hunitU.invertible
  have hunitE : IsUnit (Fintype.card G : E) := by
    simpa only [map_natCast] using hunit.map (algebraMap K E)
  letI : Invertible (Fintype.card G : E) := hunitE.invertible
  let cU : Fin n → U := fun i => X (some (coefficientClassOf c i))
  let lamU : U := X none
  let φ : U →+* K := MvPolynomial.eval (fun a => a.elim lam Subtype.val)
  let φ₀ : U →+* E := MvPolynomial.eval₂Hom (algebraMap K E)
    (fun a => a.elim 0 (fun b => algebraMap (GroupedCoefficientRing c) E (X b)))
  let τU := mapRepresentation (algebraMap K U) τ
  have hfixU : ∀ g : G, ∀ i, cU ((g : Equiv.Perm (Fin n)) i) = cU i := by
    intro g i
    have hc : coefficientClassOf c ((g : Equiv.Perm (Fin n)) i) = coefficientClassOf c i :=
      Subtype.ext (hfix g i)
    simp only [cU,hc]
  have hfix₀ : ∀ g : G, ∀ i,
      groupedCoefficient c ((g : Equiv.Perm (Fin n)) i) = groupedCoefficient c i :=
    fun g i => groupedCoefficient_permutation c g (hfix g) i
  have hcφ : (fun i => φ (cU i)) = c := by
    funext i
    exact MvPolynomial.eval_X _
  have hlφ : φ lamU = lam := MvPolynomial.eval_X _
  have hcφ₀ : (fun i => φ₀ (cU i)) = groupedCoefficient c := by
    funext i
    exact MvPolynomial.eval₂Hom_X' _ _ _
  have hlφ₀ : φ₀ lamU = 0 := MvPolynomial.eval₂Hom_X' _ _ _
  have hF : (tailDegreeMatrix cU lamU m d).map φ = tailDegreeMatrix c lam m d := by
    rw [map_tailDegreeMatrix, hcφ, hlφ]
  have hF₀ : (tailDegreeMatrix cU lamU m d).map φ₀ =
      tailDegreeMatrix (groupedCoefficient c) 0 m d := by
    rw [map_tailDegreeMatrix, hcφ₀, hlφ₀]
  have hD₀ : (syzygyDegreeMatrix cU lamU m d).map φ₀ =
      syzygyDegreeMatrix (groupedCoefficient c) 0 m d := by
    rw [map_syzygyDegreeMatrix, hcφ₀, hlφ₀]
  have hexact : LinearMap.range ((syzygyDegreeMatrix cU lamU m d).map φ₀).mulVecLin =
      LinearMap.ker ((tailDegreeMatrix cU lamU m d).map φ₀).mulVecLin := by
    rw [hD₀,hF₀]
    exact zero_slope_degree_exact _ _ _ hregular
  let π := tailQuotientDegreeRepresentation G c lam m hfix d
  let π₀ := tailQuotientDegreeRepresentation G (groupedCoefficient c) 0 m hfix₀ d
  let q : IntertwiningMap (mapRepresentation φ (shiftedDegreeAction (R := U) G 0 d)) π :=
    { toLinearMap := degreeQuotientMap c lam m d
      isIntertwining' g := by
        rw [map_shiftedDegreeAction]
        exact (degreeQuotientIntertwiner G c lam m d hfix).isIntertwining' g }
  let q₀ : IntertwiningMap (mapRepresentation φ₀ (shiftedDegreeAction (R := U) G 0 d)) π₀ :=
    { toLinearMap := degreeQuotientMap (groupedCoefficient c) 0 m d
      isIntertwining' g := by
        rw [map_shiftedDegreeAction]
        exact (degreeQuotientIntertwiner G (groupedCoefficient c) 0 m d hfix₀).isIntertwining' g }
  have hker : LinearMap.range ((tailDegreeMatrix cU lamU m d).map φ).mulVecLin =
      LinearMap.ker q.toLinearMap := by
    rw [hF]
    exact degreeQuotientMap_kernel c lam m d
  have hker₀ : LinearMap.range ((tailDegreeMatrix cU lamU m d).map φ₀).mulVecLin =
      LinearMap.ker q₀.toLinearMap := by
    rw [hF₀]
    exact degreeQuotientMap_kernel _ _ _ _
  have h := intertwiner_cokernel_dimension_ge_exact_fiber
    τU (syzygyDegreeAction (R := U) G m d) (tailDegreeAction (R := U) G m d)
    (shiftedDegreeAction (R := U) G 0 d)
    (tailDegreeMatrix cU lamU m d) (syzygyDegreeMatrix cU lamU m d)
    (tailDegreeMatrix_mul_syzygyDegreeMatrix cU lamU m d)
    (tailDegreeMatrix_intertwines G cU lamU m d hfixU)
    (syzygyDegreeMatrix_intertwines G cU lamU m d hfixU)
    φ φ₀ hexact π π₀ q q₀ (degreeQuotientMap_surjective c lam m d)
    (degreeQuotientMap_surjective (groupedCoefficient c) 0 m d) hker hker₀
  have hφC : φ.comp (algebraMap K U) = RingHom.id K := by
    ext a
    exact MvPolynomial.eval_C _
  have hφ₀C : φ₀.comp (algebraMap K U) = algebraMap K E := by
    ext a
    exact MvPolynomial.eval₂Hom_C _ _ _
  have hτ : mapRepresentation φ τU = τ := by
    calc
      mapRepresentation φ τU = mapRepresentation (φ.comp (algebraMap K U)) τ :=
        mapRepresentation_comp (algebraMap K U) φ τ
      _ = τ := by rw [hφC]; exact mapRepresentation_id τ
  have hτ₀ : mapRepresentation φ₀ τU = mapRepresentation (algebraMap K E) τ := by
    calc
      mapRepresentation φ₀ τU = mapRepresentation (φ₀.comp (algebraMap K U)) τ :=
        mapRepresentation_comp (algebraMap K U) φ₀ τ
      _ = mapRepresentation (algebraMap K E) τ := by rw [hφ₀C]
  rw [hτ₀, hτ] at h
  simpa only [π, π₀, E, hfix₀] using h

/-- The full nonresonant endpoint: regularity and group-order invertibility
are derived from the paper's hypotheses, rather than supplied. -/
theorem tailQuotientDegree_intertwiner_finrank_ge_grouped_zero
    (c : Fin n → K) (lam : K) (m d : ℕ) (hm : 0 < m)
    (hnr : Nonresonant c lam m)
    (G : Subgroup (Equiv.Perm (Fin n)))
    (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i)
    {l : Type*} [Fintype l] (τ : Representation K G (l → K)) :
    Module.finrank (GroupedCoefficientField c)
      (IntertwiningMap (mapRepresentation (algebraMap K (GroupedCoefficientField c)) τ)
        (tailQuotientDegreeRepresentation G (groupedCoefficient c) 0 m
          (fun g i => groupedCoefficient_permutation c g (hfix g) i) d)) ≤
      Module.finrank K (IntertwiningMap τ (tailQuotientDegreeRepresentation G c lam m hfix d)) := by
  exact tailQuotientDegree_intertwiner_finrank_ge_grouped_zero_of_regular c lam m d hm G hfix
    (hnr.isUnit_stabilizer_card G hfix) (grouped_weighted_power_regular hnr m hm) τ

/-- For the constant tuple, the generic zero-slope comparison remains valid
at every slope in characteristic zero, including the resonant parameters.
This is the unconditional comparison used in the necessity direction of
Theorem 1.1. -/
theorem constant_tailQuotientDegree_intertwiner_finrank_ge_grouped_zero
    [CharZero K] (lam : K) (m d : ℕ) (hm : 0 < m)
    (G : Subgroup (Equiv.Perm (Fin n)))
    {l : Type*} [Fintype l] (τ : Representation K G (l → K)) :
    Module.finrank (GroupedCoefficientField (fun _ : Fin n => (1 : K)))
      (IntertwiningMap
        (mapRepresentation (algebraMap K (GroupedCoefficientField (fun _ : Fin n => (1 : K)))) τ)
        (tailQuotientDegreeRepresentation G (groupedCoefficient (fun _ : Fin n => (1 : K))) 0 m
          (fun g i => groupedCoefficient_permutation _ g (fun _ => rfl) i) d)) ≤
      Module.finrank K (IntertwiningMap τ
        (tailQuotientDegreeRepresentation G (fun _ : Fin n => (1 : K)) lam m (fun _ _ => rfl) d)) := by
  classical
  let c : Fin n → K := fun _ => 1
  let E := GroupedCoefficientField c
  have hcard : IsUnit (Nat.card G : K) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (ne_of_gt Nat.card_pos))
  have hsum : ∀ I : Finset (Fin n), I.Nonempty → IsUnit (∑ i ∈ I, groupedCoefficient c i) := by
    intro I hI
    obtain ⟨i,hi⟩ := hI
    have he : ∀ j, groupedCoefficient c j = groupedCoefficient c i := by
      intro j
      have hc : coefficientClassOf c j = coefficientClassOf c i := Subtype.ext rfl
      simp only [groupedCoefficient,hc]
    have hx : groupedCoefficient c i ≠ 0 := by
      apply (map_ne_zero_iff _ (IsFractionRing.injective (GroupedCoefficientRing c) E)).mpr
      exact MvPolynomial.X_ne_zero _
    have hscalar : (I.card : E) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_pos.mpr ⟨i,hi⟩).ne'
    apply isUnit_iff_ne_zero.mpr
    simp only [he,Finset.sum_const,nsmul_eq_mul]
    exact mul_ne_zero hscalar hx
  have hregular : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) E)
      (List.ofFn fun i : Fin n => weightedPower (groupedCoefficient c) (m+i.val)) := by
    simpa only [weightedPower_eq_powerMoment] using
      Fermion.powerMoments_isWeaklyRegular (fun _ : Fin n => 1) (groupedCoefficient c) m
        (fun _ => Nat.zero_lt_one) hm hsum
  exact tailQuotientDegree_intertwiner_finrank_ge_grouped_zero_of_regular c lam m d hm G
    (fun _ _ => rfl) hcard hregular τ

end PaperVerification.PowerOperators
