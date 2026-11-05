module

public import PaperVerification.PowerOriginalDegreeEquiv
public import PaperVerification.EquivariantCokernelGenericSpecialization

/-!
# A universal original slope and the characteristic-zero lower bound

The parameter is the indeterminate in `K[T]`, and the generic field is its
fraction field. Nonresonance and all diagonal factors follow by reading the
constant coefficient. At a special slope the full original matrix, containing
every operator which can contribute in the degree, presents the actual image
span. Its projected Reynolds rank gives an unconditional lower bound, even
where the diagonal conjugation is singular.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Representation
open PaperVerification.EquivariantHomMatrices
open scoped BigOperators

namespace PaperVerification.PowerOperators

variable {K : Type*} [Field K] {n : ℕ}

/-- Equality elimination transports the actual quotient representation,
including the dependent quotient module and its invariance witness. -/
private theorem universal_ordinary_intertwiner_finrank_congr_family
    (G : Subgroup (Equiv.Perm (Fin n)))
    {f₁ f₂ : Fin n → MvPolynomial (Fin n) K} (heq : f₁ = f₂)
    (hinv₁ : ∀ g : G, ∀ i, MvPolynomial.rename (g : Equiv.Perm (Fin n)) (f₁ i) = f₁ i)
    (hinv₂ : ∀ g : G, ∀ i, MvPolynomial.rename (g : Equiv.Perm (Fin n)) (f₂ i) = f₂ i)
    (d : ℕ) {l : Type*} [Fintype l] (τ : Representation K G (l → K)) :
    Module.finrank K (IntertwiningMap τ (ordinaryQuotientDegreeRepresentation G f₁ hinv₁ d)) =
      Module.finrank K (IntertwiningMap τ (ordinaryQuotientDegreeRepresentation G f₂ hinv₂ d)) := by
  subst f₂
  rfl

abbrev UniversalSlopeField (K : Type*) [Field K] := FractionRing (Polynomial K)

def universalSlope (K : Type*) [Field K] : UniversalSlopeField K :=
  algebraMap (Polynomial K) (UniversalSlopeField K) Polynomial.X

theorem universalSlope_factor_ne_zero (a : ℕ) :
    (1 : UniversalSlopeField K) + universalSlope K * (a : UniversalSlopeField K) ≠ 0 := by
  have hp : (1 : Polynomial K) + Polynomial.X * (a : Polynomial K) ≠ 0 := by
    intro h
    have hc := congrArg (fun p : Polynomial K => p.coeff 0) h
    simpa using hc
  have h := (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial K) (UniversalSlopeField K))).mpr hp
  simpa only [map_add,map_one,map_mul,map_natCast,universalSlope] using h

theorem universalSlope_nonresonant [CharZero K] (m : ℕ) :
    Nonresonant (fun _ : Fin n => (1 : UniversalSlopeField K)) (universalSlope K) m := by
  intro I hI s hs
  have hp : (I.card : Polynomial K) + Polynomial.X * (s : Polynomial K) ≠ 0 := by
    intro h
    have hc := congrArg (fun p : Polynomial K => p.coeff 0) h
    have hcard : (I.card : K) ≠ 0 := Nat.cast_ne_zero.mpr hI.card_pos.ne'
    apply hcard
    simpa using hc
  have h := (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial K) (UniversalSlopeField K))).mpr hp
  simpa only [map_add,map_mul,map_natCast,universalSlope,Finset.sum_const,nsmul_eq_mul,mul_one] using h

theorem complete_intertwiner_finrank_scalar_extension
    {L : Type*} [Field L] [Algebra K L]
    (m d : ℕ) (hm : 0 < m) (G : Subgroup (Equiv.Perm (Fin n)))
    (hcard : IsUnit (Nat.card G : K))
    {l : Type*} [Fintype l] (τ : Representation K G (l → K)) :
    Module.finrank L (IntertwiningMap (mapRepresentation (algebraMap K L) τ)
      (completeHomogeneousDegreeRepresentation (K := L) G m d)) =
      Module.finrank K (IntertwiningMap τ (completeHomogeneousDegreeRepresentation G m d)) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  have hu : IsUnit (Fintype.card G : K) := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  letI : Invertible (Fintype.card G : K) := hu.invertible
  have huL : IsUnit (Fintype.card G : L) := by
    simpa only [map_natCast] using hu.map (algebraMap K L)
  letI : Invertible (Fintype.card G : L) := huL.invertible
  let f := completeHomogeneousFamily K n m
  have hmap (ψ : K →+* L) : (fun i => MvPolynomial.map ψ (f i)) =
      completeHomogeneousFamily L n m := by
    funext i
    exact MvPolynomial.map_hsymm (Fin n) K (m+i.val) ψ
  have hid : (fun i => MvPolynomial.map (RingHom.id K) (f i)) = f := by
    funext i
    exact MvPolynomial.map_id (f i)
  have hr : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) K)
      (List.ofFn fun i => MvPolynomial.map (RingHom.id K) (f i)) := by
    rw [hid]
    exact complete_homogeneous_isWeaklyRegular K n m hm
  have hrL : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) L)
      (List.ofFn fun i => MvPolynomial.map (algebraMap K L) (f i)) := by
    rw [hmap]
    exact complete_homogeneous_isWeaklyRegular L n m hm
  have h := ordinary_intertwiner_dimension_eq_at_regular_fibers G f m d
    (fun i => MvPolynomial.isHomogeneous_hsymm (m+i.val))
    (completeHomogeneousFamily_invariant G m) (RingHom.id K) (algebraMap K L) hr hrL τ
  rw [mapRepresentation_id] at h
  have hleft := universal_ordinary_intertwiner_finrank_congr_family (K := L) G
    (hmap (algebraMap K L))
    (map_family_invariant G f (completeHomogeneousFamily_invariant G m) (algebraMap K L))
    (completeHomogeneousFamily_invariant (K := L) G m) d
    (mapRepresentation (algebraMap K L) τ)
  have hright := universal_ordinary_intertwiner_finrank_congr_family (K := K) G hid
    (map_family_invariant G f (completeHomogeneousFamily_invariant G m) (RingHom.id K))
    (completeHomogeneousFamily_invariant (K := K) G m) d τ
  exact hleft.symm.trans (h.trans hright)

/-- The actual original-family homogeneous cokernel has at least the generic
intertwining dimension for every slope, without a nonresonance hypothesis. -/
theorem constant_original_intertwiner_finrank_ge_universal
    [CharZero K] (lam : K) (m d : ℕ)
    (G : Subgroup (Equiv.Perm (Fin n)))
    {l : Type*} [Fintype l] (τ : Representation K G (l → K)) :
    Module.finrank (UniversalSlopeField K)
      (IntertwiningMap (mapRepresentation (algebraMap K (UniversalSlopeField K)) τ)
        (originalTailQuotientDegreeRepresentation G (fun _ => 1) (universalSlope K) m
          (fun _ _ => rfl) d)) ≤
      Module.finrank K (IntertwiningMap τ
        (originalTailQuotientDegreeRepresentation G (fun _ => 1) lam m (fun _ _ => rfl) d)) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let R := Polynomial K
  let L := UniversalSlopeField K
  let φ : R →+* K := Polynomial.evalRingHom lam
  let φ₀ : R →+* L := algebraMap R L
  have hu : IsUnit (Fintype.card G : K) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  letI : Invertible (Fintype.card G : K) := hu.invertible
  have huR : IsUnit (Fintype.card G : R) := by
    simpa only [map_natCast] using hu.map (algebraMap K R)
  letI : Invertible (Fintype.card G : R) := huR.invertible
  have huL : IsUnit (Fintype.card G : L) := by
    simpa only [map_natCast] using hu.map (algebraMap K L)
  letI : Invertible (Fintype.card G : L) := huL.invertible
  let F := originalDegreeMatrix (fun _ : Fin n => (1 : R)) Polynomial.X m d
  let π := originalTailQuotientDegreeRepresentation G (fun _ : Fin n => (1 : K)) lam m
    (fun _ _ => rfl) d
  let π₀ := originalTailQuotientDegreeRepresentation G (fun _ : Fin n => (1 : L))
    (universalSlope K) m (fun _ _ => rfl) d
  have hφX : φ Polynomial.X = lam := by
    change Polynomial.eval lam Polynomial.X = lam
    exact Polynomial.eval_X
  have hφ₀X : φ₀ Polynomial.X = universalSlope K := rfl
  have hF : F.map φ = originalDegreeMatrix (fun _ : Fin n => (1 : K)) lam m d := by
    rw [map_originalDegreeMatrix]
    simp only [map_one,hφX]
  have hF₀ : F.map φ₀ =
      originalDegreeMatrix (fun _ : Fin n => (1 : L)) (universalSlope K) m d := by
    rw [map_originalDegreeMatrix]
    simp only [map_one,hφ₀X]
  let q : IntertwiningMap (mapRepresentation φ (shiftedDegreeAction (R := R) G 0 d)) π :=
    { toLinearMap := originalDegreeQuotientMap (fun _ => 1) lam m d
      isIntertwining' g := by
        rw [map_shiftedDegreeAction]
        exact (originalDegreeQuotientIntertwiner G (fun _ => 1) lam m d (fun _ _ => rfl)).isIntertwining' g }
  let q₀ : IntertwiningMap (mapRepresentation φ₀ (shiftedDegreeAction (R := R) G 0 d)) π₀ :=
    { toLinearMap := originalDegreeQuotientMap (fun _ => 1) (universalSlope K) m d
      isIntertwining' g := by
        rw [map_shiftedDegreeAction]
        exact (originalDegreeQuotientIntertwiner G (fun _ => 1) (universalSlope K) m d
          (fun _ _ => rfl)).isIntertwining' g }
  have hker : LinearMap.range (F.map φ).mulVecLin = LinearMap.ker q.toLinearMap := by
    rw [hF]
    exact originalDegreeQuotientMap_kernel _ _ _ _
  have hker₀ : LinearMap.range (F.map φ₀).mulVecLin = LinearMap.ker q₀.toLinearMap := by
    rw [hF₀]
    exact originalDegreeQuotientMap_kernel _ _ _ _
  have h := intertwiner_cokernel_dimension_ge_generic
    (mapRepresentation (algebraMap K R) τ) (originalDegreeAction (R := R) G d)
    (shiftedDegreeAction (R := R) G 0 d) F
    (originalDegreeMatrix_intertwines G (fun _ => 1) Polynomial.X m d (fun _ _ => rfl))
    φ π π₀ q q₀ (originalDegreeQuotientMap_surjective _ _ _ _)
    (originalDegreeQuotientMap_surjective _ _ _ _) hker hker₀
  have hφC : φ.comp (algebraMap K R) = RingHom.id K := by
    ext a
    simp [φ,R]
  have hφ₀C : φ₀.comp (algebraMap K R) = algebraMap K L :=
    (IsScalarTower.algebraMap_eq K R L).symm
  have hτ : mapRepresentation φ (mapRepresentation (algebraMap K R) τ) = τ := by
    calc
      mapRepresentation φ (mapRepresentation (algebraMap K R) τ) =
          mapRepresentation (φ.comp (algebraMap K R)) τ :=
        mapRepresentation_comp (algebraMap K R) φ τ
      _ = τ := by rw [hφC]; exact mapRepresentation_id τ
  have hτ₀ : mapRepresentation φ₀ (mapRepresentation (algebraMap K R) τ) =
      mapRepresentation (algebraMap K L) τ := by
    calc
      mapRepresentation φ₀ (mapRepresentation (algebraMap K R) τ) =
          mapRepresentation (φ₀.comp (algebraMap K R)) τ :=
        mapRepresentation_comp (algebraMap K R) φ₀ τ
      _ = mapRepresentation (algebraMap K L) τ := by rw [hφ₀C]
  rw [hτ₀,hτ] at h
  exact h

/-- The unconditional original-family comparison used in the necessity part
of Theorem 1.1. It holds over every characteristic-zero field and for every
slope, including all singular values of the diagonal conjugation. -/
theorem constant_complete_intertwiner_finrank_le_original
    [CharZero K] (lam : K) (m d : ℕ) (hm : 0 < m)
    (G : Subgroup (Equiv.Perm (Fin n)))
    {l : Type*} [Fintype l] (τ : Representation K G (l → K)) :
    Module.finrank K (IntertwiningMap τ (completeHomogeneousDegreeRepresentation G m d)) ≤
      Module.finrank K (IntertwiningMap τ
        (originalTailQuotientDegreeRepresentation G (fun _ : Fin n => (1 : K)) lam m
          (fun _ _ => rfl) d)) := by
  let L := UniversalSlopeField K
  have hcard : IsUnit (Nat.card G : K) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (ne_of_gt Nat.card_pos))
  obtain ⟨e⟩ := paper_theorem_2_2_original_degree_representation
    (fun _ : Fin n => (1 : L)) (universalSlope K) m d hm (universalSlope_nonresonant m)
    (fun _ a _ => universalSlope_factor_ne_zero a) G (fun _ _ => rfl)
  have he := (RepresentationHomComparison.intertwinerTargetEquiv
    (mapRepresentation (algebraMap K L) τ) e).finrank_eq
  have hbase := complete_intertwiner_finrank_scalar_extension (L := L) m d hm G hcard τ
  have h := constant_original_intertwiner_finrank_ge_universal lam m d G τ
  rw [he,hbase] at h
  exact h

end PaperVerification.PowerOperators
