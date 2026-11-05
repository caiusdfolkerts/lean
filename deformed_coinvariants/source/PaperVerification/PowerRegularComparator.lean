module

public import PaperVerification.PowerEquivariantSpecialization
public import PaperVerification.PowerCompleteHomogeneousRegular
public import PaperVerification.HomogeneousKoszulSpecialization

/-!
# The complete homogeneous representation comparator

A homogeneous invariant family interpolates between the grouped generic
weighted powers and the literal complete homogeneous polynomials. Both fibers
are regular, so the proved two-endpoint Koszul/Reynolds comparison identifies
every intertwining dimension. The identification is over the original field;
there is no passage to an algebraically closed representation field and no
assumed descent statement.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Representation
open PaperVerification.EquivariantHomMatrices
open scoped BigOperators

namespace PaperVerification.PowerOperators

section Ring

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

theorem weightedPower_isHomogeneous (c : Fin n → R) (k : ℕ) :
    (weightedPower c k).IsHomogeneous k := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  exact (MvPolynomial.isHomogeneous_X_pow i k).C_mul (c i)

theorem map_weightedPower (φ : R →+* S) (c : Fin n → R) (k : ℕ) :
    MvPolynomial.map φ (weightedPower c k) = weightedPower (fun i => φ (c i)) k := by
  simp only [weightedPower,map_sum,map_mul,MvPolynomial.map_C,map_pow,MvPolynomial.map_X]

theorem rename_weightedPower (e : Equiv.Perm (Fin n)) (c : Fin n → R)
    (hfix : ∀ i, c (e i) = c i) (k : ℕ) :
    MvPolynomial.rename e (weightedPower c k) = weightedPower c k := by
  have h := rename_reversed e c 0 hfix k (1 : MvPolynomial (Fin n) R)
  simpa only [reversed_zero_slope,map_one,mul_one] using h

theorem tailDegreeMatrix_zero_eq_ordinary (c : Fin n → R) (m d : ℕ) :
    tailDegreeMatrix c 0 m d = ordinaryFirstMatrix (fun i => weightedPower c (m+i.val)) m d := by
  apply Matrix.mulVec_injective
  funext v a
  rw [tailDegreeMatrix_mulVec,ordinaryFirstMatrix_mulVec,tailMap_zero_slope]

end Ring

section Field

variable {K : Type*} [Field K] {n : ℕ}

def completeHomogeneousFamily (K : Type*) [Field K] (n m : ℕ) :
    Fin n → MvPolynomial (Fin n) K := fun i => MvPolynomial.hsymm (Fin n) K (m+i.val)

theorem completeHomogeneousFamily_invariant
    (G : Subgroup (Equiv.Perm (Fin n))) (m : ℕ) (g : G) (i : Fin n) :
    MvPolynomial.rename (g : Equiv.Perm (Fin n)) (completeHomogeneousFamily K n m i) =
      completeHomogeneousFamily K n m i :=
  MvPolynomial.rename_hsymm _ _ _ _

def completeHomogeneousDegreeRepresentation
    (G : Subgroup (Equiv.Perm (Fin n))) (m d : ℕ) :
    Representation K G (ordinaryQuotientDegree (completeHomogeneousFamily K n m) d) :=
  ordinaryQuotientDegreeRepresentation G (completeHomogeneousFamily K n m)
    (completeHomogeneousFamily_invariant G m) d

/-- At zero slope the actual differential quotient and the actual ordinary
ideal quotient have identical intertwining dimensions, via their identical
finite presentations. No regularity assumption is needed for this bridge. -/
theorem zero_tail_ordinary_intertwiner_finrank_eq
    (G : Subgroup (Equiv.Perm (Fin n))) [Fintype G] [Invertible (Fintype.card G : K)]
    (c : Fin n → K) (m d : ℕ)
    (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i)
    {l : Type*} [Fintype l] (τ : Representation K G (l → K)) :
    Module.finrank K (IntertwiningMap τ (tailQuotientDegreeRepresentation G c 0 m hfix d)) =
      Module.finrank K (IntertwiningMap τ
        (ordinaryQuotientDegreeRepresentation G (fun i => weightedPower c (m+i.val))
          (fun g i => rename_weightedPower g c (hfix g) (m+i.val)) d)) := by
  let f : IntertwiningMap (tailDegreeAction (R := K) G m d) (shiftedDegreeAction (R := K) G 0 d) :=
    ⟨(tailDegreeMatrix c 0 m d).mulVecLin,tailDegreeMatrix_intertwines G c 0 m d hfix⟩
  let q := degreeQuotientIntertwiner G c 0 m d hfix
  let q₀ := ordinaryDegreeQuotientIntertwiner G (fun i => weightedPower c (m+i.val))
    (fun g i => rename_weightedPower g c (hfix g) (m+i.val)) d
  have h₁ := equivariant_cokernel_rank_formula τ f q (degreeQuotientMap_surjective c 0 m d)
    (degreeQuotientMap_kernel c 0 m d)
  have he : LinearMap.range f.toLinearMap = LinearMap.ker q₀.toLinearMap := by
    change LinearMap.range (tailDegreeMatrix c 0 m d).mulVecLin = _
    rw [tailDegreeMatrix_zero_eq_ordinary]
    exact ordinaryDegreeQuotientMap_kernel _ m d (fun i => weightedPower_isHomogeneous c _)
  have h₀ := equivariant_cokernel_rank_formula τ f q₀
    (ordinaryDegreeQuotientMap_surjective _ d) he
  omega

/-- Transport an intertwining dimension along equality of the actual families.
The invariance witnesses are proposition-valued, so equality elimination also
identifies the induced quotient actions. -/
private theorem ordinary_intertwiner_finrank_congr_family
    (G : Subgroup (Equiv.Perm (Fin n)))
    {f₁ f₂ : Fin n → MvPolynomial (Fin n) K} (heq : f₁ = f₂)
    (hinv₁ : ∀ g : G, ∀ i, MvPolynomial.rename (g : Equiv.Perm (Fin n)) (f₁ i) = f₁ i)
    (hinv₂ : ∀ g : G, ∀ i, MvPolynomial.rename (g : Equiv.Perm (Fin n)) (f₂ i) = f₂ i)
    (d : ℕ) {l : Type*} [Fintype l] (τ : Representation K G (l → K)) :
    Module.finrank K (IntertwiningMap τ (ordinaryQuotientDegreeRepresentation G f₁ hinv₁ d)) =
      Module.finrank K (IntertwiningMap τ (ordinaryQuotientDegreeRepresentation G f₂ hinv₂ d)) := by
  subst f₂
  rfl

set_option maxHeartbeats 800000 in
/-- The generic ordinary weighted-power quotient and the complete homogeneous
quotient have equal intertwining dimensions over their respective fields.
The comparison is obtained from a literal invariant polynomial family. -/
theorem grouped_power_complete_intertwiner_finrank_eq
    (c : Fin n → K) (m d : ℕ) (hm : 0 < m)
    (G : Subgroup (Equiv.Perm (Fin n)))
    (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i)
    (hcard : IsUnit (Nat.card G : K))
    (hregular : RingTheory.Sequence.IsWeaklyRegular
      (MvPolynomial (Fin n) (GroupedCoefficientField c))
      (List.ofFn fun i : Fin n => weightedPower (groupedCoefficient c) (m+i.val)))
    {l : Type*} [Fintype l] (τ : Representation K G (l → K)) :
    Module.finrank (GroupedCoefficientField c)
      (IntertwiningMap (mapRepresentation (algebraMap K (GroupedCoefficientField c)) τ)
        (ordinaryQuotientDegreeRepresentation (K := GroupedCoefficientField c) G
          (fun i => weightedPower (groupedCoefficient c) (m+i.val))
          (fun g i => rename_weightedPower (R := GroupedCoefficientField c)
            (g : Equiv.Perm (Fin n)) (groupedCoefficient c)
            (fun j => groupedCoefficient_permutation (K := K) c
              (g : Equiv.Perm (Fin n)) (hfix g) j) (m+i.val)) d)) =
      Module.finrank K (IntertwiningMap τ (completeHomogeneousDegreeRepresentation G m d)) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let U := MvPolynomial (Option (CoefficientClass c)) K
  let E := GroupedCoefficientField c
  have hu : IsUnit (Fintype.card G : K) := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  letI : Invertible (Fintype.card G : K) := hu.invertible
  have huU : IsUnit (Fintype.card G : U) := by
    simpa only [map_natCast] using hu.map (algebraMap K U)
  letI : Invertible (Fintype.card G : U) := huU.invertible
  have huE : IsUnit (Fintype.card G : E) := by
    simpa only [map_natCast] using hu.map (algebraMap K E)
  letI : Invertible (Fintype.card G : E) := huE.invertible
  let b : Fin n → U := fun i => X (some (coefficientClassOf c i))
  let t : U := X none
  let f : Fin n → MvPolynomial (Fin n) U := fun i =>
    C (1-t)*weightedPower b (m+i.val) + C t*MvPolynomial.hsymm (Fin n) U (m+i.val)
  have hf : ∀ i, (f i).IsHomogeneous (m+i.val) := fun i =>
    ((weightedPower_isHomogeneous b (m+i.val)).C_mul (1-t)).add
      ((MvPolynomial.isHomogeneous_hsymm (m+i.val)).C_mul t)
  have hb : ∀ g : G, ∀ i, b ((g : Equiv.Perm (Fin n)) i) = b i := by
    intro g i
    have hc : coefficientClassOf c ((g : Equiv.Perm (Fin n)) i) = coefficientClassOf c i :=
      Subtype.ext (hfix g i)
    simp only [b,hc]
  have hinv : ∀ g : G, ∀ i, MvPolynomial.rename (g : Equiv.Perm (Fin n)) (f i) = f i := by
    intro g i
    simp only [f,map_add,map_mul,MvPolynomial.rename_C,rename_weightedPower (R := U) (g : Equiv.Perm (Fin n)) b (hb g),
      MvPolynomial.rename_hsymm]
  let φ : U →+* K := MvPolynomial.eval (fun a => a.elim 1 Subtype.val)
  let φ₀ : U →+* E := MvPolynomial.eval₂Hom (algebraMap K E)
    (fun a => a.elim 0 (fun b => algebraMap (GroupedCoefficientRing c) E (X b)))
  have hφt : φ t = 1 := MvPolynomial.eval_X _
  have hφ₀t : φ₀ t = 0 := MvPolynomial.eval₂Hom_X' _ _ _
  have hφ₀b : (fun i => φ₀ (b i)) = groupedCoefficient c := by
    funext i
    exact MvPolynomial.eval₂Hom_X' _ _ _
  have hφ : (fun i => MvPolynomial.map φ (f i)) = completeHomogeneousFamily K n m := by
    funext i
    simp only [f, map_add, map_mul, MvPolynomial.map_C, map_sub, map_one,
      hφt, sub_self, map_zero, zero_mul, zero_add, one_mul,
      MvPolynomial.map_hsymm, completeHomogeneousFamily]
  have hφ₀ : (fun i => MvPolynomial.map φ₀ (f i)) =
      (fun i => weightedPower (groupedCoefficient c) (m+i.val)) := by
    funext i
    simp only [f, map_add, map_mul, MvPolynomial.map_C, map_sub, map_one,
      hφ₀t, sub_zero, map_zero, one_mul, zero_mul, add_zero,
      map_weightedPower φ₀ b (m+i.val), hφ₀b]
  have hr : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) K)
      (List.ofFn fun i : Fin n => MvPolynomial.map φ (f i)) := by
    rw [hφ]
    exact complete_homogeneous_isWeaklyRegular K n m hm
  have hr₀ : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) E)
      (List.ofFn fun i : Fin n => MvPolynomial.map φ₀ (f i)) := by
    rw [hφ₀]
    exact hregular
  have h := ordinary_intertwiner_dimension_eq_at_regular_fibers G f m d hf hinv φ φ₀ hr hr₀
    (mapRepresentation (algebraMap K U) τ)
  have hφC : φ.comp (algebraMap K U) = RingHom.id K := by
    ext a
    exact MvPolynomial.eval_C _
  have hφ₀C : φ₀.comp (algebraMap K U) = algebraMap K E := by
    ext a
    exact MvPolynomial.eval₂Hom_C _ _ _
  have hτ : mapRepresentation φ (mapRepresentation (algebraMap K U) τ) = τ := by
    calc
      mapRepresentation φ (mapRepresentation (algebraMap K U) τ) =
          mapRepresentation (φ.comp (algebraMap K U)) τ :=
        mapRepresentation_comp (algebraMap K U) φ τ
      _ = τ := by rw [hφC]; exact mapRepresentation_id τ
  have hτ₀ : mapRepresentation φ₀ (mapRepresentation (algebraMap K U) τ) =
      mapRepresentation (algebraMap K E) τ := by
    calc
      mapRepresentation φ₀ (mapRepresentation (algebraMap K U) τ) =
          mapRepresentation (φ₀.comp (algebraMap K U)) τ :=
        mapRepresentation_comp (algebraMap K U) φ₀ τ
      _ = mapRepresentation (algebraMap K E) τ := by rw [hφ₀C]
  rw [hτ₀, hτ] at h
  have hleft := ordinary_intertwiner_finrank_congr_family (K := E) G hφ₀
    (map_family_invariant G f hinv φ₀)
    (fun g i => rename_weightedPower (R := E) (g : Equiv.Perm (Fin n))
      (groupedCoefficient c) (fun j => groupedCoefficient_permutation (K := K) c
        (g : Equiv.Perm (Fin n)) (hfix g) j) (m+i.val)) d
    (mapRepresentation (algebraMap K E) τ)
  have hright := ordinary_intertwiner_finrank_congr_family (K := K) G hφ
    (map_family_invariant G f hinv φ) (completeHomogeneousFamily_invariant (K := K) G m) d τ
  exact hleft.symm.trans (h.trans hright)

end Field

end PaperVerification.PowerOperators
