module

public import PaperVerification.FermionCreatorAllDegrees

/-!
# Creator triangularity for the paper's multiplicity weight

Both exterior colors at index `i` receive weight `3^i`. Equal weights are
allowed: the creator transformation has zero entries between distinct modes
of the same weight. The determinant argument therefore separates every
colored wedge, including different colorings of a single multiplicity block.

The initial-ideal assertion in Theorem 8.1 is developed using the actual
exterior coordinates and creator maps.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open scoped BigOperators

variable {R I : Type*} [CommRing R] {k : ℕ}

/-- A repeated numerical rank is allowed when its diagonal block is itself
diagonal. No arbitrary order is imposed on equal-weight colors. -/
theorem triangular_minor_zero_of_weight_with_ties
    (rank : I → ℕ) (A : Matrix I I R)
    (hA : ∀ i j, rank j < rank i → A i j = 0)
    (hEq : ∀ i j, rank i = rank j → i ≠ j → A i j = 0)
    (s t : Fin k → I) (hne : Set.range s ≠ Set.range t)
    (hweight : (∑ i, rank (t i)) ≤ ∑ i, rank (s i)) :
    (Matrix.of fun i j : Fin k ↦ A (s i) (t j)).det = 0 := by
  classical
  rw [Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro σ _
  have hz : ∃ i : Fin k, A (s (σ i)) (t i) = 0 := by
    by_contra h
    push_neg at h
    have hle (i : Fin k) : rank (s (σ i)) ≤ rank (t i) := by
      by_contra hi
      exact h i (hA _ _ (Nat.lt_of_not_ge hi))
    have hsum : (∑ i, rank (s (σ i))) = ∑ i, rank (t i) := by
      apply le_antisymm (Finset.sum_le_sum fun i _ ↦ hle i)
      calc
        (∑ i, rank (t i)) ≤ ∑ i, rank (s i) := hweight
        _ = ∑ i, rank (s (σ i)) :=
          (Equiv.sum_comp σ (fun i ↦ rank (s i))).symm
    have heq (i : Fin k) : s (σ i) = t i := by
      have hr : rank (s (σ i)) = rank (t i) :=
        (Finset.sum_eq_sum_iff_of_le (fun j _ ↦ hle j)).mp hsum i
          (Finset.mem_univ i)
      by_contra hi
      exact h i (hEq _ _ hr hi)
    apply hne
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      refine ⟨σ.symm i,?_⟩
      simpa only [Equiv.apply_symm_apply] using (heq (σ.symm i)).symm
    · rintro ⟨i,rfl⟩
      exact ⟨σ i,heq i⟩
  obtain ⟨i,hi⟩ := hz
  rw [Finset.prod_eq_zero (Finset.mem_univ i) hi,smul_zero]

theorem exterior_map_coordinate_zero_with_ties
    {V : Type*} [AddCommGroup V] [Module R V] [LinearOrder I] [Fintype I]
    (b : Module.Basis I R V) (f : V →ₗ[R] V) (rank : I → ℕ)
    (hf : ∀ i j, rank j < rank i → b.repr (f (b j)) i = 0)
    (hEq : ∀ i j, rank i = rank j → i ≠ j → b.repr (f (b j)) i = 0)
    (s t : Set.powersetCard I k) (hst : s ≠ t)
    (hweight : exteriorIndexWeight rank t ≤ exteriorIndexWeight rank s) :
    (b.exteriorPower k).repr (exteriorPower.map k f (b.exteriorPower k t)) s = 0 := by
  rw [exterior_map_coordinate_minor]
  apply triangular_minor_zero_of_weight_with_ties rank
    (Matrix.of fun i j ↦ b.repr (f (b j)) i) hf hEq _ _ _ hweight
  intro heq
  apply hst
  apply Subtype.ext
  apply Finset.coe_injective
  simpa only [exteriorIndex_enum_range] using heq

end PaperVerification.Fermion

namespace PaperVerification.Fermion.Exterior

open scoped BigOperators

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}

def modeIndex : OddIndex n → Fin n
  | .inl i => i
  | .inr i => i

def multiplicityModeWeight (j : OddIndex n) : ℕ := 3^(modeIndex j).val

def multiplicityWordWeight (T : Finset (OddIndex n)) : ℕ :=
  ∑ j ∈ T,multiplicityModeWeight j

variable (b : Module.Basis (OddIndex n) R V) (φ β a c : Fin n → R)

theorem prefixCreatorMap_multiplicity_triangular (i j : OddIndex n)
    (hij : multiplicityModeWeight j < multiplicityModeWeight i) :
    b.repr (prefixCreatorMap b φ β a c (b j)) i = 0 := by
  have hindex : (modeIndex j).val < (modeIndex i).val :=
    (Nat.pow_lt_pow_iff_right (by decide : 1 < (3 : ℕ))).mp hij
  rw [prefixCreatorMap_basis]
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          change b.coord (.inl i) (thetaCreatorVector b φ β a (suffixPolynomial φ j)) = 0
          rw [coord_thetaCreatorVector_left,
            suffixPolynomial_eval_above φ j i hindex,mul_zero]
      | inr j => exact coord_xiCreatorVector_left b φ c (suffixPolynomial φ j) i
  | inr i =>
      cases j with
      | inl j => exact coord_thetaCreatorVector_right b φ β a (suffixPolynomial φ j) i
      | inr j =>
          change b.coord (.inr i) (xiCreatorVector b φ c (suffixPolynomial φ j)) = 0
          rw [coord_xiCreatorVector_right,
            suffixPolynomial_eval_above φ j i hindex,mul_zero]

theorem prefixCreatorMap_equal_multiplicity_zero (i j : OddIndex n)
    (hij : multiplicityModeWeight i = multiplicityModeWeight j) (hne : i ≠ j) :
    b.repr (prefixCreatorMap b φ β a c (b j)) i = 0 := by
  have hindex : modeIndex i = modeIndex j := by
    apply Fin.ext
    apply le_antisymm
    · exact (Nat.pow_le_pow_iff_right (by decide : 1 < (3 : ℕ))).mp hij.le
    · exact (Nat.pow_le_pow_iff_right (by decide : 1 < (3 : ℕ))).mp hij.ge
  rw [prefixCreatorMap_basis]
  cases i with
  | inl i =>
      cases j with
      | inl j => exact (hne (congrArg Sum.inl hindex)).elim
      | inr j => exact coord_xiCreatorVector_left b φ c (suffixPolynomial φ j) i
  | inr i =>
      cases j with
      | inl j => exact coord_thetaCreatorVector_right b φ β a (suffixPolynomial φ j) i
      | inr j => exact (hne (congrArg Sum.inr hindex)).elim

local instance FermionMultiplicityTriangular_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective

theorem sum_exteriorEnumeration {M : Type*} [AddCommMonoid M]
    (k : ℕ) (T : Set.powersetCard (OddIndex n) k) (f : OddIndex n → M) :
    (∑ i : Fin k,f (Set.powersetCard.ofFinEmbEquiv.symm T i))=∑ a ∈ T.val,f a := by
  classical
  let e := Set.powersetCard.ofFinEmbEquiv.symm T
  apply Finset.sum_bij (fun i _ ↦ e i)
  · intro i hi
    have hm : e i ∈ Set.range e := ⟨i,rfl⟩
    rw [exteriorIndex_enum_range] at hm
    exact hm
  · intro i hi j hj he
    exact e.injective he
  · intro a ha
    have hm : a ∈ Set.range e := by rw [exteriorIndex_enum_range]; exact ha
    obtain ⟨i,rfl⟩ := hm
    exact ⟨i,Finset.mem_univ i,rfl⟩
  · intro i hi
    rfl

theorem exteriorIndexWeight_multiplicity (k : ℕ)
    (T : Set.powersetCard (OddIndex n) k) :
    exteriorIndexWeight multiplicityModeWeight T=multiplicityWordWeight T.val :=
  sum_exteriorEnumeration k T multiplicityModeWeight

/-- The actual creator has only strictly smaller multiplicity-weight terms
besides its own colored word. -/
theorem prefixCreatorWedge_multiplicity_coordinate_zero
    (S T : Finset (OddIndex n)) (hST : S ≠ T)
    (hweight : multiplicityWordWeight S ≤ multiplicityWordWeight T) :
    b.ExteriorAlgebra.repr
      (prefixCreatorWedge b φ β a c S.card ⟨S,rfl⟩ : ExteriorAlgebra R V) T = 0 := by
  by_cases hc : T.card=S.card
  · rw [show b.ExteriorAlgebra.repr
        (prefixCreatorWedge b φ β a c S.card ⟨S,rfl⟩ : ExteriorAlgebra R V) T =
        (b.exteriorPower S.card).repr
          (prefixCreatorWedge b φ β a c S.card ⟨S,rfl⟩) ⟨T,hc⟩ from
        exteriorPower_coordinate_coe b S.card ⟨T,hc⟩ _]
    apply exterior_map_coordinate_zero_with_ties b (prefixCreatorMap b φ β a c)
      multiplicityModeWeight (prefixCreatorMap_multiplicity_triangular b φ β a c)
      (prefixCreatorMap_equal_multiplicity_zero b φ β a c)
    · exact fun he ↦ hST (congrArg Subtype.val he).symm
    · simpa only [exteriorIndexWeight_multiplicity] using hweight
  · exact exteriorPower_coordinate_coe_of_card_ne b S.card T hc _

end PaperVerification.Fermion.Exterior
