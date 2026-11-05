import CommAlg.KoszulComplex.MonomialBasis
import CommAlg.KoszulComplex.CoefficientTor

/-! # The actual Koszul differential preserves the standard multigrading -/

noncomputable section

set_option maxHeartbeats 200000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false

namespace CommAlg.Koszul

open Classical MvPolynomial CommAlg.Polymatroid CategoryTheory

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

abbrev monomialDifferential (B : Family V) (i : ℕ) :
    (Set.powersetCard V (i + 1) →₀ (monomialIdeal k B)) →ₗ[k]
      (Set.powersetCard V i →₀ (monomialIdeal k B)) :=
  (coordinateDifferential (X : V → MvPolynomial V k)
    (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)) i).restrictScalars k

/-- A term obtained by removing one exterior variable and multiplying the coefficient by it. -/
def differentialIndex {B : Family V} {i : ℕ} (t : MonomialIndex B (i + 1))
    (j : {j // j ∈ t.1.val}) : MonomialIndex B i :=
  ⟨eraseIndex t.1 j, ⟨t.2.val + Finsupp.single j.val 1, by
    obtain ⟨b, hb, hba⟩ := t.2.property
    exact ⟨b, hb, hba.trans (le_add_of_nonneg_right (zero_le))⟩⟩⟩

lemma differentialIndex_degree {B : Family V} {i : ℕ} (t : MonomialIndex B (i + 1))
    (j : {j // j ∈ t.1.val}) :
    monomialDegree (differentialIndex t j) = monomialDegree t := by
  change (t.2.val + Finsupp.single j.val 1) + faceExponent (t.1.val.erase j.val) = _
  rw [add_assoc, add_comm (Finsupp.single j.val 1), faceExponent_erase_add j.property]
  rfl

lemma monomialBasis_mul_variable (B : Family V) (a : {a : Exponent V // Contains B a})
    (j : V) (ha : Contains B (a.val + Finsupp.single j 1)) :
    (X j : MvPolynomial V k) • monomialBasis (k := k) B a =
      monomialBasis (k := k) B ⟨a.val + Finsupp.single j 1, ha⟩ := by
  apply Subtype.ext
  change X j * (monomialBasis (k := k) B a).val = _
  rw [monomialBasis_val, monomialBasis_val, X, monomial_mul_monomial]
  simp [add_comm]

lemma monomialDifferential_basis (B : Family V) (i : ℕ) (t : MonomialIndex B (i + 1)) :
    monomialDifferential (k := k) B i (monomialCoefficientBasis (k := k) B (i + 1) t) =
      ∑ j : {j // j ∈ t.1.val}, TauCeti.ExteriorAlgebra.basisEraseSign j.val t.1.val •
        monomialCoefficientBasis (k := k) B i (differentialIndex t j) := by
  rcases t with ⟨s, a⟩
  rw [monomialCoefficientBasis_apply]
  change coordinateDifferential (X : V → MvPolynomial V k)
    (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)) i
    (Finsupp.single s (monomialBasis (k := k) B a)) = _
  rw [coordinateDifferential_single]
  apply Finset.sum_congr rfl
  intro j hj
  change Finsupp.single (eraseIndex s j)
    (X j.val • (TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val • monomialBasis (k := k) B a)) = _
  rw [smul_comm (X j.val)]
  rw [monomialBasis_mul_variable (k := k) B a j.val (differentialIndex (B := B) ⟨s, a⟩ j).2.property]
  simp [differentialIndex, monomialCoefficientBasis_apply, Finsupp.smul_single]

lemma monomialDifferential_comp (B : Family V) (i : ℕ) :
    monomialDifferential (k := k) B i ∘ₗ monomialDifferential (k := k) B (i + 1) = 0 := by
  apply LinearMap.ext
  intro z
  exact LinearMap.congr_fun (underlyingDifferential_comp (k := k) B i) z

lemma monomialDifferential_homogeneous (B : Family V) (a : Exponent V) (i : ℕ)
    {z : Set.powersetCard V (i + 1) →₀ (monomialIdeal k B)}
    (hz : z ∈ homogeneousPiece (k := k) B a (i + 1)) :
    monomialDifferential (k := k) B i z ∈ homogeneousPiece (k := k) B a i := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨t, ht, rfl⟩ := hz
    rw [monomialDifferential_basis]
    apply Submodule.sum_mem
    intro j hj
    apply (Submodule.smul_mem_iff' _ (TauCeti.ExteriorAlgebra.basisEraseSign j.val t.1.val)).2
    exact Submodule.subset_span
      ⟨differentialIndex t j, (differentialIndex_degree t j).trans ht, rfl⟩
  | zero => simpa only [map_zero] using (Submodule.zero_mem (homogeneousPiece (k := k) B a i))
  | add z w hz hw ihz ihw => simpa using Submodule.add_mem _ ihz ihw
  | smul c z hz ih => simpa using Submodule.smul_mem _ c ih

lemma homogeneousProjection_differential (B : Family V) (a : Exponent V) (i : ℕ) :
    homogeneousProjection (k := k) B a i ∘ₗ monomialDifferential (k := k) B i =
      monomialDifferential (k := k) B i ∘ₗ homogeneousProjection (k := k) B a (i + 1) := by
  apply (monomialCoefficientBasis (k := k) B (i + 1)).ext
  intro t
  change homogeneousProjection (k := k) B a i
    (monomialDifferential B i (monomialCoefficientBasis B (i + 1) t)) =
    monomialDifferential B i (homogeneousProjection B a (i + 1)
      (monomialCoefficientBasis B (i + 1) t))
  have hm : monomialDifferential (k := k) B i (monomialCoefficientBasis B (i + 1) t) ∈
      homogeneousPiece B (monomialDegree t) i :=
    monomialDifferential_homogeneous B _ i (Grading.basis_mem_piece _ _ t)
  change Grading.projection _ _ a _ = monomialDifferential (k := k) B i
    (Grading.projection _ _ a ((monomialCoefficientBasis B (i + 1)) t))
  rw [Grading.projection_basis]
  by_cases ht : monomialDegree t = a
  · rw [if_pos ht]
    exact Grading.projection_eq_self (ht ▸ hm)
  · rw [if_neg ht, map_zero]
    exact Grading.projection_eq_zero (Ne.symm ht) hm

/-- Restricting the actual Koszul differential to its genuine degree component. -/
def homogeneousDifferential (B : Family V) (a : Exponent V) (i : ℕ) :
    homogeneousPiece (k := k) B a (i + 1) →ₗ[k] homogeneousPiece (k := k) B a i :=
  ((monomialDifferential (k := k) B i).domRestrict (homogeneousPiece (k := k) B a (i + 1))).codRestrict _
    (fun z => monomialDifferential_homogeneous B a i z.property)

lemma homogeneousDifferential_comp (B : Family V) (a : Exponent V) (i : ℕ) :
    homogeneousDifferential (k := k) B a i ∘ₗ homogeneousDifferential (k := k) B a (i + 1) = 0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact LinearMap.congr_fun (monomialDifferential_comp B i) z.val

/-- The actual multidegree subcomplex of the tensor Koszul resolution. -/
def homogeneousComplex (B : Family V) (a : Exponent V) :
    ChainComplex (ModuleCat.{u} k) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of k (homogeneousPiece (k := k) B a i))
    (fun i => ModuleCat.ofHom (homogeneousDifferential (k := k) B a i))
    (fun i => ModuleCat.hom_ext (homogeneousDifferential_comp B a i))

@[simp] lemma homogeneousComplex_d (B : Family V) (a : Exponent V) (i : ℕ) :
    (homogeneousComplex (k := k) B a).d (i + 1) i =
      ModuleCat.ofHom (homogeneousDifferential (k := k) B a i) := by
  simp [homogeneousComplex]

end CommAlg.Koszul
