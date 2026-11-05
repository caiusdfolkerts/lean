import CommAlg.KoszulComplex.CoefficientProjectiveDimension
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal

/-! Genuine coefficient Koszul rows, their naturality and exactness on free coefficients. -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2500
namespace Characterizations.Resolution
open Classical CategoryTheory CategoryTheory.Limits MvPolynomial CommAlg.Koszul
open scoped BigOperators
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

abbrev KoszulRows (M : Type u) [Zero M] (i : ℕ) :=
  Set.powersetCard V i →₀ M

abbrev rowDifferential (M : Type u) [AddCommGroup M] [Module (MvPolynomial V k) M] (i : ℕ) :
    KoszulRows (V := V) M (i + 1) →ₗ[MvPolynomial V k] KoszulRows (V := V) M i :=
  coordinateDifferential (X : V → MvPolynomial V k) (ModuleCat.of (MvPolynomial V k) M) i

abbrev mapRows {M N : Type u} [AddCommGroup M] [Module (MvPolynomial V k) M]
    [AddCommGroup N] [Module (MvPolynomial V k) N]
    (f : M →ₗ[MvPolynomial V k] N) (i : ℕ) :
    KoszulRows (V := V) M i →ₗ[MvPolynomial V k] KoszulRows (V := V) N i :=
  Finsupp.mapRange.linearMap f

@[simp] lemma mapRows_apply {M N : Type u} [AddCommGroup M] [Module (MvPolynomial V k) M]
    [AddCommGroup N] [Module (MvPolynomial V k) N]
    (f : M →ₗ[MvPolynomial V k] N) (i : ℕ) (z : KoszulRows (V := V) M i) (s) :
    mapRows f i z s = f (z s) := rfl

@[simp] lemma mapRows_single {M N : Type u} [AddCommGroup M] [Module (MvPolynomial V k) M]
    [AddCommGroup N] [Module (MvPolynomial V k) N]
    (f : M →ₗ[MvPolynomial V k] N) (i : ℕ) (s : Set.powersetCard V i) (m : M) :
    mapRows f i (Finsupp.single s m) = Finsupp.single s (f m) := by
  exact Finsupp.mapRange_single (hf := f.map_zero)

lemma rowDifferential_natural {M N : Type u} [AddCommGroup M] [Module (MvPolynomial V k) M]
    [AddCommGroup N] [Module (MvPolynomial V k) N]
    (f : M →ₗ[MvPolynomial V k] N) (i : ℕ) (z : KoszulRows (V := V) M (i + 1)) :
    rowDifferential (V := V) (k := k) N i (mapRows f (i + 1) z) = mapRows f i (rowDifferential (V := V) (k := k) M i z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | single s m =>
      rw [mapRows_single, coordinateDifferential_single, coordinateDifferential_single, map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [mapRows_single]
      congr 1
      simp only [map_smul, map_zsmul_unit]

lemma rowDifferential_square {M : Type u} [AddCommGroup M] [Module (MvPolynomial V k) M]
    (i : ℕ) (z : KoszulRows (V := V) M (i + 2)) :
    rowDifferential (V := V) (k := k) M i (rowDifferential (V := V) (k := k) M (i + 1) z) = 0 :=
  LinearMap.congr_fun (coordinateDifferential_comp X (ModuleCat.of (MvPolynomial V k) M) i) z

variable {J : Type}

def HomogeneousRows (i t : ℕ) (z : KoszulRows (V := V) (J → MvPolynomial V k) i) : Prop :=
  ∀ s j, (z s j).IsHomogeneous t

lemma homogeneousRows_zero (i t : ℕ) :
    HomogeneousRows (V := V) (k := k) (J := J) i t 0 := fun _ _ => (homogeneousSubmodule V k t).zero_mem

lemma homogeneousRows_differential {i t : ℕ}
    {z : KoszulRows (V := V) (J → MvPolynomial V k) (i + 1)}
    (hz : HomogeneousRows (i + 1) t z) :
    HomogeneousRows i (t + 1) (rowDifferential (V := V) (k := k) (J → MvPolynomial V k) i z) := by
  intro a b
  have hre : z = ∑ s ∈ z.support, Finsupp.single s (z s) := by
    exact (Finsupp.sum_single z).symm
  rw [hre, map_sum]
  simp only [Finsupp.finsetSum_apply, Finset.sum_apply]
  apply IsHomogeneous.sum
  intro s hs
  rw [coordinateDifferential_single]
  simp only [Finsupp.finsetSum_apply, Finset.sum_apply]
  apply IsHomogeneous.sum
  intro j hj
  by_cases he : eraseIndex s j = a
  · simp only [Finsupp.single_apply, he, ↓reduceIte, Pi.smul_apply, smul_eq_mul]
    have hsign : ((TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val) • z s b).IsHomogeneous t := by
      rcases Int.units_eq_one_or (TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val) with h | h
      · rw [h]
        simpa only [one_smul] using hz s b
      · rw [h]
        simpa only [Units.smul_def, Units.val_neg, Units.val_one, neg_one_zsmul] using (hz s b).neg
    simpa [Nat.add_comm] using (isHomogeneous_X (R := k) j.val).mul hsign
  · simp only [Finsupp.single_apply, he, ↓reduceIte, Pi.zero_apply]
    exact (homogeneousSubmodule V k _).zero_mem

variable [Nontrivial k] [Fintype J]

/-- Exactness here is transported from the actual regular Koszul complex tensored
with the actual finite free coefficient module. -/
lemma freeRows_exact (i : ℕ)
    (z : KoszulRows (V := V) (J → MvPolynomial V k) (i + 1))
    (hz : rowDifferential (V := V) (k := k) (J → MvPolynomial V k) i z = 0) :
    ∃ w, rowDifferential (V := V) (k := k) (J → MvPolynomial V k) (i + 1) w = z := by
  let M := ModuleCat.of (MvPolynomial V k) (J → MvPolynomial V k)
  have hK : (koszulComplex (Fintype.linearCombination (MvPolynomial V k) X)).ExactAt (i + 1) :=
    (koszulComplex.exactAt_of_isRegular (finiteVariableList (V := V) (k := k))
      finite_variables_regular (i + 1) (by omega)).of_iso finiteVariableKoszulIso
  have hF : (familyCoefficientComplex (X : V → MvPolynomial V k) M).ExactAt (i + 1) := by
    change ((koszulComplex (Fintype.linearCombination (MvPolynomial V k) X)).sc (i + 1)).map
      (CategoryTheory.MonoidalCategory.tensorRight M) |>.Exact
    exact Module.Flat.rTensor_shortComplex_exact M _ hK
  have hC := hF.of_iso (coordinateComplexIso X M)
  rw [HomologicalComplex.exactAt_iff' _ (i + 2) (i + 1) i (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_range_eq_ker] at hC
  change LinearMap.range (ModuleCat.Hom.hom ((coordinateComplex X M).d (i + 2) (i + 1))) =
    LinearMap.ker (ModuleCat.Hom.hom ((coordinateComplex X M).d (i + 1) i)) at hC
  rw [coordinateComplex_d, coordinateComplex_d] at hC
  change LinearMap.range (rowDifferential (V := V) (k := k) (J → MvPolynomial V k) (i + 1)) =
    LinearMap.ker (rowDifferential (V := V) (k := k) (J → MvPolynomial V k) i) at hC
  have hm : z ∈ LinearMap.range (rowDifferential (V := V) (k := k) (J → MvPolynomial V k) (i + 1)) := by
    rw [hC]
    exact hz
  exact hm

lemma homogeneous_mem_variables {f : MvPolynomial V k} {t : ℕ}
    (hf : f.IsHomogeneous t) (ht : 0 < t) : f ∈ idealOfVars V k := by
  rw [idealOfVars_eq_restrictSupportIdeal]
  intro a ha
  have he : a.degree = t := by
    simpa only [← Finsupp.degree_apply] using (hf.degree_eq_sum_deg_support ha).symm
  change 1 ≤ a.degree
  omega

lemma rowDifferential_singleton (i : V) (m : J → MvPolynomial V k) :
    rowDifferential (V := V) (k := k) (J → MvPolynomial V k) 0
      (Finsupp.single (⟨{i}, by simp⟩ : Set.powersetCard V 1) m) =
      Finsupp.single (⟨∅, by simp⟩ : Set.powersetCard V 0) ((X i : MvPolynomial V k) • m) := by
  rw [coordinateDifferential_single]
  have hsub : ∀ j : {j // j ∈ ({i} : Finset V)}, j.val = i := fun j => Finset.mem_singleton.mp j.property
  have he : ∀ j : {j // j ∈ ({i} : Finset V)},
      eraseIndex (⟨{i}, by simp⟩ : Set.powersetCard V 1) j = ⟨∅, by simp⟩ := by
    intro j
    apply Subtype.ext
    simp [eraseIndex, hsub j]
  simp only [he, hsub]
  rw [TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt]
  have hf : ({i} : Finset V).filter (fun j => j < i) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    obtain ⟨hj, hlt⟩ := Finset.mem_filter.mp hj
    have he := Finset.mem_singleton.mp hj
    exact (lt_irrefl i) (he ▸ hlt)
  simp only [hf, Finset.card_empty, pow_zero, one_smul]
  simp

/-- Positive homogeneous polynomial coefficients vanish in zeroth free Koszul homology. -/
lemma freeRows_zero_boundary {t : ℕ} (ht : 0 < t)
    (z : KoszulRows (V := V) (J → MvPolynomial V k) 0)
    (hz : HomogeneousRows 0 t z) :
    ∃ w, rowDifferential (V := V) (k := k) (J → MvPolynomial V k) 0 w = z := by
  let e : Set.powersetCard V 0 := ⟨∅, by simp⟩
  have hex : ∀ j : J, ∃ c : V → MvPolynomial V k, ∑ v, c v * X v = z e j := by
    intro j
    exact Ideal.mem_span_range_iff_exists_fun.mp (homogeneous_mem_variables (hz e j) ht)
  choose c hc using hex
  refine ⟨∑ v : V, Finsupp.single (⟨{v}, by simp⟩ : Set.powersetCard V 1) (fun j => c j v), ?_⟩
  rw [map_sum]
  simp_rw [rowDifferential_singleton]
  apply Finsupp.ext
  intro s
  funext j
  have hs : s = e := Subtype.ext (Finset.card_eq_zero.mp s.property)
  subst s
  simp only [e, Finsupp.finsetSum_apply, Finsupp.single_eq_same, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  simpa only [mul_comm] using hc j

end Characterizations.Resolution
