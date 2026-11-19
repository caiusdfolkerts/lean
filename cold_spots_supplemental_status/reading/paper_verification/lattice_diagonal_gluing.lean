module

public import PaperVerification.LatticeCosetProjection
public import PaperVerification.LatticeGluing
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

/-!
# Diagonal gluing for arbitrary finite-index lattice inclusions

This file connects the general finite-profile inequality with actual lattice
Gaussian sums. The index set is the genuine quotient of `M` by `L`; its chosen
representatives are used only to write the profiles. The glued point set itself
is defined independently as pairs in `M` whose difference lies in `L`.

Convergence follows from lattice discreteness. The positivity of the smaller
lattice's minimum is proved from its attainment. The final theorem assumes only
the finite-index inclusion, a positive parameter, and the two attained minima
specified in Proposition 7.1; it does not assume any Gaussian factorization,
coset-coverage statement, or equality criterion.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

variable {n : ℕ}

/-- The actual quotient `M/L`, formed inside the subtype `M`. -/
abbrev LatticeGlueQuotient
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) :=
  M ⧸ L.comap M.subtype

/-- A representative chosen from the actual quotient class. -/
def latticeGlueRepresentative
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (q : LatticeGlueQuotient L M) : EuclideanSpace ℝ (Fin n) :=
  q.out.val

/-- Distinct quotient classes yield distinct lattice cosets. -/
theorem latticeGlueRepresentative_distinct
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) :
    Pairwise (fun q q' : LatticeGlueQuotient L M =>
      latticeGlueRepresentative L M q - latticeGlueRepresentative L M q' ∉ L) := by
  intro q q' hne hmem
  apply hne
  have hm : q.out - q'.out ∈ L.comap M.subtype := hmem
  have heq : (Submodule.Quotient.mk q.out : LatticeGlueQuotient L M) =
      Submodule.Quotient.mk q'.out := (Submodule.Quotient.eq _).mpr hm
  simpa only [Submodule.Quotient.mk_out] using heq

/-- The disjointness needed for reindexing is deduced from the quotient, not
assumed for a list of representatives. -/
theorem latticeGlueCosets_pairwise_disjoint
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) :
    Pairwise (fun q q' : LatticeGlueQuotient L M => Disjoint
      (euclideanLatticeCoset L (latticeGlueRepresentative L M q))
      (euclideanLatticeCoset L (latticeGlueRepresentative L M q'))) :=
  euclideanLatticeCoset_pairwise_disjoint L (latticeGlueRepresentative L M)
    (latticeGlueRepresentative_distinct L M)

/-- Exact coverage of the larger lattice by the genuine quotient cosets. -/
theorem latticeGlueCosets_union
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (hLM : L ≤ M) :
    (⋃ q : LatticeGlueQuotient L M,
      euclideanLatticeCoset L (latticeGlueRepresentative L M q)) =
        euclideanLatticeCoset M 0 := by
  ext x
  constructor
  · intro hx
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx
    have hq' : WithLp.toLp 2 x - latticeGlueRepresentative L M q ∈ L := hq
    have hm := M.add_mem (hLM hq') q.out.property
    change WithLp.toLp 2 x - 0 ∈ M
    simpa only [sub_add_cancel, sub_zero, latticeGlueRepresentative] using hm
  · intro hx
    have hxM : WithLp.toLp 2 x ∈ M := by
      simpa only [euclideanLatticeCoset, Set.mem_setOf_eq, sub_zero] using hx
    let v : M := ⟨WithLp.toLp 2 x, hxM⟩
    let q : LatticeGlueQuotient L M := Submodule.Quotient.mk v
    refine Set.mem_iUnion.mpr ⟨q, ?_⟩
    change v - q.out ∈ L.comap M.subtype
    exact (Submodule.Quotient.eq _).mp (Submodule.Quotient.mk_out q).symm

/-- The glued lattice is the actual set of pairs in `M` congruent modulo `L`.
This definition contains no Gaussian or minimizing-set condition. -/
def diagonalLatticeGlue
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : Set (Fin (n + n) → ℝ) :=
  {z | ∃ x y : Fin n → ℝ, z = Fin.append x y ∧
    WithLp.toLp 2 x ∈ M ∧ WithLp.toLp 2 y ∈ M ∧
    WithLp.toLp 2 x - WithLp.toLp 2 y ∈ L}

/-- Equality with the literal diagonal coset union in Proposition 7.1. -/
theorem diagonalLatticeGlue_eq_orthogonalGlue
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (hLM : L ≤ M) :
    diagonalLatticeGlue L M =
      orthogonalGlue
        (fun q : LatticeGlueQuotient L M =>
          euclideanLatticeCoset L (latticeGlueRepresentative L M q))
        (fun q : LatticeGlueQuotient L M =>
          euclideanLatticeCoset L (latticeGlueRepresentative L M q)) := by
  ext z
  constructor
  · rintro ⟨x, y, hz, hxM, hyM, hxy⟩
    have hx : x ∈ euclideanLatticeCoset M 0 := by
      simpa only [euclideanLatticeCoset, Set.mem_setOf_eq, sub_zero] using hxM
    rw [← latticeGlueCosets_union L M hLM] at hx
    obtain ⟨q, hqx⟩ := Set.mem_iUnion.mp hx
    have hqy : y ∈ euclideanLatticeCoset L (latticeGlueRepresentative L M q) := by
      have hm := L.sub_mem hqx hxy
      change WithLp.toLp 2 y - latticeGlueRepresentative L M q ∈ L
      convert hm using 1
      abel
    exact ⟨q, x, hqx, y, hqy, hz⟩
  · rintro ⟨q, x, hx, y, hy, hz⟩
    have hxM : x ∈ euclideanLatticeCoset M 0 := by
      rw [← latticeGlueCosets_union L M hLM]
      exact Set.mem_iUnion.mpr ⟨q, hx⟩
    have hyM : y ∈ euclideanLatticeCoset M 0 := by
      rw [← latticeGlueCosets_union L M hLM]
      exact Set.mem_iUnion.mpr ⟨q, hy⟩
    refine ⟨x, y, hz, ?_, ?_, ?_⟩
    · simpa only [euclideanLatticeCoset, Set.mem_setOf_eq, sub_zero] using hxM
    · simpa only [euclideanLatticeCoset, Set.mem_setOf_eq, sub_zero] using hyM
    · have hm := L.sub_mem hx hy
      convert hm using 1
      abel

/-- Translation of the lattice coset is exactly translation of the argument.
The equality is obtained by bijective reindexing of actual point subtypes. -/
theorem euclideanLatticeCoset_gaussian_shift
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) (α : ℝ) (x : Fin n → ℝ) :
    setGaussian (euclideanLatticeCoset L a) α x =
      setGaussian (euclideanLatticeCoset L 0) α (x - WithLp.ofLp a) := by
  unfold setGaussian
  rw [← (euclideanLatticeCosetEquiv L a).tsum_eq
    (fun z : euclideanLatticeCoset L a => Real.exp (-α * sqDist z.val x)),
    ← (euclideanLatticeCosetEquiv L 0).tsum_eq
      (fun z : euclideanLatticeCoset L 0 =>
        Real.exp (-α * sqDist z.val (x - WithLp.ofLp a)))]
  apply tsum_congr
  intro z
  rw [sqDist_euclideanLatticeCosetEquiv, sqDist_euclideanLatticeCosetEquiv]
  simp only [WithLp.toLp_sub, WithLp.toLp_ofLp, sub_zero]

/-- Changing a representative within its coset leaves the point set unchanged. -/
theorem euclideanLatticeCoset_eq_of_sub_mem
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (a b : EuclideanSpace ℝ (Fin n)) (hab : a - b ∈ L) :
    euclideanLatticeCoset L a = euclideanLatticeCoset L b := by
  ext x
  constructor
  · intro hx
    have hm := L.add_mem hx hab
    change WithLp.toLp 2 x - b ∈ L
    convert hm using 1
    abel
  · intro hx
    have hm := L.sub_mem hx hab
    change WithLp.toLp 2 x - a ∈ L
    convert hm using 1
    abel

/-- In particular the shifted Gaussian profile is independent of representative. -/
theorem latticeGaussian_shift_eq_of_sub_mem
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (a b : EuclideanSpace ℝ (Fin n)) (hab : a - b ∈ L)
    (α : ℝ) (x : Fin n → ℝ) :
    setGaussian (euclideanLatticeCoset L 0) α (x - WithLp.ofLp a) =
      setGaussian (euclideanLatticeCoset L 0) α (x - WithLp.ofLp b) := by
  rw [← euclideanLatticeCoset_gaussian_shift, ← euclideanLatticeCoset_gaussian_shift,
    euclideanLatticeCoset_eq_of_sub_mem L a b hab]

/-- Convergence for the finite-index extension is derived from the smaller
lattice's convergence and the proved disjoint coset partition. -/
theorem summable_gaussian_lattice_extension
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (hLM : L ≤ M) [Fintype (LatticeGlueQuotient L M)]
    (α : ℝ) (hα : 0 < α) (x : Fin n → ℝ) :
    Summable (fun z : euclideanLatticeCoset M 0 => Real.exp (-α * sqDist z.val x)) := by
  rw [← latticeGlueCosets_union L M hLM]
  exact summable_gaussian_disjoint_finite_union _ (latticeGlueCosets_pairwise_disjoint L M)
    α x (fun q => summable_gaussian_euclideanLatticeCoset L
      (latticeGlueRepresentative L M q) α hα x)

/-- The sum of the literal shifted `L` profiles is the ordinary `M` Gaussian. -/
theorem latticeGlue_profile_sum
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (hLM : L ≤ M) [Fintype (LatticeGlueQuotient L M)]
    (α : ℝ) (hα : 0 < α) (x : Fin n → ℝ) :
    setGaussian (euclideanLatticeCoset M 0) α x =
      ∑ q : LatticeGlueQuotient L M,
        setGaussian (euclideanLatticeCoset L 0) α
          (x - WithLp.ofLp (latticeGlueRepresentative L M q)) := by
  rw [← latticeGlueCosets_union L M hLM,
    setGaussian_disjoint_finite_union _ (latticeGlueCosets_pairwise_disjoint L M)
      α x (fun q => summable_gaussian_euclideanLatticeCoset L
        (latticeGlueRepresentative L M q) α hα x)]
  apply Finset.sum_congr rfl
  intro q _
  exact euclideanLatticeCoset_gaussian_shift L (latticeGlueRepresentative L M q) α x

/-- Convergence of the actual glued Gaussian at every pair of real points. -/
theorem summable_gaussian_diagonalLatticeGlue
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (hLM : L ≤ M) [Fintype (LatticeGlueQuotient L M)]
    (α : ℝ) (hα : 0 < α) (x y : Fin n → ℝ) :
    Summable (fun z : diagonalLatticeGlue L M =>
      Real.exp (-α * sqDist z.val (Fin.append x y))) := by
  rw [diagonalLatticeGlue_eq_orthogonalGlue L M hLM]
  exact summable_gaussian_orthogonalGlue _ _ (latticeGlueCosets_pairwise_disjoint L M)
    α x y
    (fun q => summable_gaussian_euclideanLatticeCoset L
      (latticeGlueRepresentative L M q) α hα x)
    (fun q => summable_gaussian_euclideanLatticeCoset L
      (latticeGlueRepresentative L M q) α hα y)

/-- Every ambient point has the two coordinate blocks used above. Thus the
convergence theorem covers the whole ambient Euclidean space. -/
theorem summable_gaussian_diagonalLatticeGlue_all
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (hLM : L ≤ M) [Fintype (LatticeGlueQuotient L M)]
    (α : ℝ) (hα : 0 < α) (z : Fin (n + n) → ℝ) :
    Summable (fun v : diagonalLatticeGlue L M => Real.exp (-α * sqDist v.val z)) := by
  have hs := summable_gaussian_diagonalLatticeGlue L M hLM α hα
    (fun i => z (Fin.castAdd n i)) (fun i => z (Fin.natAdd n i))
  simpa only [Fin.append_castAdd_natAdd] using hs

/-- The displayed Gaussian factorization in the proof of Proposition 7.1. -/
theorem diagonalLatticeGlue_gaussian_factorization
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (hLM : L ≤ M) [Fintype (LatticeGlueQuotient L M)]
    (α : ℝ) (hα : 0 < α) (x y : Fin n → ℝ) :
    setGaussian (diagonalLatticeGlue L M) α (Fin.append x y) =
      ∑ q : LatticeGlueQuotient L M,
        setGaussian (euclideanLatticeCoset L 0) α
          (x - WithLp.ofLp (latticeGlueRepresentative L M q)) *
        setGaussian (euclideanLatticeCoset L 0) α
          (y - WithLp.ofLp (latticeGlueRepresentative L M q)) := by
  rw [diagonalLatticeGlue_eq_orthogonalGlue L M hLM,
    setGaussian_orthogonalGlue _ _ (latticeGlueCosets_pairwise_disjoint L M)
      α x y
      (fun q => summable_gaussian_euclideanLatticeCoset L
        (latticeGlueRepresentative L M q) α hα x)
      (fun q => summable_gaussian_euclideanLatticeCoset L
        (latticeGlueRepresentative L M q) α hα y)]
  apply Finset.sum_congr rfl
  intro q _
  exact congrArg₂ (fun a b : ℝ => a * b)
    (euclideanLatticeCoset_gaussian_shift L (latticeGlueRepresentative L M q) α x)
    (euclideanLatticeCoset_gaussian_shift L (latticeGlueRepresentative L M q) α y)

/-- An attained lattice Gaussian minimum is strictly positive. -/
theorem latticeGaussian_minimum_pos
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (α : ℝ) (hα : 0 < α) (κ : ℝ)
    (hκ : IsLeast (Set.range (setGaussian (euclideanLatticeCoset L 0) α)) κ) :
    0 < κ := by
  obtain ⟨x, hx⟩ := hκ.1
  rw [← hx]
  exact setGaussian_pos_of_nonempty (euclideanLatticeCoset L 0) α x
    (euclideanLatticeCoset_nonempty L 0)
    (summable_gaussian_euclideanLatticeCoset L 0 α hα x)

/-- An attained least value identifies the full global minimum set. -/
theorem isColdSpot_iff_gaussian_eq_of_isLeast
    (S : Set (Fin n → ℝ)) (α κ : ℝ)
    (hκ : IsLeast (Set.range (setGaussian S α)) κ) (x : Fin n → ℝ) :
    IsColdSpot S α x ↔ setGaussian S α x = κ := by
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := hκ.1
    exact le_antisymm (by simpa only [hz] using hx z) (hκ.2 ⟨x, rfl⟩)
  · intro hx y
    rw [hx]
    exact hκ.2 ⟨y, rfl⟩

/-- Full arbitrary-finite-index diagonal gluing, Proposition 7.1. The index is
the cardinality of the actual quotient, the minima are actual attained Gaussian
minima, and the conclusion gives the exact global equality criterion. -/
theorem lattice_diagonal_gluing
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (hLM : L ≤ M) [Finite (LatticeGlueQuotient L M)]
    (α : ℝ) (hα : 0 < α) (κ σ : ℝ)
    (hκ : IsLeast (Set.range (setGaussian (euclideanLatticeCoset L 0) α)) κ)
    (hσ : IsLeast (Set.range (setGaussian (euclideanLatticeCoset M 0) α)) σ)
    (x y : Fin n → ℝ) :
    (2 * κ * σ - (Nat.card (LatticeGlueQuotient L M) : ℝ) * κ ^ 2 ≤
      setGaussian (diagonalLatticeGlue L M) α (Fin.append x y)) ∧
    (setGaussian (diagonalLatticeGlue L M) α (Fin.append x y) =
        2 * κ * σ - (Nat.card (LatticeGlueQuotient L M) : ℝ) * κ ^ 2 ↔
      IsColdSpot (euclideanLatticeCoset M 0) α x ∧
      IsColdSpot (euclideanLatticeCoset M 0) α y ∧
      ∀ q : LatticeGlueQuotient L M,
        IsColdSpot (euclideanLatticeCoset L 0) α
          (x - WithLp.ofLp (latticeGlueRepresentative L M q)) ∨
        IsColdSpot (euclideanLatticeCoset L 0) α
          (y - WithLp.ofLp (latticeGlueRepresentative L M q))) := by
  classical
  letI : Fintype (LatticeGlueQuotient L M) := Fintype.ofFinite _
  let u (q : LatticeGlueQuotient L M) :=
    setGaussian (euclideanLatticeCoset L 0) α
      (x - WithLp.ofLp (latticeGlueRepresentative L M q))
  let v (q : LatticeGlueQuotient L M) :=
    setGaussian (euclideanLatticeCoset L 0) α
      (y - WithLp.ofLp (latticeGlueRepresentative L M q))
  have hκpos := latticeGaussian_minimum_pos L α hα κ hκ
  have hu (q : LatticeGlueQuotient L M) : κ ≤ u q := hκ.2 ⟨_, rfl⟩
  have hv (q : LatticeGlueQuotient L M) : κ ≤ v q := hκ.2 ⟨_, rfl⟩
  have hsumx : (∑ q, u q) = setGaussian (euclideanLatticeCoset M 0) α x :=
    (latticeGlue_profile_sum L M hLM α hα x).symm
  have hsumy : (∑ q, v q) = setGaussian (euclideanLatticeCoset M 0) α y :=
    (latticeGlue_profile_sum L M hLM α hα y).symm
  have hSu : σ ≤ ∑ q, u q := by rw [hsumx]; exact hσ.2 ⟨x, rfl⟩
  have hSv : σ ≤ ∑ q, v q := by rw [hsumy]; exact hσ.2 ⟨y, rfl⟩
  have hfactor : setGaussian (diagonalLatticeGlue L M) α (Fin.append x y) =
      ∑ q, u q * v q := diagonalLatticeGlue_gaussian_factorization L M hLM α hα x y
  constructor
  · rw [hfactor]
    simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using
      PaperVerification.Lattice.diagonal_gluing_bound Finset.univ u v κ σ hκpos.le
        (fun q _ => hu q) (fun q _ => hv q) hSu hSv
  · have heq : (∑ q, u q * v q) =
        2 * κ * σ - (Nat.card (LatticeGlueQuotient L M) : ℝ) * κ ^ 2 ↔
        (∑ q, u q) = σ ∧ (∑ q, v q) = σ ∧ ∀ q, u q = κ ∨ v q = κ := by
      simpa only [Finset.card_univ, Nat.card_eq_fintype_card,
        Finset.mem_univ, forall_true_left] using
        PaperVerification.Lattice.diagonal_gluing_eq_iff Finset.univ u v κ σ hκpos
          (fun q _ => hu q) (fun q _ => hv q) hSu hSv
    rw [hfactor, heq, hsumx, hsumy]
    simp_rw [isColdSpot_iff_gaussian_eq_of_isLeast _ α σ hσ,
      isColdSpot_iff_gaussian_eq_of_isLeast _ α κ hκ, u, v]

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.latticeGlueCosets_union
#print axioms PaperVerification.ColdSpots.diagonalLatticeGlue_gaussian_factorization
#print axioms PaperVerification.ColdSpots.latticeGaussian_minimum_pos
#print axioms PaperVerification.ColdSpots.lattice_diagonal_gluing

