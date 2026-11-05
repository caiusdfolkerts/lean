module
public import Projection.Topology
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Lean.Elab.Tactic.Omega

/-!
# Compactness with a retained coordinate disk

The maximal-minor normalization fixes the complement of fewer than `k`
coordinates. Consequently, every normalized body contains one of finitely many
fixed coordinate disks. This file proves that the resulting family of actual
bodies and marks is compact, and that every member has the dimension required
in Theorem 3.1. No compactness or dimension property is assumed as an axiom.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set Metric Module MeasureTheory Filter
open scoped Topology Pointwise

namespace RankThreeProjection
open VolumePolynomials

/-- The closed disk in the coordinate subspace complementary to `s`. -/
def coordinateDisk {n : ℕ} (s : Finset (Fin n)) (ρ : ℝ) : Set (Space n) :=
  {x | ‖x‖ ≤ ρ ∧ ∀ i ∈ s, x i = 0}

theorem zero_mem_coordinateDisk {n : ℕ} (s : Finset (Fin n)) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (0 : Space n) ∈ coordinateDisk s ρ := ⟨by simpa using hρ, by simp⟩

theorem coordinateDisk_subset_closedBall {n : ℕ} (s : Finset (Fin n)) (ρ : ℝ) :
    coordinateDisk s ρ ⊆ closedBall 0 ρ := fun _ hx => mem_closedBall_zero_iff.mpr hx.1

/-- A fixed coordinate disk forces the literal affine span to contain the
entire complementary coordinate subspace. -/
theorem coordinateDisk_dimension {n : ℕ} (s : Finset (Fin n))
    {ρ : ℝ} (hρ : 0 < ρ) (K : Body n)
    (hK : coordinateDisk s ρ ⊆ (K : Set (Space n))) :
    n - s.card ≤ bodyDimension K := by
  classical
  have hzero : (0 : Space n) ∈ K := hK (zero_mem_coordinateDisk s hρ.le)
  let v : Retained s → Space n := fun i => Pi.single i.val 1
  have hli : LinearIndependent ℝ v := by
    simpa only [v, Function.comp_def, Pi.basisFun_apply] using
      (Pi.basisFun ℝ (Fin n)).linearIndependent.comp
        (fun i : Retained s => i.val) Subtype.val_injective
  have hv : ∀ j, v j ∈ (affineSpan ℝ (K : Set (Space n))).direction := by
    intro j
    have hpoint : ρ • v j ∈ K := by
      apply hK
      refine ⟨?_, ?_⟩
      · simpa only [v, norm_smul, Pi.norm_single, norm_one, mul_one,
          Real.norm_of_nonneg hρ.le] using (le_rfl : ρ ≤ ρ)
      · intro i hi
        have hij : i ≠ j.val := by
          intro heq
          exact j.property (heq ▸ hi)
        simp [v, Pi.single_apply, hij, Ne.symm hij]
    have hd : ρ • v j ∈ (affineSpan ℝ (K : Set (Space n))).direction := by
      simpa only [vsub_eq_sub, sub_zero] using
        AffineSubspace.vsub_mem_direction
          (subset_affineSpan ℝ (K : Set (Space n)) hpoint)
          (subset_affineSpan ℝ (K : Set (Space n)) hzero)
    have hh := (affineSpan ℝ (K : Set (Space n))).direction.smul_mem ρ⁻¹ hd
    simpa only [smul_smul, inv_mul_cancel₀ hρ.ne', one_smul] using hh
  have hspan : Submodule.span ℝ (Set.range v) ≤
      (affineSpan ℝ (K : Set (Space n))).direction := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hv j
  have hdim := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hli] at hdim
  simpa only [Retained, Fintype.card_subtype_compl, Fintype.card_fin,
    Fintype.card_coe, bodyDimension] using hdim

/-- Containing an arbitrary fixed set is a closed condition on convex bodies
in the Hausdorff topology. -/
theorem isClosed_bodies_containing {n : ℕ} (A : Set (Space n)) :
    IsClosed {K : Body n | A ⊆ (K : Set (Space n))} := by
  simp only [Set.subset_def, Set.ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun _hx =>
    (isClosed_compacts_contains x).preimage continuous_bodyToNonemptyCompacts

/-- Bodies between a fixed coordinate disk and a fixed ambient ball. -/
def normalizedBodies {n : ℕ} (s : Finset (Fin n)) (ρ R : ℝ) : Set (Body n) :=
  {K | coordinateDisk s ρ ⊆ (K : Set (Space n)) ∧
    (K : Set (Space n)) ⊆ closedBall 0 R}

theorem isCompact_normalizedBodies {n : ℕ} (s : Finset (Fin n))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (R : ℝ) : IsCompact (normalizedBodies s ρ R) := by
  have hbase := isCompact_bodies_in_compact (isCompact_closedBall (0 : Space n) R)
  have heq : normalizedBodies s ρ R =
      {K : Body n | (0 : Space n) ∈ K ∧ (K : Set (Space n)) ⊆ closedBall 0 R} ∩
      {K : Body n | coordinateDisk s ρ ⊆ (K : Set (Space n))} := by
    ext K
    constructor
    · intro h
      exact ⟨⟨h.1 (zero_mem_coordinateDisk s hρ), h.2⟩, h.1⟩
    · intro h
      exact ⟨h.2, h.1.2⟩
  rw [heq]
  exact hbase.inter_right (isClosed_bodies_containing (coordinateDisk s ρ))

/-- The bounded family used after maximal-minor normalization. The finite
union includes every possible set of fewer than `k` pivot coordinates. -/
def normalizedMarkedFamily (n k : ℕ) (ρ R D : ℝ) :
    Set (Body n × (Fin n → Space n)) :=
  ⋃ s : {s : Finset (Fin n) // s.card < k},
    normalizedBodies s.val ρ R ×ˢ closedBall 0 D

theorem mem_normalizedMarkedFamily_iff {n k : ℕ} {ρ R D : ℝ}
    {p : Body n × (Fin n → Space n)} :
    p ∈ normalizedMarkedFamily n k ρ R D ↔
      ∃ s : Finset (Fin n), s.card < k ∧
        coordinateDisk s ρ ⊆ (p.1 : Set (Space n)) ∧
        (p.1 : Set (Space n)) ⊆ closedBall 0 R ∧ ‖p.2‖ ≤ D := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp h
    exact ⟨s.val, s.property, hs.1.1, hs.1.2, mem_closedBall_zero_iff.mp hs.2⟩
  · rintro ⟨s, hs, hdisk, houter, hmarks⟩
    exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩,
      ⟨⟨hdisk, houter⟩, mem_closedBall_zero_iff.mpr hmarks⟩⟩

theorem isCompact_normalizedMarkedFamily (n k : ℕ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (R D : ℝ) : IsCompact (normalizedMarkedFamily n k ρ R D) := by
  apply isCompact_iUnion
  intro s
  exact (isCompact_normalizedBodies s.val hρ R).prod
    (isCompact_closedBall (0 : Fin n → Space n) D)

/-- The normalized image is compact because the marked mixed-volume map is
continuous on actual bodies and actual segment vectors. -/
theorem isCompact_normalizedMarkedImage (n k : ℕ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (R D : ℝ) :
    IsCompact ((fun p : Body n × (Fin n → Space n) => allMarkedArray (k := k) p.1 p.2) ''
      normalizedMarkedFamily n k ρ R D) :=
  (isCompact_normalizedMarkedFamily n k hρ R D).image continuous_allMarkedArray

/-- Every limit of uniformly normalized marked arrays has an actual marked
representation whose body has affine dimension at least `n - k + 1`.

The hypotheses specify concrete bounds and a literal contained coordinate disk;
they will be supplied by affine normalization and the maximal-minor theorem.
-/
theorem marked_limit_of_bounded_representations {n k : ℕ} (hkn : k ≤ n)
    {ρ R D : ℝ} (hρ : 0 < ρ)
    (p : ℕ → Deleted n k → ℝ) (P : Deleted n k → ℝ)
    (hp : Tendsto p atTop (𝓝 P))
    (hrep : ∀ m, ∃ (K : Body n) (U : Fin n → Space n) (s : Finset (Fin n)),
      s.card < k ∧ coordinateDisk s ρ ⊆ (K : Set (Space n)) ∧
      (K : Set (Space n)) ⊆ closedBall 0 R ∧ ‖U‖ ≤ D ∧ allMarkedArray K U = p m) :
    ∃ (K : Body n) (U : Fin n → Space n),
      n - k + 1 ≤ bodyDimension K ∧ allMarkedArray K U = P := by
  let S := (fun q : Body n × (Fin n → Space n) => allMarkedArray (k := k) q.1 q.2) ''
    normalizedMarkedFamily n k ρ R D
  have hS : IsClosed S := (isCompact_normalizedMarkedImage n k hρ.le R D).isClosed
  have hpS : ∀ m, p m ∈ S := by
    intro m
    obtain ⟨K, U, s, hs, hdisk, houter, hmarks, heq⟩ := hrep m
    exact ⟨(K, U), mem_normalizedMarkedFamily_iff.mpr ⟨s, hs, hdisk, houter, hmarks⟩, heq⟩
  obtain ⟨⟨K, U⟩, hKU, heq⟩ := hS.mem_of_tendsto hp (Eventually.of_forall hpS)
  obtain ⟨s, hs, hdisk, _houter, _hmarks⟩ := mem_normalizedMarkedFamily_iff.mp hKU
  refine ⟨K, U, ?_, heq⟩
  exact (by omega : n - k + 1 ≤ n - s.card).trans
    (coordinateDisk_dimension s hρ K hdisk)

end RankThreeProjection
