module

public import PaperVerification.DnGaussian
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

/-!
# Projection through finitely many orthogonal fibres

The point set is an actual disjoint union of products of sets in complementary
coordinate blocks. The Gaussian factorization is proved from a bijection of
point sets and summability. The minimizing-set transfer assumes exactly that the
fixed slice meets the global minimum set. It does not assume the projected
minimum, nor define a lattice by its desired minimizers.

This general analytic statement applies to the finite coset decomposition in
Proposition 6.1. Convergence hypotheses are explicit; the E7 application in
E7Projection discharges them for its concrete lattices.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

variable {h w : ℕ} {G : Type*}

/-- The literal union of orthogonal products in the finite glue decomposition. -/
def orthogonalGlue (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ)) :
    Set (Fin (h + w) → ℝ) :=
  {z | ∃ g : G, ∃ x ∈ C g, ∃ y ∈ D g, z = Fin.append x y}

theorem sqDist_append_blocks (x x' : Fin h → ℝ) (y y' : Fin w → ℝ) :
    sqDist (Fin.append x y) (Fin.append x' y') = sqDist x x' + sqDist y y' := by
  unfold sqDist
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

theorem append_blocks_left_injective {x x' : Fin h → ℝ} {y y' : Fin w → ℝ}
    (heq : Fin.append x y = Fin.append x' y') : x = x' := by
  funext i
  simpa only [Fin.append_left] using congrFun heq (Fin.castAdd w i)

theorem append_blocks_right_injective {x x' : Fin h → ℝ} {y y' : Fin w → ℝ}
    (heq : Fin.append x y = Fin.append x' y') : y = y' := by
  funext i
  simpa only [Fin.append_right] using congrFun heq (Fin.natAdd h i)

def orthogonalGlueMap (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (v : Σ g : G, C g × D g) : orthogonalGlue C D :=
  ⟨Fin.append v.2.1.val v.2.2.val, v.1, v.2.1.val, v.2.1.property,
    v.2.2.val, v.2.2.property, rfl⟩

theorem orthogonalGlueMap_bijective
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g'))) :
    Function.Bijective (orthogonalGlueMap C D) := by
  constructor
  · rintro ⟨g, x, y⟩ ⟨g', x', y'⟩ heq
    have hv := congrArg Subtype.val heq
    change Fin.append x.val y.val = Fin.append x'.val y'.val at hv
    have hx := append_blocks_left_injective hv
    have hg : g = g' := by
      by_contra hne
      have hmem : x.val ∈ C g ∩ C g' := ⟨x.property, hx.symm ▸ x'.property⟩
      exact (hdisj hne).le_bot hmem
    subst g'
    have hxx : x = x' := Subtype.ext hx
    have hyy : y = y' := Subtype.ext (append_blocks_right_injective hv)
    subst x'
    subst y'
    rfl
  · rintro ⟨z, g, x, hx, y, hy, rfl⟩
    exact ⟨⟨g, ⟨x, hx⟩, ⟨y, hy⟩⟩, rfl⟩

def orthogonalGlueEquiv
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g'))) :
    (Σ g : G, C g × D g) ≃ orthogonalGlue C D :=
  Equiv.ofBijective _ (orthogonalGlueMap_bijective C D hdisj)

/-- The series in a single product block, with no finite truncation. -/
theorem hasSum_orthogonal_gaussian_product
    (C : Set (Fin h → ℝ)) (D : Set (Fin w → ℝ))
    (α : ℝ) (x : Fin h → ℝ) (t : Fin w → ℝ)
    (hC : Summable (fun v : C => Real.exp (-α * sqDist v.val x)))
    (hD : Summable (fun v : D => Real.exp (-α * sqDist v.val t))) :
    HasSum (fun v : C × D =>
      Real.exp (-α * sqDist (Fin.append v.1.val v.2.val) (Fin.append x t)))
      (setGaussian C α x * setGaussian D α t) := by
  have hprod := Summable.mul_of_nonneg hC hD
    (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have hs := hC.hasSum.mul hD.hasSum hprod
  unfold setGaussian
  convert hs using 1
  funext v
  rw [sqDist_append_blocks, mul_add, Real.exp_add]

/-- Summability of the actual projected union follows from the component series. -/
theorem summable_gaussian_disjoint_finite_union [Fintype G]
    (C : G → Set (Fin h → ℝ)) (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g')))
    (α : ℝ) (x : Fin h → ℝ)
    (hC : ∀ g, Summable (fun v : C g => Real.exp (-α * sqDist v.val x))) :
    Summable (fun v : (⋃ g, C g) => Real.exp (-α * sqDist v.val x)) := by
  let e := (Set.unionEqSigmaOfDisjoint hdisj).symm
  have hs : Summable (fun v : Σ g : G, C g =>
      Real.exp (-α * sqDist v.2.val x)) :=
    (summable_sigma_of_nonneg (fun _ => (Real.exp_pos _).le)).mpr
      ⟨hC, Summable.of_finite⟩
  exact (e.summable_iff (f := fun v : (⋃ g, C g) =>
    Real.exp (-α * sqDist v.val x))).mp hs

theorem setGaussian_disjoint_finite_union [Fintype G]
    (C : G → Set (Fin h → ℝ)) (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g')))
    (α : ℝ) (x : Fin h → ℝ)
    (hC : ∀ g, Summable (fun v : C g => Real.exp (-α * sqDist v.val x))) :
    setGaussian (⋃ g, C g) α x = ∑ g : G, setGaussian (C g) α x := by
  let e := (Set.unionEqSigmaOfDisjoint hdisj).symm
  have hs : Summable (fun v : Σ g : G, C g =>
      Real.exp (-α * sqDist v.2.val x)) :=
    (summable_sigma_of_nonneg (fun _ => (Real.exp_pos _).le)).mpr
      ⟨hC, Summable.of_finite⟩
  calc
    _ = ∑' v : Σ g : G, C g, Real.exp (-α * sqDist v.2.val x) :=
      (e.tsum_eq (fun v : (⋃ g, C g) => Real.exp (-α * sqDist v.val x))).symm
    _ = ∑' g : G, ∑' v : C g, Real.exp (-α * sqDist v.val x) := hs.tsum_sigma
    _ = _ := by simp only [tsum_fintype, setGaussian]

/-- Exact orthogonal finite-coset factorization, justified by convergent series. -/
theorem setGaussian_orthogonalGlue [Fintype G]
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g')))
    (α : ℝ) (x : Fin h → ℝ) (t : Fin w → ℝ)
    (hC : ∀ g, Summable (fun v : C g => Real.exp (-α * sqDist v.val x)))
    (hD : ∀ g, Summable (fun v : D g => Real.exp (-α * sqDist v.val t))) :
    setGaussian (orthogonalGlue C D) α (Fin.append x t) =
      ∑ g : G, setGaussian (C g) α x * setGaussian (D g) α t := by
  let f : (Σ g : G, C g × D g) → ℝ := fun v =>
    Real.exp (-α * sqDist (Fin.append v.2.1.val v.2.2.val) (Fin.append x t))
  have hg (g : G) : HasSum (fun v : C g × D g => f ⟨g, v⟩)
      (setGaussian (C g) α x * setGaussian (D g) α t) :=
    hasSum_orthogonal_gaussian_product (C g) (D g) α x t (hC g) (hD g)
  have hs : Summable f :=
    (summable_sigma_of_nonneg (fun _ => (Real.exp_pos _).le)).mpr
      ⟨fun g => (hg g).summable, Summable.of_finite⟩
  calc
    _ = ∑' v, f v := ((orthogonalGlueEquiv C D hdisj).tsum_eq
      (fun v : orthogonalGlue C D =>
        Real.exp (-α * sqDist v.val (Fin.append x t)))).symm
    _ = ∑' g : G, ∑' v : C g × D g, f ⟨g, v⟩ := hs.tsum_sigma
    _ = _ := by simp only [(hg _).tsum_eq, tsum_fintype]

theorem summable_gaussian_orthogonalGlue [Fintype G]
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g')))
    (α : ℝ) (x : Fin h → ℝ) (t : Fin w → ℝ)
    (hC : ∀ g, Summable (fun v : C g => Real.exp (-α * sqDist v.val x)))
    (hD : ∀ g, Summable (fun v : D g => Real.exp (-α * sqDist v.val t))) :
    Summable (fun v : orthogonalGlue C D =>
      Real.exp (-α * sqDist v.val (Fin.append x t))) := by
  let f : (Σ g : G, C g × D g) → ℝ := fun v =>
    Real.exp (-α * sqDist (Fin.append v.2.1.val v.2.2.val) (Fin.append x t))
  have hs : Summable f :=
    (summable_sigma_of_nonneg (fun _ => (Real.exp_pos _).le)).mpr
      ⟨fun g => (hasSum_orthogonal_gaussian_product (C g) (D g) α x t
        (hC g) (hD g)).summable, Summable.of_finite⟩
  exact ((orthogonalGlueEquiv C D hdisj).summable_iff
    (f := fun v : orthogonalGlue C D =>
      Real.exp (-α * sqDist v.val (Fin.append x t)))).mp hs

/-- Equation in the proof of Proposition 6.1 for arbitrary finite product fibres. -/
theorem projection_gaussian_factorization [Fintype G]
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g')))
    (α c : ℝ) (x : Fin h → ℝ) (t₀ : Fin w → ℝ)
    (hC : ∀ g, Summable (fun v : C g => Real.exp (-α * sqDist v.val x)))
    (hD : ∀ g, Summable (fun v : D g => Real.exp (-α * sqDist v.val t₀)))
    (hfibre : ∀ g, setGaussian (D g) α t₀ = c) :
    setGaussian (orthogonalGlue C D) α (Fin.append x t₀) =
      c * setGaussian (⋃ g, C g) α x := by
  rw [setGaussian_orthogonalGlue C D hdisj α x t₀ hC hD,
    setGaussian_disjoint_finite_union C hdisj α x hC]
  simp_rw [hfibre]
  rw [← Finset.sum_mul]
  exact mul_comm _ _

/-- The full minimum-set transfer. Its slice hypothesis is the existence of an
actual global minimizer on that slice, not an assumption about the projection. -/
theorem projection_coldSpot_iff_slice [Fintype G]
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g')))
    (α c : ℝ) (hc : 0 < c) (t₀ : Fin w → ℝ)
    (hC : ∀ x g, Summable (fun v : C g => Real.exp (-α * sqDist v.val x)))
    (hD : ∀ g, Summable (fun v : D g => Real.exp (-α * sqDist v.val t₀)))
    (hfibre : ∀ g, setGaussian (D g) α t₀ = c)
    (hmeet : ∃ x₀ : Fin h → ℝ,
      IsColdSpot (orthogonalGlue C D) α (Fin.append x₀ t₀))
    (x : Fin h → ℝ) :
    IsColdSpot (⋃ g, C g) α x ↔
      IsColdSpot (orthogonalGlue C D) α (Fin.append x t₀) := by
  have hfactor (y : Fin h → ℝ) :=
    projection_gaussian_factorization C D hdisj α c y t₀ (hC y) hD hfibre
  obtain ⟨x₀, hx₀⟩ := hmeet
  constructor
  · intro hx z
    have hle := mul_le_mul_of_nonneg_left (hx x₀) hc.le
    rw [← hfactor x, ← hfactor x₀] at hle
    exact hle.trans (hx₀ z)
  · intro hx y
    have hle := hx (Fin.append y t₀)
    rw [hfactor x, hfactor y] at hle
    exact (mul_le_mul_iff_of_pos_left hc).mp hle

/-- Positive-parameter uniformity and the prescribed universal equality locus. -/
theorem projection_universal_minimum_set [Fintype G]
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g')))
    (c : ℝ → ℝ) (hc : ∀ α, 0 < α → 0 < c α) (t₀ : Fin w → ℝ)
    (hC : ∀ α, 0 < α → ∀ x g,
      Summable (fun v : C g => Real.exp (-α * sqDist v.val x)))
    (hD : ∀ α, 0 < α → ∀ g,
      Summable (fun v : D g => Real.exp (-α * sqDist v.val t₀)))
    (hfibre : ∀ α, 0 < α → ∀ g, setGaussian (D g) α t₀ = c α)
    (K : Set (Fin (h + w) → ℝ))
    (hK : ∀ α, 0 < α → ∀ z,
      IsColdSpot (orthogonalGlue C D) α z ↔ z ∈ K)
    (hmeet : ∃ x₀ : Fin h → ℝ, Fin.append x₀ t₀ ∈ K) :
    ∀ α, 0 < α → ∀ x : Fin h → ℝ,
      IsColdSpot (⋃ g, C g) α x ↔ Fin.append x t₀ ∈ K := by
  intro α hα x
  rw [projection_coldSpot_iff_slice C D hdisj α (c α) (hc α hα) t₀
    (hC α hα) (hD α hα) (hfibre α hα) (by
      obtain ⟨x₀, hx₀⟩ := hmeet
      exact ⟨x₀, (hK α hα _).mpr hx₀⟩), hK α hα]

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.projection_gaussian_factorization
#print axioms PaperVerification.ColdSpots.projection_coldSpot_iff_slice
#print axioms PaperVerification.ColdSpots.projection_universal_minimum_set

