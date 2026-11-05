module
public import PaperVerification.ToricSimplexGeometry
public import PaperVerification.ToricBoxAverages
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Tactic.Positivity
@[expose] public section
/-!
# Unit corner boxes and their facet-center slack

The unit-box assertion needed for integer decomposition follows directly from
convexity and long edge segments. It does not require contraction theory.
The second part proves the half-integral facet slack of every contained unit
basis box, which is the Cartier-center estimate in Lemma 4.2.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A simplex of edge extent `r` contains every nonnegative coordinate
combination with total coordinate sum at most `r`. -/
theorem corner_simplex_mem {d : ℕ} (A : Set E) (hA : Convex ℝ A) (p : E) (hp : p ∈ A)
    (v : Fin d → E) (r : ℝ) (hr : 0 < r) (hv : ∀ i, p + r • v i ∈ A)
    (t : Fin d → ℝ) (ht : ∀ i, 0 ≤ t i) (hsum : ∑ i, t i ≤ r) :
    p + ∑ i, t i • v i ∈ A := by
  let L : (Fin d → ℝ) →ₗ[ℝ] E := ∑ i, (LinearMap.proj i).smulRight (v i)
  have hL (x : Fin d → ℝ) : L x = ∑ i, x i • v i := by simp [L]
  let S : Set (Fin d → ℝ) := {x | p + L x ∈ A}
  have hS : Convex ℝ S := (hA.translate_preimage_right p).linear_preimage L
  have hverts : insert (0 : Fin d → ℝ) (Set.range fun i => Pi.single i r) ⊆ S := by
    rintro x (rfl | ⟨i, rfl⟩)
    · simpa [S] using hp
    · simpa [S, L, Pi.single_apply] using hv i
  have htSimplex : t ∈ RealSimplex d r := ⟨ht, hsum⟩
  rw [realSimplex_eq_convexHull hr] at htSimplex
  have hmem := convexHull_min hverts hS htSimplex
  simpa [S, hL] using hmem

/-- Any convex body containing `d` long outgoing edge segments contains their
entire unit corner box. The directions need not be linearly independent for
this convexity statement. -/
theorem unit_corner_box_of_long_segments {d : ℕ} (hd : 0 < d)
    (A : Set E) (hA : Convex ℝ A) (p : E) (hp : p ∈ A)
    (v : Fin d → E) (lengths : Fin d → ℝ)
    (hlength : ∀ i, (d : ℝ) ≤ lengths i)
    (hv : ∀ i, p + lengths i • v i ∈ A)
    (t : Fin d → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    p + ∑ i, t i • v i ∈ A := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hv' (i : Fin d) : p + (d : ℝ) • v i ∈ A := by
    have hlen : 0 < lengths i := hdR.trans_le (hlength i)
    have hratio : (d : ℝ) / lengths i ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hdR.le hlen.le, (div_le_one hlen).mpr (hlength i)⟩
    have h := hA.lineMap_mem hp (hv i) hratio
    simpa [AffineMap.lineMap_apply_module', smul_smul, hlen.ne', add_comm] using h
  apply corner_simplex_mem A hA p hp v (d : ℝ) hdR hv' t (fun i => (ht i).1)
  calc
    (∑ i, t i) ≤ ∑ _ : Fin d, (1 : ℝ) :=
      Finset.sum_le_sum (fun i _ => (ht i).2)
    _ = d := by simp

/-- A contained centered unit box forces the stated slack for any supporting
affine functional. -/
theorem unit_box_center_slack {ι : Type*} [Fintype ι]
    (f : E →ᵃ[ℝ] ℝ) (c : E) (v : ι → E)
    (hbox : ∀ t : ι → ℝ, (∀ i, |t i| ≤ 1 / 2) →
      0 ≤ f (c + ∑ i, t i • v i)) :
    (∑ i, |f.linear (v i)|) / 2 ≤ f c := by
  let t : ι → ℝ := fun i => if 0 ≤ f.linear (v i) then -(1 / 2) else 1 / 2
  have ht : ∀ i, |t i| ≤ 1 / 2 := by
    intro i
    dsimp [t]
    split_ifs <;> norm_num
  have hterm (i : ι) : t i * f.linear (v i) = -(|f.linear (v i)| / 2) := by
    by_cases hi : 0 ≤ f.linear (v i)
    · simp [t, hi, abs_of_nonneg hi] <;> ring
    · simp [t, hi, abs_of_neg (lt_of_not_ge hi)] <;> ring
  have hf : f (c + ∑ i, t i • v i) = f c + ∑ i, t i * f.linear (v i) := by
    rw [add_comm]
    change f ((∑ i, t i • v i) +ᵥ c) = _
    rw [AffineMap.map_vadd]
    simp [map_sum, map_smul, vadd_eq_add, smul_eq_mul, add_comm]
  have h := hbox t ht
  rw [hf] at h
  simp only [hterm, Finset.sum_neg_distrib, ← Finset.sum_div] at h
  linarith

/-- An integral, nonzero normal has total absolute coefficient at least one
on every genuine real basis on which it takes integer values. -/
theorem integral_basis_normal_abs_sum {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) (f : E →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (z : ι → ℤ) (hz : ∀ i, (z i : ℝ) = f (b i)) :
    1 ≤ ∑ i, |f (b i)| := by
  have hne : ∃ i, f (b i) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hf
    exact b.ext (fun i => by simpa using h i)
  obtain ⟨i, hi⟩ := hne
  have hzi : z i ≠ 0 := by
    intro hzero
    apply hi
    rw [← hz i, hzero, Int.cast_zero]
  have hziabs : (1 : ℤ) ≤ |z i| := Int.one_le_abs hzi
  have hiabs : (1 : ℝ) ≤ |f (b i)| := by
    rw [← hz i]
    exact_mod_cast hziabs
  have hsum : |f (b i)| ≤ ∑ j, |f (b j)| :=
    Finset.single_le_sum (f := fun j => |f (b j)|)
      (fun j _ => abs_nonneg (f (b j))) (Finset.mem_univ i)
  exact hiabs.trans hsum

/-- The center slack estimate of Lemma 4.2 for every nonzero integral facet
normal: a contained unit basis box has center slack at least one half. -/
theorem integral_unit_box_center_slack {ι : Type*} [Fintype ι]
    (f : E →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (c : E) (b : Module.Basis ι ℝ E)
    (z : ι → ℤ) (hz : ∀ i, (z i : ℝ) = f.linear (b i))
    (hbox : ∀ t : ι → ℝ, (∀ i, |t i| ≤ 1 / 2) →
      0 ≤ f (c + ∑ i, t i • b i)) :
    1 / 2 ≤ f c := by
  have h₁ := unit_box_center_slack f c b hbox
  have h₂ := integral_basis_normal_abs_sum b f.linear hf z hz
  linarith

end PaperVerification.Toric
