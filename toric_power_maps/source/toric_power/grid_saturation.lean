module

public import ToricPower.PeriodicMain
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

@[expose] public section
noncomputable section

open Set Module
open scoped BigOperators Pointwise

namespace ToricPower

def dimensionDenominator (n : ℕ) : ℕ :=
  (Finset.Icc 1 (n + 1)).lcm id

lemma dimensionDenominator_pos (n : ℕ) : 0 < dimensionDenominator n := by
  apply Nat.pos_of_ne_zero
  apply Finset.lcm_ne_zero_iff.mpr
  intro k hk
  have : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  change k ≠ 0
  omega

lemma card_dvd_dimensionDenominator {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n + 1) :
    k ∣ dimensionDenominator n := by
  exact Finset.dvd_lcm (s := Finset.Icc 1 (n + 1)) (f := id)
    (Finset.mem_Icc.mpr ⟨hk, hkn⟩)

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def finiteBarycenter (S : Finset E) : E := (S.card : ℝ)⁻¹ • ∑ v ∈ S, v

lemma finiteBarycenter_mem (S : Finset E) (hS : S.Nonempty) :
    finiteBarycenter S ∈ convexHull ℝ (S : Set E) := by
  have hc : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  simpa [finiteBarycenter, Finset.centerMass] using
    S.centerMass_id_mem_convexHull (w := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)
      (by simpa using hc)

/-- Averaging a finite support retains every strict linear inequality already
satisfied by a point of its convex hull, provided the whole support satisfies
the corresponding weak inequality. -/
lemma linear_strict_at_barycenter (S : Finset E) (hS : S.Nonempty)
    (f : E →ₗ[ℝ] ℝ) (a : ℝ) (hweak : ∀ v ∈ S, f v ≤ a)
    (x : E) (hx : x ∈ convexHull ℝ (S : Set E)) (hstrict : f x < a) :
    f (finiteBarycenter S) < a := by
  classical
  have hex : ∃ v ∈ S, f v < a := by
    by_contra h
    push_neg at h
    have hs : (S : Set E) ⊆ f ⁻¹' Set.Ici a := fun v hv => h v hv
    have hh : convexHull ℝ (S : Set E) ⊆ f ⁻¹' Set.Ici a :=
      convexHull_min hs ((convex_Ici a).linear_preimage f)
    exact (not_le_of_gt hstrict) (hh hx)
  have hsum : (∑ v ∈ S, f v) < (S.card : ℝ) * a := by
    have hh := Finset.sum_lt_sum (fun v hv => hweak v hv) hex
    simpa using hh
  have hc : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  rw [finiteBarycenter, map_smul, map_sum]
  change (S.card : ℝ)⁻¹ * (∑ v ∈ S, f v) < a
  calc
    (S.card : ℝ)⁻¹ * (∑ v ∈ S, f v) <
        (S.card : ℝ)⁻¹ * ((S.card : ℝ) * a) :=
      mul_lt_mul_of_pos_left hsum (inv_pos.mpr hc)
    _ = a := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

lemma scaled_barycenter_integral (L : AddSubgroup E) (S : Finset E)
    (hS : S.Nonempty) (D H : ℕ) (hcard : S.card ∣ H)
    (hintegral : ∀ v ∈ S, (D : ℝ) • v ∈ L) :
    ((D * H : ℕ) : ℝ) • finiteBarycenter S ∈ L := by
  obtain ⟨q, hq⟩ := hcard
  have hc : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hS)
  have heq : (((D * H : ℕ) : ℝ) * (S.card : ℝ)⁻¹) = (q : ℝ) * D := by
    rw [hq]
    push_cast
    field_simp
    <;> ring
  rw [finiteBarycenter, smul_smul, heq, mul_smul, Finset.smul_sum]
  simpa only [Nat.cast_smul_eq_nsmul] using
    L.nsmul_mem (L.sum_mem fun v hv => hintegral v hv) q

/-- Caratheodory and a uniform barycenter denominator put a point on a prescribed
rational grid while retaining any chosen family of strict supporting
inequalities. This is the geometric input for Lemma 6.1, in all dimensions. -/
theorem exists_grid_point_preserving_strict_faces {n : ℕ} {ι : Type*}
    (vertices : Finset (Fin n → ℝ)) (x : Fin n → ℝ)
    (hx : x ∈ convexHull ℝ (vertices : Set (Fin n → ℝ)))
    (D : ℕ) (hintegral : ∀ v ∈ vertices, (D : ℝ) • v ∈ integerLattice n)
    (f : ι → (Fin n → ℝ) →ₗ[ℝ] ℝ) (a : ι → ℝ) (strict : Set ι)
    (hweak : ∀ v ∈ vertices, ∀ i, f i v ≤ a i)
    (hstrict : ∀ i ∈ strict, f i x < a i) :
    ∃ y ∈ convexHull ℝ (vertices : Set (Fin n → ℝ)),
      ((D * dimensionDenominator n : ℕ) : ℝ) • y ∈ integerLattice n ∧
        ∀ i ∈ strict, f i y < a i := by
  classical
  let S := Caratheodory.minCardFinsetOfMemConvexHull hx
  have hS : S.Nonempty := Caratheodory.minCardFinsetOfMemConvexHull_nonempty hx
  have hsub : (S : Set (Fin n → ℝ)) ⊆ vertices :=
    Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
  have hxS : x ∈ convexHull ℝ (S : Set (Fin n → ℝ)) :=
    Caratheodory.mem_minCardFinsetOfMemConvexHull hx
  have haff : AffineIndependent ℝ ((↑) : S → (Fin n → ℝ)) :=
    Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
  have hcard : S.card ≤ n + 1 := by
    have h := haff.card_le_finrank_succ
    have hd := Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : S → (Fin n → ℝ))))
    have h' := h.trans (Nat.add_le_add_right hd 1)
    simpa using h'
  refine ⟨finiteBarycenter S, convexHull_mono hsub (finiteBarycenter_mem S hS), ?_, ?_⟩
  · exact scaled_barycenter_integral (integerLattice n) S hS D (dimensionDenominator n)
      (card_dvd_dimensionDenominator (Finset.card_pos.mpr hS) hcard)
      (fun v hv => hintegral v (hsub hv))
  · intro i hi
    exact linear_strict_at_barycenter S hS (f i) (a i)
      (fun v hv => hweak v (hsub hv) i) x hxS (hstrict i hi)

end ToricPower
