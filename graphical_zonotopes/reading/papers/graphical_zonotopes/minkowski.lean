module

public import Papers.GraphicalZonotopes.Ordering
public import Papers.GraphicalZonotopes.Elemental

@[expose] public section

/-!
The geometric bridge from arbitrary compact convex Minkowski summands to
supermodular set functions. No deformation-cone characterization is assumed.
-/
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

def lowerSupport (P : Set (V → ℝ)) (S : Finset V) : ℝ :=
  sInf ((fun x => subsetSum x S) '' P)

theorem continuous_subsetSum (S : Finset V) :
    Continuous (fun x : V → ℝ => subsetSum x S) := by
  unfold subsetSum
  exact continuous_finsetSum _ (fun v _ => continuous_apply v)

theorem lowerSupport_minimum {P : Set (V → ℝ)} (hc : IsCompact P)
    (hne : P.Nonempty) (S : Finset V) :
    ∃ x ∈ P, subsetSum x S = lowerSupport P S ∧
      ∀ y ∈ P, lowerSupport P S ≤ subsetSum y S := by
  obtain ⟨x, hx, hmin⟩ := hc.exists_isMinOn hne (continuous_subsetSum S).continuousOn
  have hi : IsLeast ((fun y => subsetSum y S) '' P) (subsetSum x S) := by
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmin hy
  have he : lowerSupport P S = subsetSum x S := hi.csInf_eq
  exact ⟨x, hx, he.symm, fun y hy => by rw [he]; exact hmin hy⟩

theorem lowerSupport_le {P : Set (V → ℝ)} (hc : IsCompact P)
    {x : V → ℝ} (hx : x ∈ P) (S : Finset V) :
    lowerSupport P S ≤ subsetSum x S := by
  obtain ⟨_, _, _, h⟩ := lowerSupport_minimum hc ⟨x, hx⟩ S
  exact h x hx

theorem lowerSupport_normalized {P : Set (V → ℝ)} (hc : IsCompact P)
    (hne : P.Nonempty) : Normalized (lowerSupport P) := by
  obtain ⟨x, hx, he, _⟩ := lowerSupport_minimum hc hne ∅
  simpa [Normalized] using he.symm

theorem lowerSupport_add {P R : Set (V → ℝ)}
    (hP : IsCompact P) (hR : IsCompact R) (hnP : P.Nonempty) (hnR : R.Nonempty) :
    lowerSupport (P + R) = lowerSupport P + lowerSupport R := by
  funext S
  obtain ⟨p, hp, hpmin, hpbound⟩ := lowerSupport_minimum hP hnP S
  obtain ⟨r, hr, hrmin, hrbound⟩ := lowerSupport_minimum hR hnR S
  have hi : IsLeast ((fun y => subsetSum y S) '' (P + R))
      (lowerSupport P S + lowerSupport R S) := by
    refine ⟨⟨p + r, Set.add_mem_add hp hr, ?_⟩, ?_⟩
    · change subsetSum (p+r) S = lowerSupport P S + lowerSupport R S
      rw [subsetSum_add, hpmin, hrmin]
    · rintro _ ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      change lowerSupport P S + lowerSupport R S ≤ subsetSum (x+y) S
      rw [subsetSum_add]
      exact add_le_add (hpbound x hx) (hrbound y hy)
  exact hi.csInf_eq

theorem lowerSupport_basePolytope {z : SetFunction V} (hz : Normalized z)
    (hs : Supermodular z) : lowerSupport (basePolytope z) = z := by
  funext S
  obtain ⟨e, j, hj, hp⟩ := exists_prefix_enumeration S
  have hg := greedyPoint_mem_basePolytope hz hs e
  have he : subsetSum (greedyPoint z e) S = z S := by
    rw [← hp]
    exact greedyPoint_prefix z hz e j hj
  have hi : IsLeast ((fun y => subsetSum y S) '' basePolytope z) (z S) := by
    refine ⟨⟨greedyPoint z e, hg, he⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hy.2 S
  exact hi.csInf_eq

/-- A decomposition of a greedy point simultaneously minimizes every prefix
in both summands. -/
theorem summand_prefix_minima {z : SetFunction V} (hz : Normalized z)
    (hs : Supermodular z) {P R : Set (V → ℝ)}
    (hP : IsCompact P) (hR : IsCompact R) (hnP : P.Nonempty) (hnR : R.Nonempty)
    (heq : P + R = basePolytope z)
    (e : Fin (Fintype.card V) ≃ V) :
    ∃ p ∈ P, ∀ j ≤ Fintype.card V,
      subsetSum p (orderPrefix e j) = lowerSupport P (orderPrefix e j) := by
  have hg := greedyPoint_mem_basePolytope hz hs e
  rw [← heq] at hg
  obtain ⟨p, hp, r, hr, hpr⟩ := hg
  change p+r = greedyPoint z e at hpr
  refine ⟨p, hp, ?_⟩
  intro j hj
  have hadd : lowerSupport P (orderPrefix e j) + lowerSupport R (orderPrefix e j) =
      z (orderPrefix e j) := by
    have h := congrFun (lowerSupport_add hP hR hnP hnR) (orderPrefix e j)
    rw [heq, lowerSupport_basePolytope hz hs] at h
    exact h.symm
  have hsum : subsetSum p (orderPrefix e j) + subsetSum r (orderPrefix e j) =
      z (orderPrefix e j) := by
    rw [← subsetSum_add, hpr]
    exact greedyPoint_prefix z hz e j hj
  have hpbound := lowerSupport_le hP hp (orderPrefix e j)
  have hrbound := lowerSupport_le hR hr (orderPrefix e j)
  linarith

/-- Supermodularity is derived for arbitrary compact-convex summands, rather
than being imposed on them as an extra assumption. -/
theorem summand_lowerSupport_supermodular {z : SetFunction V} (hz : Normalized z)
    (hs : Supermodular z) {P R : Set (V → ℝ)}
    (hP : IsCompact P) (hR : IsCompact R) (hnP : P.Nonempty) (hnR : R.Nonempty)
    (heq : P + R = basePolytope z) : Supermodular (lowerSupport P) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv S hu hv
  obtain ⟨e, heS, heSu⟩ := exists_pair_enumeration S huv hu hv
  obtain ⟨p, hp, hpref⟩ := summand_prefix_minima hz hs hP hR hnP hnR heq e
  have hS : subsetSum p S = lowerSupport P S := by
    rw [← heS]
    exact hpref _ (e.symm u).isLt.le
  have hSu : subsetSum p (insert u S) = lowerSupport P (insert u S) := by
    rw [← heSu]
    exact hpref _ (e.symm v).isLt.le
  have hSuv : subsetSum p (insert v (insert u S)) = lowerSupport P (insert v (insert u S)) := by
    have h := hpref ((e.symm v).val + 1) (by omega)
    rw [orderPrefix_succ, e.apply_symm_apply, heSu] at h
    exact h
  have hSv := lowerSupport_le hP hp (insert v S)
  rw [subsetSum_insert (by simp [Ne.symm huv, hv]), hSu] at hSuv
  rw [subsetSum_insert hv, hS] at hSv
  simp only [delta, insert_comm u v]
  linarith

theorem summand_greedyPoint_mem {z : SetFunction V} (hz : Normalized z)
    (hs : Supermodular z) {P R : Set (V → ℝ)}
    (hP : IsCompact P) (hR : IsCompact R) (hnP : P.Nonempty) (hnR : R.Nonempty)
    (heq : P + R = basePolytope z)
    (e : Fin (Fintype.card V) ≃ V) : greedyPoint (lowerSupport P) e ∈ P := by
  obtain ⟨p, hp, hpref⟩ := summand_prefix_minima hz hs hP hR hnP hnR heq e
  have he : greedyPoint (lowerSupport P) e = p := by
    funext v
    have h0 := hpref (e.symm v).val (e.symm v).isLt.le
    have h1 := hpref ((e.symm v).val + 1) (by omega)
    rw [orderPrefix_succ, e.apply_symm_apply,
      subsetSum_insert (by simpa using not_mem_orderPrefix e (e.symm v))] at h1
    simp only [greedyPoint]
    rw [orderPrefix_succ,e.apply_symm_apply]
    linarith
  rwa [he]

/-- The full geometric summand theorem for lower base polytopes. -/
theorem summand_eq_basePolytope {z : SetFunction V} (hz : Normalized z)
    (hs : Supermodular z) {P R : Set (V → ℝ)}
    (hP : IsCompact P) (hR : IsCompact R) (hconv : Convex ℝ P)
    (hnP : P.Nonempty) (hnR : R.Nonempty)
    (heq : P + R = basePolytope z) : P = basePolytope (lowerSupport P) := by
  apply Set.Subset.antisymm
  · intro p hp
    refine ⟨?_, fun S => lowerSupport_le hP hp S⟩
    obtain ⟨q, hq, hqmin, _⟩ := lowerSupport_minimum hP hnP univ
    obtain ⟨r, hr⟩ := hnR
    have hpr : p + r ∈ basePolytope z := by rw [← heq]; exact Set.add_mem_add hp hr
    have hqr : q + r ∈ basePolytope z := by rw [← heq]; exact Set.add_mem_add hq hr
    have ht1 := hpr.1
    have ht2 := hqr.1
    rw [subsetSum_add] at ht1 ht2
    linarith
  · rw [basePolytope_eq_convexHull (lowerSupport_normalized hP hnP)
      (summand_lowerSupport_supermodular hz hs hP hR hnP hnR heq)]
    apply convexHull_min ?_ hconv
    rintro _ ⟨e, rfl⟩
    exact summand_greedyPoint_mem hz hs hP hR hnP hnR heq e

end GraphicalZonotopes
