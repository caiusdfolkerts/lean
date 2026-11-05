module

public import PaperVerification.ToricFanPolytopeSmoothness
public import PaperVerification.ToricBundleFanAverages


@[expose] public section
/-!
# Edge bounds under convex averages on one actual normal fan

For each fixed primitive dual direction, every endpoint polytope contains
the initial segment of the prescribed common length.  Averaging its actual
Cartier vertices averages these feasible points.  The complete classification
of actual incident edges then bounds every edge of the averaged polytope.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem cartierPoint_weighted_sum {κ : Type*} (s : Finset κ)
    (a : κ → Lattice n → ℝ) (w : κ → ℝ) (C : «Σ».fullCones) :
    «Σ».cartierPoint (fun v => ∑ i ∈ s, w i * a i v) C =
      ∑ i ∈ s, w i • «Σ».cartierPoint (a i) C := by
  simp only [cartierPoint, Finset.sum_smul, Finset.smul_sum, smul_neg,
    mul_smul, Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_comm

theorem support_axis_point_of_edgesAtLeast (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {bound : ℕ} (hbound : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast bound)
    (s : «Σ».fullCones) (i : Fin n) :
    «Σ».cartierPoint (fun u => (a u : ℝ)) s + (bound : ℝ) • «Σ».cartierBasis s i ∈
      «Σ».fanPolytope (fun u => (a u : ℝ)) := by
  let P := «Σ».supportLatticePolytope hpure a ha
  obtain ⟨lengths, hlengths⟩ := «Σ».support_polytope_coordinate_edges hpure a ha s
  have hedge : P.IsEdge (embed n («Σ».cartierLatticePoint a s))
      (embed n («Σ».cartierLatticePoint a s +
        (lengths i : ℤ) • integralDualBasis («Σ».fullConeBasis s) i)) := by
    simpa only [«Σ».embed_cartierLatticePoint] using (hlengths i).2.1
  have hlen := P.edge_basis_length_bound hbound («Σ».cartierLatticePoint a s)
    (integralDualBasis («Σ».fullConeBasis s)) i (lengths i) hedge
  have hlenR : (bound : ℝ) ≤ lengths i := by exact_mod_cast hlen
  have hpos : (0 : ℝ) < lengths i := by exact_mod_cast (hlengths i).1
  let t : ℝ := bound / lengths i
  have ht : t ∈ Icc 0 1 := ⟨div_nonneg (Nat.cast_nonneg _) hpos.le,
    (div_le_one hpos).mpr hlenR⟩
  have hend : embed n («Σ».cartierLatticePoint a s +
      (lengths i : ℤ) • integralDualBasis («Σ».fullConeBasis s) i) =
      «Σ».cartierPoint (fun u => (a u : ℝ)) s + (lengths i : ℝ) • «Σ».cartierBasis s i := by
    rw [map_add, embed_int_smul, Int.cast_natCast, «Σ».embed_cartierLatticePoint]
    rw [cartierBasis, integralBasisReal_apply]
  have hseg : «Σ».cartierPoint (fun u => (a u : ℝ)) s + (bound : ℝ) • «Σ».cartierBasis s i ∈
      segment ℝ («Σ».cartierPoint (fun u => (a u : ℝ)) s)
        (embed n («Σ».cartierLatticePoint a s +
          (lengths i : ℤ) • integralDualBasis («Σ».fullConeBasis s) i)) := by
    rw [hend]
    refine ⟨1 - t, t, sub_nonneg.mpr ht.2, ht.1, by ring, ?_⟩
    have htlen : t * (lengths i : ℝ) = bound := div_mul_cancel₀ _ hpos.ne'
    rw [smul_add, smul_smul, htlen, sub_smul, one_smul]
    abel
  have hmem := (hlengths i).2.1.2.subset hseg
  simpa only [P, «Σ».supportLatticePolytope_carrier] using hmem

theorem support_edgesAtLeast_of_axis_points (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    (bound : ℕ)
    (haxis : ∀ s : «Σ».fullCones, ∀ i : Fin n,
      «Σ».cartierPoint (fun u => (a u : ℝ)) s + (bound : ℝ) • «Σ».cartierBasis s i ∈
        «Σ».fanPolytope (fun u => (a u : ℝ))) :
    («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast bound := by
  let P := «Σ».supportLatticePolytope hpure a ha
  apply (P.edgesAtLeast_iff bound).mpr
  intro v w hedge
  have hv := (P.edge_endpoints_extreme hedge).1
  have hP : P.carrier = convexHull ℝ (Set.range («Σ».cartierPoint (fun u => (a u : ℝ)))) := by
    rw [«Σ».supportLatticePolytope_carrier,
      «Σ».fanPolytope_eq_convexHull_cartier hpure _ (IsStrictSupport.isNef «Σ» ha)]
  have hv' := hP ▸ hv
  obtain ⟨s, hs⟩ := extremePoints_convexHull_subset hv'
  have hvZ : v = «Σ».cartierLatticePoint a s := by
    apply embed_injective n
    rw [«Σ».embed_cartierLatticePoint]
    exact hs.symm
  subst v
  have hedge' : P.IsEdge («Σ».cartierPoint (fun u => (a u : ℝ)) s) (embed n w) := by
    simpa only [«Σ».embed_cartierLatticePoint] using hedge
  obtain ⟨lengths, hlengths⟩ := «Σ».support_polytope_coordinate_edges hpure a ha s
  obtain ⟨i, hi⟩ := «Σ».support_polytope_edge_has_coordinate_direction hpure a ha s (embed n w) hedge'
  have hwseg := (hlengths i).2.2 ▸ hi
  have hverts := P.edge_endpoints_extreme hedge'
  have hend := (P.edge_endpoints_extreme (hlengths i).2.1).2.1
  have hwZ : w = «Σ».cartierLatticePoint a s +
      (lengths i : ℤ) • integralDualBasis («Σ».fullConeBasis s) i := by
    rcases (mem_extremePoints_iff_forall_segment.mp hverts.2).2
      _ hverts.1.1 _ hend hwseg with heq | heq
    · exact (hedge'.1 heq).elim
    · apply embed_injective n
      exact heq.symm
  rw [hwZ, LatticePolytope.latticeLength_basis_direction]
  have haxismem : «Σ».cartierPoint (fun u => (a u : ℝ)) s +
      (bound : ℝ) • «Σ».cartierBasis s i ∈
      P.coordinateRayFace («Σ».cartierPoint (fun u => (a u : ℝ)) s) («Σ».cartierBasis s) i := by
    refine ⟨?_, ?_⟩
    · simpa only [P, «Σ».supportLatticePolytope_carrier] using haxis s i
    · intro j hji
      simp [Module.Basis.repr_self_apply, hji, Ne.symm hji]
  rw [(hlengths i).2.2] at haxismem
  obtain ⟨r, t, hr, ht, hrt, he⟩ := haxismem
  have ht1 : t ≤ 1 := by linarith
  have he' := congrArg (fun x => («Σ».cartierBasis s).repr x i) he
  have hend' : embed n («Σ».cartierLatticePoint a s +
      (lengths i : ℤ) • integralDualBasis («Σ».fullConeBasis s) i) =
      «Σ».cartierPoint (fun u => (a u : ℝ)) s + (lengths i : ℝ) • «Σ».cartierBasis s i := by
    rw [map_add, embed_int_smul, Int.cast_natCast, «Σ».embed_cartierLatticePoint]
    rw [cartierBasis, integralBasisReal_apply]
  rw [hend'] at he'
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
    Module.Basis.repr_self_apply, if_pos rfl, ite_true, smul_eq_mul, mul_one] at he'
  have hlen0 : (0 : ℝ) ≤ lengths i := Nat.cast_nonneg _
  have hlength : (bound : ℝ) ≤ lengths i := by
    have hm := mul_le_mul_of_nonneg_right ht1 hlen0
    have hscaled := congrArg
      (fun t : ℝ => t * («Σ».cartierBasis s).repr
        («Σ».cartierPoint (fun u => (a u : ℝ)) s) i) hrt
    simp only [add_mul, one_mul] at hscaled
    nlinarith only [he', hscaled, hm]
  exact_mod_cast hlength

/-- Edge bounds are preserved by a convex combination of integral strictly
supported coefficients whenever the resulting coefficients are integral. -/
theorem support_edgesAtLeast_convex_combination {κ : Type*} (s : Finset κ)
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    (A : κ → Lattice n → ℤ)
    (hA : ∀ i ∈ s, «Σ».IsStrictSupport (fun u => (A i u : ℝ)))
    (w : κ → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : (∑ i ∈ s, w i) = 1)
    (hcoeff : (fun u => (a u : ℝ)) = fun u => ∑ i ∈ s, w i * (A i u : ℝ))
    (bound : ℕ)
    (hedges : ∀ i (hi : i ∈ s),
      («Σ».supportLatticePolytope hpure (A i) (hA i hi)).EdgesAtLeast bound) :
    («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast bound := by
  apply «Σ».support_edgesAtLeast_of_axis_points hpure a ha bound
  intro C j
  have hv : «Σ».cartierPoint (fun u => (a u : ℝ)) C =
      ∑ i ∈ s, w i • «Σ».cartierPoint (fun u => (A i u : ℝ)) C := by
    rw [hcoeff, «Σ».cartierPoint_weighted_sum]
  intro u hu
  have hle := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
    («Σ».support_axis_point_of_edgesAtLeast hpure (A i) (hA i hi) (hedges i hi) C j u hu)
      (hw i hi))
  change -(a u : ℝ) ≤ (dotProductEquiv ℝ (Fin n) (embed n u))
    («Σ».cartierPoint (fun u => (a u : ℝ)) C + (bound : ℝ) • «Σ».cartierBasis C j)
  rw [show (a u : ℝ) = ∑ i ∈ s, w i * (A i u : ℝ) from congrFun hcoeff u, hv]
  simp only [map_add, map_sum, map_smul, smul_eq_mul] at hle ⊢
  have hconst : (∑ i ∈ s, w i * ((bound : ℝ) *
      (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierBasis C j))) =
      (bound : ℝ) * (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierBasis C j) := by
    rw [← Finset.sum_mul, hsum, one_mul]
  simp only [mul_add, mul_neg, Finset.sum_neg_distrib,
    Finset.sum_add_distrib, hconst] at hle
  exact hle

end PaperVerification.ToricGeometry.SmoothCompleteFan
