module

public import PaperVerification.ToricNearSelectedParity

@[expose] public section

/-!
# An interior summand near a selected nonempty focus

The second parent has height one in every focus normal, while the first
receives the remaining target height. Actual quotient parent polytopes
satisfy the separate base-edge and fiber-degree bounds. Their ordinary
lower-dimensional adjoint decomposition lifts through the exact canonical
slice identity, with no missing boundary or zero-base case.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical Pointwise

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem near_selected_adjoint_decomposition (hpure : «Σ».IsPure)
    (a c : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    (hc : «Σ».IsStrictSupport (fun u => (c u : ℝ)))
    (hedgesA : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast (n + 1))
    (hedgesC : («Σ».supportLatticePolytope hpure c hc).EdgesAtLeast (n + 1))
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hne : R.negative.Nonempty) (t : ℤ)
    (ht : t ≤ (n : ℤ) - 2 * R.baseDimension - 2)
    (m : Lattice n)
    (hm : embed n m ∈ interior («Σ».fanPolytope (fun u => ((a + c) u : ℝ))))
    (hslacks : ∀ u ∈ R.negative, 2 ≤ latticeSlack (a + c) m u)
    (hbudget : (∑ u ∈ R.negative, latticeSlack (a + c) m u) ≤ R.negative.card + t)
    (IH : ∀ d : ℕ, d < n → AdjointDimensionStatement d) :
    ∃ x y : Lattice n,
      embed n x ∈ «Σ».fanPolytope (fun u => (a u : ℝ)) ∧
      embed n y ∈ interior («Σ».fanPolytope (fun u => (c u : ℝ))) ∧ x + y = m := by
  have hdim := R.dimension_eq hR
  have hrpos := R.fiberDimension_pos
  have hqpos : 0 < R.negative.card := Finset.card_pos.mpr hne
  have hn : 0 < n := by omega
  let h : Lattice n → ℕ := fun u => (latticeSlack (a + c) m u - 1).toNat
  let k : Lattice n → ℕ := fun _ => 1
  have hcast (u : Lattice n) (hu : u ∈ R.negative) :
      (h u : ℤ) = latticeSlack (a + c) m u - 1 :=
    Int.toNat_of_nonneg (by have := hslacks u hu; omega)
  have hsum (u : Lattice n) (hu : u ∈ R.negative) :
      (h u : ℤ) + (k u : ℤ) = latticeSlack (a + c) m u := by
    rw [hcast u hu]
    simp only [k, Nat.cast_one]
    omega
  have hHZ : ((∑ u ∈ R.negative, h u : ℕ) : ℤ) =
      (∑ u ∈ R.negative, latticeSlack (a + c) m u) - R.negative.card := by
    rw [Nat.cast_sum, Finset.sum_congr rfl hcast, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hH : (∑ u ∈ R.negative, h u) + 2 * R.baseDimension + 2 ≤ n := by
    have hcast' : ((∑ u ∈ R.negative, h u : ℕ) : ℤ) + 2 * R.baseDimension + 2 ≤ n := by omega
    exact_mod_cast hcast'
  obtain ⟨b, I, hI'⟩ := «Σ».smooth R.negative R.negative_cone
  have hI : I.image b = R.negative := hI'.symm
  let hF : I.image b ∈ «Σ».cones := hI.symm ▸ R.negative_cone
  let Ψ := «Σ».completeQuotientStarFan b I hF
  let RQ := R.focusQuotientRelation hR b I hI
  let coord := RQ.bundleCoordinates
  have hIcard : I.card = R.negative.card := by
    rw [← hI, Finset.card_image_of_injective I b.injective]
  have hrdim : coord.fiberIndices.card = R.fiberDimension := by
    rw [coord.fiberIndices_card, R.focusQuotientRelation_fiberDimension hR b I hI]
  have hbqdim : (n - I.card) - coord.fiberIndices.card = R.baseDimension := by
    rw [hrdim, hIcard]
    omega
  have hH' : (∑ u ∈ I.image b, h u) + 2 * R.baseDimension + 2 ≤ n := by rw [hI]; exact hH
  have hK' : (∑ u ∈ I.image b, k u) = R.negative.card := by simp only [hI, k, Finset.sum_const, smul_eq_mul, mul_one]
  obtain ⟨A, hApoly, hAsm, hAfan, hAlen, hAimage, hqa, hAdegree⟩ :=
    R.exists_focus_slicePolytope hR b I hI hpure a ha (by omega) hedgesA h
      (by omega) (by intro he; omega)
  obtain ⟨C, hCpoly, hCsm, hCfan, hClen, hCimage, hqc, hCdegree⟩ :=
    R.exists_focus_slicePolytope hR b I hI hpure c hc (by omega) hedgesC k
      (by rw [hK']; omega) (by intro he; rw [hK'] at he; omega)
  let dA := displacedSupportLattice a (I.image b) h
  let dC := displacedSupportLattice c (I.image b) k
  let eA := quotientFaceIntegralChart dA b I
  let eC := quotientFaceIntegralChart dC b I
  obtain ⟨mQ, hmQmap, hmQ⟩ := «Σ».exists_quotient_slice_sum_target b I hF a c h k m hm
    (by intro u hu; exact (hsum u (hI ▸ hu)).symm)
  have hmQinterior : embed (n - I.card) mQ ∈ interior (A.minkowskiSum C) :=
    «Σ».quotient_slice_sum_target_interior b I hF a c h k A C hApoly hCpoly hpure
      (IsStrictSupport.isNef Ψ hqa) (IsStrictSupport.isNef Ψ hqc) mQ hmQ
  have hAlen' : A.EdgesAtLeast (((n - I.card) - coord.fiberIndices.card) + 1) :=
    A.edgesAtLeast_mono hAlen (by rw [hbqdim]; omega)
  have hClen' : C.EdgesAtLeast (((n - I.card) - coord.fiberIndices.card) + 1) :=
    C.edgesAtLeast_mono hClen (by rw [hbqdim, hK']; omega)
  have hCdegree' : ((coord.fiberIndices.card + 1 : ℕ) : ℝ) ≤
      RQ.degree (fun u => (C.integralSupport u : ℝ)) := by
    have hle : ((coord.fiberIndices.card + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      rw [hrdim]
      exact_mod_cast (by omega : R.fiberDimension + 1 ≤ n + 1)
    exact hle.trans hCdegree
  have hIH : AdjointDimensionStatement ((n - I.card) - coord.fiberIndices.card) := by
    rw [hbqdim]
    exact IH R.baseDimension (by omega)
  obtain ⟨xQ, yQ, hxQ, hyQ, hxyQ⟩ := coord.bundle_adjoint_of_base_bounds
    (R.focusQuotientRelation_contractible hR b I hI) rfl
    («Σ».completeQuotientStarFan_isPure hpure b I hF)
    A C hAsm hCsm hAfan.symm hCfan.symm hAlen' hClen' hCdegree'
    hIH mQ hmQinterior
  refine ⟨eA.latticeMap xQ, eC.latticeMap yQ, ?_, ?_, ?_⟩
  · have hx : eA.realMap (embed (n - I.card) xQ) ∈ eA.realMap '' A.carrier :=
      Set.mem_image_of_mem _ hxQ
    rw [hAimage] at hx
    simpa only [IntegralAffineEmbedding.embed_latticeMap] using hx.1
  · rw [hCpoly] at hyQ
    exact «Σ».quotient_slice_interior_lattice_image b I hF hpure c hc hedgesC k
      (fun u hu => le_rfl) (by rw [hK']; omega) yQ hyQ
  · rw [← quotientFaceIntegralChart_add, hxyQ]
    exact hmQmap

/-- The complete selected-locus adjoint branch on the original polytopes,
with the literal old normal slacks and an exact integer displacement. -/
theorem polytope_near_selected_adjoint (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast (n + 1)) (hboundQ : Q.EdgesAtLeast (n + 1))
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hne : R.negative.Nonempty) (t : ℤ)
    (ht : t ≤ (n : ℤ) - 2 * R.baseDimension - 2)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q))
    (hslacks : ∀ u ∈ R.negative, 2 ≤ latticeSlack (P.integralSupport + Q.integralSupport) m u)
    (hbudget : (∑ u ∈ R.negative, latticeSlack (P.integralSupport + Q.integralSupport) m u) ≤
      R.negative.card + t)
    (IH : ∀ d : ℕ, d < n → AdjointDimensionStatement d) :
    ∃ x y : Lattice n,
      embed n x ∈ P.carrier ∧ embed n y ∈ interior Q.carrier ∧ x + y = m := by
  have ha := P.integralSupport_isStrictSupport «Σ» hfanP
  have hc := Q.integralSupport_isStrictSupport «Σ» hfanQ
  have hedgesP := P.supportReconstruction_edgesAtLeast «Σ» hpure hfanP hboundP
  have hedgesQ := Q.supportReconstruction_edgesAtLeast «Σ» hpure hfanQ hboundQ
  have hm' : embed n m ∈ interior («Σ».fanPolytope
      (fun u => ((P.integralSupport + Q.integralSupport) u : ℝ))) := by
    rw [«Σ».integralSupport_sum_polytope_eq hpure P Q hfanP hfanQ]
    exact hm
  obtain ⟨x, y, hx, hy, hxy⟩ := «Σ».near_selected_adjoint_decomposition hpure
    P.integralSupport Q.integralSupport ha hc hedgesP hedgesQ R hR hne t ht m hm'
    hslacks hbudget IH
  rw [P.fanPolytope_integralSupport_eq «Σ» hfanP] at hx
  rw [Q.fanPolytope_integralSupport_eq «Σ» hfanQ] at hy
  exact ⟨x, y, hx, hy, hxy⟩

end PaperVerification.ToricGeometry.SmoothCompleteFan
