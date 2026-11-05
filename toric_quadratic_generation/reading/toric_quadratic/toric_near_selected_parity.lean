module

public import PaperVerification.ToricFocusSlicePolytopes
public import PaperVerification.ToricSlicePairTargets
public import PaperVerification.ToricNormalFiniteAllocation
public import PaperVerification.ToricBundleFanBaseInduction
public import PaperVerification.ToricMixedPolytopeBridges

@[expose] public section

/-!
# Every prescribed parity near a selected nonempty focus

The literal normal slacks are split within the exact height budgets. The
resulting saturated quotient slices are genuine smooth polytopes, including
the zero-base nef endpoint. Their actual empty-focus relation supplies the
fiber allocation, and only the ordinary theorem in the smaller base dimension
is used for the remaining coordinates.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open PaperVerification.ToricExchange
open scoped BigOperators Classical Pointwise

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem near_selected_parity_decomposition (hpure : «Σ».IsPure)
    (a c : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    (hc : «Σ».IsStrictSupport (fun u => (c u : ℝ)))
    (hedgesA : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast n)
    (hedgesC : («Σ».supportLatticePolytope hpure c hc).EdgesAtLeast n)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hne : R.negative.Nonempty) (hlarge : n < 2 * R.fiberDimension)
    (m : Lattice n)
    (hm : embed n m ∈ interior («Σ».fanPolytope (fun u => ((a + c) u : ℝ))))
    (hbudget : (∑ u ∈ R.negative, latticeSlack (a + c) m u) + 3 ≤
      2 * ((n : ℤ) - 2 * R.baseDimension))
    (IH : ∀ d : ℕ, d < n → ParityDimensionStatement d) (p : Lattice n) :
    ∃ x y : Lattice n,
      embed n x ∈ «Σ».fanPolytope (fun u => (a u : ℝ)) ∧
      embed n y ∈ «Σ».fanPolytope (fun u => (c u : ℝ)) ∧
      x + y = m ∧ SameParity x p := by
  have hdim := R.dimension_eq hR
  have hrpos := R.fiberDimension_pos
  have hqpos : 0 < R.negative.card := Finset.card_pos.mpr hne
  have hn : 0 < n := by omega
  have hbase : 2 * R.baseDimension ≤ n := by omega
  have hqcap : R.negative.card ≤ n - 2 * R.baseDimension := by omega
  have hcapcast : ((n - 2 * R.baseDimension : ℕ) : ℤ) =
      (n : ℤ) - 2 * R.baseDimension := by
    rw [Nat.cast_sub hbase, Nat.cast_mul, Nat.cast_ofNat]
  have hmpos (u : Lattice n) (hu : u ∈ R.negative) :
      0 < latticeSlack (a + c) m u :=
    «Σ».latticeSlack_pos_of_interior (a + c) m hm u
      («Σ».ray_mem_of_mem_cone R.negative_cone hu)
  obtain ⟨h, k, hsum, hH, hK, hpar⟩ := finset_bounded_parity_split R.negative hqcap
    (latticeSlack (a + c) m) (latticeSlack a p) hmpos (by rw [hcapcast]; exact hbudget)
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
  have hbq0 : (n - I.card) - R.fiberDimension = R.baseDimension := by
    rw [hIcard]
    omega
  have hH' : (∑ u ∈ I.image b, h u) ≤ n - 2 * R.baseDimension := by rw [hI]; exact hH
  have hK' : (∑ u ∈ I.image b, k u) ≤ n - 2 * R.baseDimension := by rw [hI]; exact hK
  obtain ⟨A, hApoly, hAsm, hAfan, hAlen, hAimage, hqa, hAdegree⟩ :=
    R.exists_focus_slicePolytope hR b I hI hpure a ha hn hedgesA h
      (hH'.trans (Nat.sub_le _ _)) (by intro he; rw [hbq0]; omega)
  obtain ⟨C, hCpoly, hCsm, hCfan, hClen, hCimage, hqc, hCdegree⟩ :=
    R.exists_focus_slicePolytope hR b I hI hpure c hc hn hedgesC k
      (hK'.trans (Nat.sub_le _ _)) (by intro he; rw [hbq0]; omega)
  let dA := displacedSupportLattice a (I.image b) h
  let dC := displacedSupportLattice c (I.image b) k
  let eA := quotientFaceIntegralChart dA b I
  let eC := quotientFaceIntegralChart dC b I
  obtain ⟨mQ, hmQmap, hmQ⟩ := «Σ».exists_quotient_slice_sum_target b I hF a c h k m hm
    (by intro u hu; exact (hsum u (hI ▸ hu)).symm)
  have hmQinterior : embed (n - I.card) mQ ∈ interior (A.minkowskiSum C) :=
    «Σ».quotient_slice_sum_target_interior b I hF a c h k A C hApoly hCpoly hpure
      (IsStrictSupport.isNef Ψ hqa) (IsStrictSupport.isNef Ψ hqc) mQ hmQ
  obtain ⟨pQ, hpQ⟩ := quotientFace_parity_representative dA b I p (by
    intro i hi
    have hbi : b i ∈ I.image b := Finset.mem_image.mpr ⟨i, hi, rfl⟩
    obtain ⟨w, hw⟩ := hpar (b i) (hI ▸ hbi)
    refine ⟨-w, ?_⟩
    have hcomm : (∑ j, p j * b i j) = ∑ j, b i j * p j :=
      Finset.sum_congr rfl (fun j hj => mul_comm _ _)
    rw [hcomm]
    dsimp only [dA, displacedSupportLattice]
    rw [if_pos hbi]
    dsimp only [latticeSlack] at hw
    omega)
  have hAlen' : A.EdgesAtLeast ((n - I.card) - coord.fiberIndices.card) :=
    A.edgesAtLeast_mono hAlen (by rw [hbqdim]; omega)
  have hClen' : C.EdgesAtLeast ((n - I.card) - coord.fiberIndices.card) :=
    C.edgesAtLeast_mono hClen (by rw [hbqdim]; omega)
  have hAdegree' : (coord.fiberIndices.card : ℝ) ≤
      RQ.degree (fun u => (A.integralSupport u : ℝ)) := by
    have hle : (coord.fiberIndices.card : ℝ) ≤ (n : ℝ) := by rw [hrdim]; exact_mod_cast (by omega : R.fiberDimension ≤ n)
    exact hle.trans hAdegree
  have hCdegree' : (coord.fiberIndices.card : ℝ) ≤
      RQ.degree (fun u => (C.integralSupport u : ℝ)) := by
    have hle : (coord.fiberIndices.card : ℝ) ≤ (n : ℝ) := by rw [hrdim]; exact_mod_cast (by omega : R.fiberDimension ≤ n)
    exact hle.trans hCdegree
  have hIH : ParityDimensionStatement ((n - I.card) - coord.fiberIndices.card) := by
    rw [hbqdim]
    exact IH R.baseDimension (by omega)
  obtain ⟨xQ, yQ, hxQ, hyQ, hxyQ, hpQ'⟩ := coord.bundle_parity_of_base_bounds
    (R.focusQuotientRelation_contractible hR b I hI) rfl
    («Σ».completeQuotientStarFan_isPure hpure b I hF)
    A C hAsm hCsm hAfan.symm hCfan.symm hAlen' hClen' hAdegree' hCdegree'
    hIH mQ hmQinterior pQ
  refine ⟨eA.latticeMap xQ, eC.latticeMap yQ, ?_, ?_, ?_, ?_⟩
  · have hx : eA.realMap (embed (n - I.card) xQ) ∈ eA.realMap '' A.carrier :=
      Set.mem_image_of_mem _ hxQ
    rw [hAimage] at hx
    simpa only [IntegralAffineEmbedding.embed_latticeMap] using hx.1
  · have hy : eC.realMap (embed (n - I.card) yQ) ∈ eC.realMap '' C.carrier :=
      Set.mem_image_of_mem _ hyQ
    rw [hCimage] at hy
    simpa only [IntegralAffineEmbedding.embed_latticeMap] using hy.1
  · rw [← quotientFaceIntegralChart_add, hxyQ]
    exact hmQmap
  · obtain ⟨v, hv⟩ := eA.sameParity_latticeMap hpQ'
    obtain ⟨w, hw⟩ := hpQ
    refine ⟨v + w, ?_⟩
    calc
      eA.latticeMap xQ - p =
          (eA.latticeMap xQ - eA.latticeMap pQ) + (eA.latticeMap pQ - p) := by abel
      _ = (v + v) + (w + w) := by rw [hv, hw]
      _ = (v + w) + (v + w) := by abel

/-- The complete selected-locus parity branch on the original polytopes. -/
theorem polytope_near_selected_parity (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hne : R.negative.Nonempty) (hlarge : n < 2 * R.fiberDimension)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q))
    (hbudget : (∑ u ∈ R.negative, latticeSlack (P.integralSupport + Q.integralSupport) m u) + 3 ≤
      2 * ((n : ℤ) - 2 * R.baseDimension))
    (IH : ∀ d : ℕ, d < n → ParityDimensionStatement d) (p : Lattice n) :
    ∃ x y : Lattice n, embed n x ∈ P.carrier ∧ embed n y ∈ Q.carrier ∧
      x + y = m ∧ SameParity x p := by
  have ha := P.integralSupport_isStrictSupport «Σ» hfanP
  have hc := Q.integralSupport_isStrictSupport «Σ» hfanQ
  have hedgesP := P.supportReconstruction_edgesAtLeast «Σ» hpure hfanP hboundP
  have hedgesQ := Q.supportReconstruction_edgesAtLeast «Σ» hpure hfanQ hboundQ
  have hm' : embed n m ∈ interior («Σ».fanPolytope
      (fun u => ((P.integralSupport + Q.integralSupport) u : ℝ))) := by
    rw [«Σ».integralSupport_sum_polytope_eq hpure P Q hfanP hfanQ]
    exact hm
  obtain ⟨x, y, hx, hy, hxy, hp⟩ := «Σ».near_selected_parity_decomposition hpure
    P.integralSupport Q.integralSupport ha hc hedgesP hedgesQ R hR hne hlarge m hm' hbudget IH p
  rw [P.fanPolytope_integralSupport_eq «Σ» hfanP] at hx
  rw [Q.fanPolytope_integralSupport_eq «Σ» hfanQ] at hy
  exact ⟨x, y, hx, hy, hxy, hp⟩

end PaperVerification.ToricGeometry.SmoothCompleteFan
