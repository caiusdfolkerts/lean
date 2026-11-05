module

public import PaperVerification.ToricQuotientFaceSupport
public import PaperVerification.ToricDisplacedEdgeBounds
public import PaperVerification.ToricSmoothFaces

@[expose] public section

/-!
# Actual smooth lattice polytopes of displaced faces

Integral restriction coefficients construct a full-dimensional smooth
polytope in the saturated face lattice. Its exact fan, affine image, and
all edge bounds follow from the preceding geometric results.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b ∈ «Σ».cones)

theorem isStrictSupport_of_dimension_zero {d : ℕ} (Ψ : SmoothCompleteFan d)
    (hd : d = 0) (a : Lattice d → ℝ) : Ψ.IsStrictSupport a := by
  subst d
  have hnoray (u : Lattice 0) : u ∉ Ψ.rays := by
    intro hu
    exact Ψ.ray_ne_zero hu (Subsingleton.elim u 0)
  intro s hs
  refine ⟨0, ?_, ?_⟩
  · intro u hu
    exact (hnoray u (Ψ.ray_mem_of_mem_cone hs hu)).elim
  · intro u hu hus
    exact (hnoray u hu).elim

/-- Global nefness is enough when the actual restriction is strictly
supported. This includes collapsed normal directions at an endpoint. -/
theorem exists_face_supportPolytope_of_nefRestriction (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsNef (fun u => (a u : ℝ)))
    (hq : («Σ».completeQuotientStarFan b I hF).IsStrictSupport
      (fun u => («Σ».faceSupportLattice b I hF a u : ℝ))) :
    ∃ Q : LatticePolytope (n - I.card),
      Q.carrier = («Σ».completeQuotientStarFan b I hF).fanPolytope
        (fun u => («Σ».faceSupportLattice b I hF a u : ℝ)) ∧
      Q.Smooth ∧ Q.normalFan = («Σ».completeQuotientStarFan b I hF).realCones ∧
      (quotientFaceIntegralChart a b I).realMap '' Q.carrier =
        «Σ».supportFace (fun u => (a u : ℝ)) (I.image b) := by
  let Ψ := «Σ».completeQuotientStarFan b I hF
  obtain ⟨Q, hQ, hQs, hQfan⟩ :=
    Ψ.exists_smooth_latticePolytope_of_integral_strictSupport
      («Σ».completeQuotientStarFan_isPure hpure b I hF)
      («Σ».faceSupportLattice b I hF a) hq
  refine ⟨Q, hQ, hQs, hQfan, ?_⟩
  rw [hQ]
  exact «Σ».quotientFaceIntegralChart_image_fanPolytope b I hF hpure a ha

/-- Actual smooth face polytopes, with exact normal fan and unchanged edge
bound, in the chosen saturated chart. -/
theorem exists_face_supportPolytope (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    (P : LatticePolytope n) (hP : P.carrier = «Σ».fanPolytope (fun u => (a u : ℝ)))
    {bound : ℕ} (hbound : P.EdgesAtLeast bound) :
    ∃ Q : LatticePolytope (n - I.card),
      Q.carrier = («Σ».completeQuotientStarFan b I hF).fanPolytope
        (fun u => («Σ».faceSupportLattice b I hF a u : ℝ)) ∧
      Q.Smooth ∧ Q.normalFan = («Σ».completeQuotientStarFan b I hF).realCones ∧
      Q.EdgesAtLeast bound ∧
      (quotientFaceIntegralChart a b I).realMap '' Q.carrier =
        «Σ».supportFace (fun u => (a u : ℝ)) (I.image b) := by
  let Ψ := «Σ».completeQuotientStarFan b I hF
  let c := «Σ».faceSupportLattice b I hF a
  have hcpure : Ψ.IsPure := «Σ».completeQuotientStarFan_isPure hpure b I hF
  have hc : Ψ.IsStrictSupport (fun u => (c u : ℝ)) := by
    change Ψ.IsStrictSupport (fun u => («Σ».faceSupportLattice b I hF a u : ℝ))
    rw [«Σ».faceSupportLattice_cast]
    exact «Σ».faceSupport_isStrictSupport b I hF _ ha
  obtain ⟨Q, hQ, hQs, hQfan⟩ :=
    Ψ.exists_smooth_latticePolytope_of_integral_strictSupport hcpure c hc
  have himage : (quotientFaceIntegralChart a b I).realMap '' Q.carrier =
      «Σ».supportFace (fun u => (a u : ℝ)) (I.image b) := by
    rw [hQ]
    exact «Σ».quotientFaceIntegralChart_image_fanPolytope b I hF hpure a
      (IsStrictSupport.isNef «Σ» ha)
  have hface : IsExtreme ℝ P.carrier
      («Σ».supportFace (fun u => (a u : ℝ)) (I.image b)) := by
    rw [hP]
    exact «Σ».supportFace_isExtreme _ _ (fun u hu => «Σ».ray_mem_of_mem_cone hF hu)
  have hlength := P.edgesAtLeast_face_chart hbound _ hface Q
    (quotientFaceIntegralChart a b I) himage
  exact ⟨Q, hQ, hQs, hQfan, hlength, himage⟩

def displacedSupportLattice (a : Lattice n → ℤ)
    (T : Finset (Lattice n)) (h : Lattice n → ℕ) : Lattice n → ℤ :=
  fun u => a u - if u ∈ T then (h u : ℤ) else 0

theorem displacedSupportLattice_cast (a : Lattice n → ℤ)
    (T : Finset (Lattice n)) (h : Lattice n → ℕ) :
    (fun u => (displacedSupportLattice a T h u : ℝ)) =
      displacedSupport (fun u => (a u : ℝ)) T (fun u => (h u : ℝ)) := by
  funext u
  simp only [displacedSupportLattice, displacedSupport, Pi.sub_apply, facetWeight]
  split_ifs <;> simp

/-- Exact integral slices below the original edge threshold, with genuine
smoothness, a common actual quotient fan, saturation, and all edge bounds. -/
theorem exists_displaced_facePolytope (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (h : Lattice n → ℕ) (hbudget : (∑ u ∈ I.image b, h u) < e) :
    ∃ Q : LatticePolytope (n - I.card),
      Q.carrier = («Σ».completeQuotientStarFan b I hF).fanPolytope
        (fun u => («Σ».faceSupportLattice b I hF
          (displacedSupportLattice a (I.image b) h) u : ℝ)) ∧
      Q.Smooth ∧ Q.normalFan = («Σ».completeQuotientStarFan b I hF).realCones ∧
      Q.EdgesAtLeast (e - ∑ u ∈ I.image b, h u) ∧
      (quotientFaceIntegralChart (displacedSupportLattice a (I.image b) h) b I).realMap ''
        Q.carrier = {x ∈ «Σ».fanPolytope (fun u => (a u : ℝ)) | ∀ u ∈ I.image b,
          (dotProductEquiv ℝ (Fin n) (embed n u)) x + (a u : ℝ) = (h u : ℝ)} := by
  let d := displacedSupportLattice a (I.image b) h
  have hsum : (∑ u ∈ I.image b, (h u : ℝ)) = (∑ u ∈ I.image b, h u : ℕ) := by
    simp only [Nat.cast_sum]
  have hbudgetR : (∑ u ∈ I.image b, (h u : ℝ)) < (e : ℝ) := by
    rw [hsum]
    exact_mod_cast hbudget
  have hd : «Σ».IsStrictSupport (fun u => (d u : ℝ)) := by
    rw [displacedSupportLattice_cast]
    exact «Σ».displacedSupport_isStrictSupport_of_edges hpure a ha hedges _ _
      (fun u hu => Nat.cast_nonneg _) hbudgetR
  let D := «Σ».supportLatticePolytope hpure d hd
  have hDbound : D.EdgesAtLeast (e - ∑ u ∈ I.image b, h u) := by
    apply «Σ».displacedSupport_edgesAtLeast hpure a d ha hd (by omega) hedges
      (I.image b) (fun u => (h u : ℝ)) (fun u hu => Nat.cast_nonneg _)
      (displacedSupportLattice_cast a _ h) hbudgetR.le
    rw [hsum, Nat.cast_sub hbudget.le]
  obtain ⟨Q, hQ, hQs, hQfan, hQbound, himage⟩ :=
    «Σ».exists_face_supportPolytope b I hF hpure d hd D
      («Σ».supportLatticePolytope_carrier hpure d hd) hDbound
  refine ⟨Q, hQ, hQs, hQfan, hQbound, ?_⟩
  rw [himage, displacedSupportLattice_cast]
  exact «Σ».displaced_supportFace_eq_slice _ _ _ (fun u hu => Nat.cast_nonneg _)

/-- The first normal slice of an actual facet has the required dimension
and edge bound, including the zero-dimensional endpoint when `n=1`. -/
theorem exists_displaced_facetPolytope (hpure : «Σ».IsPure)
    (hIcard : I.card = 1)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast n)
    (h : Lattice n → ℕ) (hbudget : (∑ u ∈ I.image b, h u) ≤ 1) :
    ∃ Q : LatticePolytope (n - I.card),
      Q.carrier = («Σ».completeQuotientStarFan b I hF).fanPolytope
        (fun u => («Σ».faceSupportLattice b I hF
          (displacedSupportLattice a (I.image b) h) u : ℝ)) ∧
      Q.Smooth ∧ Q.normalFan = («Σ».completeQuotientStarFan b I hF).realCones ∧
      Q.EdgesAtLeast (n - I.card) ∧
      (quotientFaceIntegralChart (displacedSupportLattice a (I.image b) h) b I).realMap ''
        Q.carrier = {x ∈ «Σ».fanPolytope (fun u => (a u : ℝ)) | ∀ u ∈ I.image b,
          (dotProductEquiv ℝ (Fin n) (embed n u)) x + (a u : ℝ) = (h u : ℝ)} := by
  have hIn : I.card ≤ n := by
    simpa only [Finset.card_fin] using Finset.card_le_card (Finset.subset_univ I)
  by_cases hlt : (∑ u ∈ I.image b, h u) < n
  · obtain ⟨Q, hQ, hQs, hQfan, hQbound, himage⟩ :=
      «Σ».exists_displaced_facePolytope b I hF hpure a ha hedges h hlt
    exact ⟨Q, hQ, hQs, hQfan, Q.edgesAtLeast_mono hQbound (by omega), himage⟩
  · have hn : n = 1 := by omega
    have hdim : n - I.card = 0 := by omega
    let d := displacedSupportLattice a (I.image b) h
    have hsum : (∑ u ∈ I.image b, (h u : ℝ)) = (∑ u ∈ I.image b, h u : ℕ) := by
      simp only [Nat.cast_sum]
    have hd : «Σ».IsNef (fun u => (d u : ℝ)) := by
      rw [displacedSupportLattice_cast]
      apply «Σ».displacedSupport_isNef_of_edges hpure a ha hedges _ _
        (fun u hu => Nat.cast_nonneg _)
      rw [hsum]
      exact_mod_cast (by omega : (∑ u ∈ I.image b, h u) ≤ n)
    have hq := isStrictSupport_of_dimension_zero («Σ».completeQuotientStarFan b I hF) hdim
      (fun u => («Σ».faceSupportLattice b I hF d u : ℝ))
    obtain ⟨Q, hQ, hQs, hQfan, himage⟩ :=
      «Σ».exists_face_supportPolytope_of_nefRestriction b I hF hpure d hd hq
    have hQbound : Q.EdgesAtLeast (n - I.card) := by
      apply (Q.edgesAtLeast_iff (n - I.card)).mpr
      intro x y hxy
      calc
        n - I.card = 0 := hdim
        _ ≤ LatticePolytope.latticeLength x y := Nat.zero_le _
    refine ⟨Q, hQ, hQs, hQfan, hQbound, ?_⟩
    rw [himage, displacedSupportLattice_cast]
    exact «Σ».displaced_supportFace_eq_slice _ _ _ (fun u hu => Nat.cast_nonneg _)

end PaperVerification.ToricGeometry.SmoothCompleteFan
