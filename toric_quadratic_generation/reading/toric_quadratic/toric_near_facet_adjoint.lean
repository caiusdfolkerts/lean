module

public import PaperVerification.ToricNearFacetParity
public import PaperVerification.ToricCanonicalSlices

@[expose] public section

/-!
# Adjoint splitting at the first old-facet slice

The first summand has normal height zero and the second has normal height
one. The canonical slice identity carries an interior lattice point of the
second quotient polytope back to an interior lattice point of the original
polytope. Only the ordinary lower-dimensional mixed adjoint statement is used.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical Pointwise

/-- The exact mixed adjoint statement in a fixed dimension. -/
def AdjointDimensionStatement (d : ℕ) : Prop :=
  ∀ P Q : LatticePolytope d, P.Smooth → Q.Smooth → P.SameNormalFan Q →
    P.EdgesAtLeast (d + 1) → Q.EdgesAtLeast (d + 1) →
    ∀ m : Lattice d, embed d m ∈ interior (P.minkowskiSum Q) →
    ∃ x y : Lattice d, embed d x ∈ P.carrier ∧
      embed d y ∈ interior Q.carrier ∧ x + y = m

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem near_facet_adjoint_in_basis (hpure : «Σ».IsPure)
    (a c : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun v => (a v : ℝ)))
    (hc : «Σ».IsStrictSupport (fun v => (c v : ℝ)))
    (hedgesA : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast (n + 1))
    (hedgesC : («Σ».supportLatticePolytope hpure c hc).EdgesAtLeast (n + 1))
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (u : Lattice n) (hI : I.image b = {u}) (hF : I.image b ∈ «Σ».cones)
    (m : Lattice n)
    (hm : embed n m ∈ interior («Σ».fanPolytope (fun v => ((a + c) v : ℝ))))
    (hslack : latticeSlack (a + c) m u = 1)
    (IH : ∀ d : ℕ, d < n → AdjointDimensionStatement d) :
    ∃ x y : Lattice n,
      embed n x ∈ «Σ».fanPolytope (fun v => (a v : ℝ)) ∧
      embed n y ∈ interior («Σ».fanPolytope (fun v => (c v : ℝ))) ∧ x + y = m := by
  have hIcard : I.card = 1 := by
    rw [← Finset.card_image_of_injective I b.injective, hI, Finset.card_singleton]
  have hn : 1 ≤ n := by
    have h := Finset.card_le_card (Finset.subset_univ I)
    simpa only [hIcard, Finset.card_fin] using h
  have huF : u ∈ I.image b := by rw [hI]; exact Finset.mem_singleton_self u
  let hA : Lattice n → ℕ := fun _ => 0
  let hC : Lattice n → ℕ := fun _ => 1
  let dA := displacedSupportLattice a (I.image b) hA
  let dC := displacedSupportLattice c (I.image b) hC
  let Ψ := «Σ».completeQuotientStarFan b I hF
  let eA := quotientFaceIntegralChart dA b I
  let eC := quotientFaceIntegralChart dC b I
  let eSum := quotientFaceIntegralChart (dA + dC) b I
  have hsumA : (∑ v ∈ I.image b, hA v) = 0 := by simp [hA]
  have hsumC : (∑ v ∈ I.image b, hC v) = 1 := by simp [hI, hC]
  obtain ⟨A, hApoly, hAsm, hAfan, hAlen, hAimage⟩ :=
    «Σ».exists_displaced_facePolytope b I hF hpure a ha hedgesA hA (by rw [hsumA]; omega)
  obtain ⟨C, hCpoly, hCsm, hCfan, hClen, hCimage⟩ :=
    «Σ».exists_displaced_facePolytope b I hF hpure c hc hedgesC hC (by rw [hsumC]; omega)
  have hcoeffZ (v : Lattice n) : (dA + dC) v =
      (a + c) v - if v ∈ I.image b then 1 else 0 := by
    dsimp only [dA, dC, displacedSupportLattice, Pi.add_apply, hA, hC]
    split_ifs <;> omega
  have hcoeff : (fun v => ((dA + dC) v : ℝ)) =
      displacedSupport (fun v => ((a + c) v : ℝ)) (I.image b) (fun _ => 1) := by
    funext v
    rw [hcoeffZ]
    simp only [displacedSupport, Pi.sub_apply, facetWeight]
    split_ifs <;> simp
  have hmactive : ∀ i ∈ I,
      (dotProductEquiv ℝ (Fin n) (embed n (b i))) (embed n m) = -((dA + dC) (b i) : ℝ) := by
    intro i hi
    have hbi : b i = u := Finset.mem_singleton.mp (hI ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    rw [hbi, normalRay_pairing_lattice, hcoeffZ, if_pos huF]
    have hz : (∑ j, u j * m j) = -((a + c) u - 1) := by
      dsimp only [latticeSlack] at hslack
      omega
    exact_mod_cast hz
  obtain ⟨mQ, hmQmap⟩ := eSum.exists_latticeMap_of_mem_range m (by
    rw [quotientFaceIntegralChart_realMap]
    exact (mem_range_quotientFaceMap_iff _ b I _).mpr hmactive)
  have hmQreal : quotientFaceMap (fun v => ((dA + dC) v : ℝ)) b I
      (embed (n - I.card) mQ) = embed n m := by
    rw [← quotientFaceIntegralChart_realMap, ← IntegralAffineEmbedding.embed_latticeMap]
    exact congrArg (embed n) hmQmap
  have hmQinterior : embed (n - I.card) mQ ∈ interior (Ψ.fanPolytope
      («Σ».faceSupport b I hF (fun v => ((dA + dC) v : ℝ)))) := by
    rw [hcoeff]
    apply «Σ».quotient_slice_interior b I hF _ (fun _ => 1)
    rw [← hcoeff, hmQreal]
    exact hm
  have hDA : «Σ».IsNef (fun v => (dA v : ℝ)) := by
    rw [displacedSupportLattice_cast]
    apply «Σ».displacedSupport_isNef_of_edges hpure a ha hedgesA _ _
      (fun v hv => Nat.cast_nonneg _)
    simp only [hA, Nat.cast_zero, Finset.sum_const_zero]
    positivity
  have hDC : «Σ».IsNef (fun v => (dC v : ℝ)) := by
    rw [displacedSupportLattice_cast]
    apply «Σ».displacedSupport_isNef_of_edges hpure c hc hedgesC _ _
      (fun v hv => Nat.cast_nonneg _)
    simp only [hI, Finset.sum_singleton, hC, Nat.cast_one]
    exact_mod_cast (by omega : 1 ≤ n + 1)
  have hsumSupport : «Σ».faceSupport b I hF (fun v => ((dA + dC) v : ℝ)) =
      «Σ».faceSupport b I hF (fun v => (dA v : ℝ)) +
        «Σ».faceSupport b I hF (fun v => (dC v : ℝ)) := by
    have hcast : (fun v => ((dA + dC) v : ℝ)) =
        (fun v => (dA v : ℝ)) + (fun v => (dC v : ℝ)) := by funext v; simp
    rw [hcast, «Σ».faceSupport_add]
  have hsumPoly : Ψ.fanPolytope («Σ».faceSupport b I hF
      (fun v => ((dA + dC) v : ℝ))) = A.minkowskiSum C := by
    rw [hsumSupport, Ψ.fanPolytope_add («Σ».completeQuotientStarFan_isPure hpure b I hF)
      _ _ («Σ».faceSupport_isNef b I hF _ hDA) («Σ».faceSupport_isNef b I hF _ hDC),
      ← «Σ».faceSupportLattice_cast, ← «Σ».faceSupportLattice_cast]
    change _ = A.carrier + C.carrier
    rw [← hApoly, ← hCpoly]
  rw [hsumPoly] at hmQinterior
  have hd : n - I.card < n := by omega
  have hAlen' : A.EdgesAtLeast ((n - I.card) + 1) :=
    A.edgesAtLeast_mono hAlen (by rw [hsumA]; omega)
  have hClen' : C.EdgesAtLeast ((n - I.card) + 1) :=
    C.edgesAtLeast_mono hClen (by rw [hsumC]; omega)
  obtain ⟨xQ, yQ, hxQ, hyQ, hxyQ⟩ := IH (n - I.card) hd A C hAsm hCsm
    (hAfan.trans hCfan.symm) hAlen' hClen' mQ hmQinterior
  refine ⟨eA.latticeMap xQ, eC.latticeMap yQ, ?_, ?_, ?_⟩
  · have hx : eA.realMap (embed (n - I.card) xQ) ∈ eA.realMap '' A.carrier :=
      Set.mem_image_of_mem _ hxQ
    rw [hAimage] at hx
    simpa only [IntegralAffineEmbedding.embed_latticeMap] using hx.1
  · rw [hCpoly] at hyQ
    have hyadj := (Ψ.lattice_mem_interior_iff_adjointSupport
      («Σ».faceSupportLattice b I hF dC) yQ).mp hyQ
    have hycanonical : embed (n - I.card) yQ ∈ Ψ.fanPolytope
        (fun v => «Σ».faceSupport b I hF (fun v => (dC v : ℝ)) v - 1) := by
      simpa only [← «Σ».faceSupportLattice_cast, Int.cast_sub, Int.cast_one] using hyadj
    have hcanonical := «Σ».canonical_slice_eq_of_edges b I hF hpure c hc hedgesC
      (fun _ => (1 : ℝ)) (fun v hv => le_rfl) (by simp only [hI, Finset.sum_singleton]; exact_mod_cast (by omega : 1 + 1 ≤ n + 1))
    have hDCcast : (fun v => (dC v : ℝ)) =
        displacedSupport (fun v => (c v : ℝ)) (I.image b) (fun _ => 1) := by
      simpa only [hC, Nat.cast_one] using
        (displacedSupportLattice_cast c (I.image b) hC)
    rw [← hDCcast] at hcanonical
    have hyimage : eC.realMap (embed (n - I.card) yQ) ∈
        {x ∈ «Σ».fanPolytope (fun v => (c v : ℝ) - 1) | ∀ v ∈ I.image b,
          (dotProductEquiv ℝ (Fin n) (embed n v)) x + (c v : ℝ) = 1} := by
      rw [← hcanonical, quotientFaceIntegralChart_realMap]
      exact Set.mem_image_of_mem _ hycanonical
    apply («Σ».lattice_mem_interior_iff_adjointSupport c (eC.latticeMap yQ)).mpr
    simpa only [IntegralAffineEmbedding.embed_latticeMap, Int.cast_sub, Int.cast_one] using hyimage.1
  · rw [← quotientFaceIntegralChart_add, hxyQ]
    exact hmQmap

/-- The old-facet branch of Theorem 1.3 for the literal integer slack. -/
theorem near_facet_adjoint_decomposition (hpure : «Σ».IsPure)
    (a c : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun v => (a v : ℝ)))
    (hc : «Σ».IsStrictSupport (fun v => (c v : ℝ)))
    (hedgesA : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast (n + 1))
    (hedgesC : («Σ».supportLatticePolytope hpure c hc).EdgesAtLeast (n + 1))
    (u : Lattice n) (hu : u ∈ «Σ».rays) (m : Lattice n)
    (hm : embed n m ∈ interior («Σ».fanPolytope (fun v => ((a + c) v : ℝ))))
    (hslack : latticeSlack (a + c) m u = 1)
    (IH : ∀ d : ℕ, d < n → AdjointDimensionStatement d) :
    ∃ x y : Lattice n,
      embed n x ∈ «Σ».fanPolytope (fun v => (a v : ℝ)) ∧
      embed n y ∈ interior («Σ».fanPolytope (fun v => (c v : ℝ))) ∧ x + y = m := by
  have hsing := «Σ».singleton_mem_of_mem_rays hu
  obtain ⟨b, I, hI⟩ := «Σ».smooth {u} hsing
  exact «Σ».near_facet_adjoint_in_basis hpure a c ha hc hedgesA hedgesC b I u hI.symm
    (hI ▸ hsing) m hm hslack IH

end SmoothCompleteFan

end PaperVerification.ToricGeometry
