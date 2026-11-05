module

public import PaperVerification.ToricSliceCoordinates
public import PaperVerification.ToricCenterTargets

@[expose] public section

/-!
# Prescribed parity at the first old-facet slice

The normal parity chooses the two heights zero and one. The actual
saturated slice polytopes share their quotient fan and have dimension
`n-1`; the induction hypothesis supplies the remaining tangent parity.
The zero-dimensional endpoint is included.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open PaperVerification.ToricExchange
open scoped BigOperators Classical Pointwise

/-- The exact mixed parity statement in a fixed dimension, used only as
an induction predicate. -/
def ParityDimensionStatement (d : ℕ) : Prop :=
  ∀ P Q : LatticePolytope d, P.Smooth → Q.Smooth → P.SameNormalFan Q →
    P.EdgesAtLeast d → Q.EdgesAtLeast d →
    ∀ m : Lattice d, embed d m ∈ interior (P.minkowskiSum Q) →
    ∀ p : Lattice d, ∃ x y : Lattice d,
      embed d x ∈ P.carrier ∧ embed d y ∈ Q.carrier ∧ x + y = m ∧ SameParity x p

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem near_facet_parity_in_basis (hpure : «Σ».IsPure)
    (a c : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun v => (a v : ℝ)))
    (hc : «Σ».IsStrictSupport (fun v => (c v : ℝ)))
    (hedgesA : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast n)
    (hedgesC : («Σ».supportLatticePolytope hpure c hc).EdgesAtLeast n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (u : Lattice n) (hI : I.image b = {u}) (hF : I.image b ∈ «Σ».cones)
    (m : Lattice n)
    (hm : embed n m ∈ interior («Σ».fanPolytope (fun v => ((a + c) v : ℝ))))
    (hslack : latticeSlack (a + c) m u = 1)
    (IH : ∀ d : ℕ, d < n → ParityDimensionStatement d) (p : Lattice n) :
    ∃ x y : Lattice n,
      embed n x ∈ «Σ».fanPolytope (fun v => (a v : ℝ)) ∧
      embed n y ∈ «Σ».fanPolytope (fun v => (c v : ℝ)) ∧
      x + y = m ∧ SameParity x p := by
  have hIcard : I.card = 1 := by
    rw [← Finset.card_image_of_injective I b.injective, hI, Finset.card_singleton]
  have hn : 1 ≤ n := by
    have h := Finset.card_le_card (Finset.subset_univ I)
    simpa only [hIcard, Finset.card_fin] using h
  have huF : u ∈ I.image b := by rw [hI]; exact Finset.mem_singleton_self u
  let z := latticeSlack a p u
  let ε : ℕ := (z % 2).toNat
  let η : ℕ := 1 - ε
  have hz0 : 0 ≤ z % 2 := Int.emod_nonneg z (by norm_num)
  have hz2 : z % 2 < 2 := Int.emod_lt_of_pos z (by norm_num)
  have hε : (ε : ℤ) = z % 2 := Int.toNat_of_nonneg hz0
  have hε1 : ε ≤ 1 := by omega
  have hη1 : η ≤ 1 := Nat.sub_le _ _
  have hεη : ε + η = 1 := by omega
  have hεηZ : (ε : ℤ) + (η : ℤ) = 1 := by exact_mod_cast hεη
  let hA : Lattice n → ℕ := fun _ => ε
  let hC : Lattice n → ℕ := fun _ => η
  let dA := displacedSupportLattice a (I.image b) hA
  let dC := displacedSupportLattice c (I.image b) hC
  let Ψ := «Σ».completeQuotientStarFan b I hF
  let eA := quotientFaceIntegralChart dA b I
  let eC := quotientFaceIntegralChart dC b I
  let eSum := quotientFaceIntegralChart (dA + dC) b I
  have hsumA : (∑ v ∈ I.image b, hA v) ≤ 1 := by simpa only [hI, Finset.sum_singleton, hA] using hε1
  have hsumC : (∑ v ∈ I.image b, hC v) ≤ 1 := by simpa only [hI, Finset.sum_singleton, hC] using hη1
  obtain ⟨A, hApoly, hAsm, hAfan, hAlen, hAimage⟩ :=
    «Σ».exists_displaced_facetPolytope b I hF hpure hIcard a ha hedgesA hA hsumA
  obtain ⟨C, hCpoly, hCsm, hCfan, hClen, hCimage⟩ :=
    «Σ».exists_displaced_facetPolytope b I hF hpure hIcard c hc hedgesC hC hsumC
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
    simpa only [hI, Finset.sum_singleton, hA] using
      (by exact_mod_cast hε1.trans hn : (ε : ℝ) ≤ n)
  have hDC : «Σ».IsNef (fun v => (dC v : ℝ)) := by
    rw [displacedSupportLattice_cast]
    apply «Σ».displacedSupport_isNef_of_edges hpure c hc hedgesC _ _
      (fun v hv => Nat.cast_nonneg _)
    simpa only [hI, Finset.sum_singleton, hC] using
      (by exact_mod_cast hη1.trans hn : (η : ℝ) ≤ n)
  have hqA := «Σ».faceSupport_isNef b I hF _ hDA
  have hqC := «Σ».faceSupport_isNef b I hF _ hDC
  have hsumSupport : «Σ».faceSupport b I hF (fun v => ((dA + dC) v : ℝ)) =
      «Σ».faceSupport b I hF (fun v => (dA v : ℝ)) +
        «Σ».faceSupport b I hF (fun v => (dC v : ℝ)) := by
    have hcast : (fun v => ((dA + dC) v : ℝ)) =
        (fun v => (dA v : ℝ)) + (fun v => (dC v : ℝ)) := by funext v; simp
    rw [hcast, «Σ».faceSupport_add]
  have hsumPoly : Ψ.fanPolytope («Σ».faceSupport b I hF
      (fun v => ((dA + dC) v : ℝ))) = A.minkowskiSum C := by
    rw [hsumSupport, Ψ.fanPolytope_add («Σ».completeQuotientStarFan_isPure hpure b I hF)
      _ _ hqA hqC, ← «Σ».faceSupportLattice_cast, ← «Σ».faceSupportLattice_cast]
    change _ = A.carrier + C.carrier
    rw [← hApoly, ← hCpoly]
  rw [hsumPoly] at hmQinterior
  obtain ⟨pQ, hpQ⟩ := quotientFace_parity_representative dA b I p (by
    intro i hi
    have hbi : b i = u := Finset.mem_singleton.mp (hI ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    rw [hbi]
    refine ⟨z / 2, ?_⟩
    have hcomm : (∑ j, p j * u j) = ∑ j, u j * p j :=
      Finset.sum_congr rfl (fun j hj => mul_comm _ _)
    rw [hcomm]
    dsimp only [dA, displacedSupportLattice, hA]
    rw [if_pos huF]
    have hz : z = (∑ j, u j * p j) + a u := rfl
    omega)
  have hd : n - I.card < n := by omega
  obtain ⟨xQ, yQ, hxQ, hyQ, hxyQ, hpQ'⟩ := IH (n - I.card) hd A C hAsm hCsm
    (hAfan.trans hCfan.symm) hAlen hClen mQ hmQinterior pQ
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

/-- The old-facet branch of Theorem 1.2, stated for an arbitrary actual
primitive old ray and the literal integer slack. -/
theorem near_facet_parity_decomposition (hpure : «Σ».IsPure)
    (a c : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun v => (a v : ℝ)))
    (hc : «Σ».IsStrictSupport (fun v => (c v : ℝ)))
    (hedgesA : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast n)
    (hedgesC : («Σ».supportLatticePolytope hpure c hc).EdgesAtLeast n)
    (u : Lattice n) (hu : u ∈ «Σ».rays)
    (m : Lattice n)
    (hm : embed n m ∈ interior («Σ».fanPolytope (fun v => ((a + c) v : ℝ))))
    (hslack : latticeSlack (a + c) m u = 1)
    (IH : ∀ d : ℕ, d < n → ParityDimensionStatement d) (p : Lattice n) :
    ∃ x y : Lattice n,
      embed n x ∈ «Σ».fanPolytope (fun v => (a v : ℝ)) ∧
      embed n y ∈ «Σ».fanPolytope (fun v => (c v : ℝ)) ∧
      x + y = m ∧ SameParity x p := by
  have hsing := «Σ».singleton_mem_of_mem_rays hu
  obtain ⟨b, I, hI⟩ := «Σ».smooth {u} hsing
  exact «Σ».near_facet_parity_in_basis hpure a c ha hc hedgesA hedgesC b I u hI.symm
    (hI ▸ hsing) m hm hslack IH p

end SmoothCompleteFan

end PaperVerification.ToricGeometry
