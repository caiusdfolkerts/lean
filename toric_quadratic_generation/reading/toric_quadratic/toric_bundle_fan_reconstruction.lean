module

public import PaperVerification.ToricBundleFanAllocation
public import PaperVerification.ToricBundleFanAverages
public import PaperVerification.ToricAdjointSupport


@[expose] public section
/-!
# Interior, addition, and parity in the actual bundle lattice

The homogeneous slice coordinates describe the ambient topological interior,
the ordinary integer lattice addition, and the doubled integer lattice.
These are reconstruction theorems, not extra structure imposed on a bundle.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

open Set
open scoped BigOperators Classical
open PaperVerification.ToricExchange

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} {R : «Σ».PrimitiveRelation}
  (c : R.BundleCoordinates)

theorem point_mem_interior_fanPolytope_iff (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a α : Lattice n → ℝ)
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v)
    (y : Ambient (n - c.fiberIndices.card)) :
    c.point a α y ∈ interior («Σ».fanPolytope a) ↔
      (∀ v ∈ R.positive, 0 < α v) ∧
        y ∈ interior (c.baseFan.fanPolytope (c.baseWeight hR hN a α)) := by
  rw [«Σ».interior_fanPolytope_eq, c.baseFan.interior_fanPolytope_eq]
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · intro v hv
      have h := hx v (R.primitive.1 hv)
      rw [c.point_pairing_positive hN a α hα y hv] at h
      linarith
    · intro q hq
      have hv := c.baseRayLift_mem hR hN hq
      have h := hx (c.baseRayLift hR hN q) (Finset.mem_sdiff.mp hv).1
      have he := c.nonfiber_slack_identity hR hN a α y hv
      rw [c.quotient_baseRayLift hR hN hq] at he
      linarith
  · rintro ⟨hα0, hy⟩ v hv
    by_cases hvP : v ∈ R.positive
    · rw [c.point_pairing_positive hN a α hα y hvP]
      linarith [hα0 v hvP]
    · have hv' := Finset.mem_sdiff.mpr ⟨hv, hvP⟩
      have hq := (c.base_ray_iff hR hN _).mpr ⟨v, hv', rfl⟩
      have h := hy (c.quotientLattice v) hq
      have he := c.nonfiber_slack_identity hR hN a α y hv'
      linarith

def integerHomogeneousWeight (c : R.BundleCoordinates) (a : Lattice n → ℤ) (x v : Lattice n) : ℤ :=
  a v + ∑ i, v i * x i

theorem integerHomogeneousWeight_cast (a : Lattice n → ℤ) (x v : Lattice n) :
    (c.integerHomogeneousWeight a x v : ℝ) =
      c.homogeneousWeight (fun u => (a u : ℝ)) (embed n x) v := by
  rw [homogeneousWeight, SmoothCompleteFan.normalRay_pairing_lattice]
  simp only [integerHomogeneousWeight, Int.cast_add]

theorem integerHomogeneousWeight_total (hN : R.negative = ∅)
    (a : Lattice n → ℤ) (x : Lattice n) :
    (∑ v ∈ R.positive, c.integerHomogeneousWeight a x v) =
      ∑ v ∈ R.positive, a v := by
  have h := c.homogeneousWeight_total hN (fun v => (a v : ℝ)) (embed n x)
  simp only [← c.integerHomogeneousWeight_cast] at h
  exact_mod_cast h

theorem integerHomogeneousWeight_pos_of_interior (a : Lattice n → ℤ)
    (x : Lattice n) (hx : embed n x ∈ interior («Σ».fanPolytope (fun v => (a v : ℝ))))
    {v : Lattice n} (hv : v ∈ «Σ».rays) :
    0 < c.integerHomogeneousWeight a x v := by
  have h := («Σ».interior_fanPolytope_eq (fun u => (a u : ℝ)) ▸ hx) v hv
  have hpos : (0 : ℝ) < c.integerHomogeneousWeight a x v := by
    rw [c.integerHomogeneousWeight_cast, homogeneousWeight]
    linarith
  exact_mod_cast hpos

theorem fiberIndices_card_le : c.fiberIndices.card ≤ n := by
  simpa only [Fintype.card_fin] using Finset.card_le_univ c.fiberIndices

theorem baseDimension_lt : n - c.fiberIndices.card < n := by
  have hpos : 0 < c.fiberIndices.card := by
    rw [c.fiberIndices_card]
    exact R.fiberDimension_pos
  have hle := c.fiberIndices_card_le
  omega

theorem integerPoint_homogeneousWeight_basePoint (a : Lattice n → ℤ) (x : Lattice n) :
    c.integerPoint a (c.integerHomogeneousWeight a x) (c.integerBasePoint x) = x := by
  apply embed_injective n
  rw [c.integerPoint_compatible, c.integerBasePoint_compatible]
  have he : (fun v => (c.integerHomogeneousWeight a x v : ℝ)) =
      c.homogeneousWeight (fun v => (a v : ℝ)) (embed n x) := by
    funext v
    exact c.integerHomogeneousWeight_cast a x v
  rw [he]
  exact c.point_homogeneousWeight_basePoint _ _

theorem integerPoint_congr_weights (a α β : Lattice n → ℤ)
    (h : ∀ i ∈ c.fiberIndices, α (c.basis i) = β (c.basis i))
    (y : Lattice (n - c.fiberIndices.card)) :
    c.integerPoint a α y = c.integerPoint a β y := by
  unfold integerPoint integerPointFunctional
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i hi]

theorem integerPoint_add (a b α β : Lattice n → ℤ)
    (y z : Lattice (n - c.fiberIndices.card)) :
    c.integerPoint (a + b) (α + β) (y + z) =
      c.integerPoint a α y + c.integerPoint b β z := by
  funext j
  simp only [integerPoint, integerDualVector, integerPointFunctional,
    LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, Pi.add_apply, smul_eq_mul, map_add]
  have he (i : Fin n) :
      (α (c.basis i) + β (c.basis i) - (a (c.basis i) + b (c.basis i))) *
          c.basis.coord i (Pi.basisFun ℤ (Fin n) j) =
      (α (c.basis i) - a (c.basis i)) * c.basis.coord i (Pi.basisFun ℤ (Fin n) j) +
      (β (c.basis i) - b (c.basis i)) * c.basis.coord i (Pi.basisFun ℤ (Fin n) j) := by ring
  simp only [he, Finset.sum_add_distrib]
  ring

theorem integerPoint_sub (a b α β : Lattice n → ℤ)
    (y z : Lattice (n - c.fiberIndices.card)) :
    c.integerPoint (a - b) (α - β) (y - z) =
      c.integerPoint a α y - c.integerPoint b β z := by
  have h := c.integerPoint_add (a - b) b (α - β) β (y - z) z
  simp only [sub_add_cancel] at h
  exact eq_sub_iff_add_eq.mpr h.symm

theorem integerBasePoint_add (x y : Lattice n) :
    c.integerBasePoint (x + y) = c.integerBasePoint x + c.integerBasePoint y := by
  funext j
  simp [integerBasePoint, integerDualVector, map_add]

theorem integerBasePoint_integerPoint (a α : Lattice n → ℤ)
    (y : Lattice (n - c.fiberIndices.card)) :
    c.integerBasePoint (c.integerPoint a α y) = y := by
  apply embed_injective (n - c.fiberIndices.card)
  rw [c.integerBasePoint_compatible, c.integerPoint_compatible, c.basePoint_point]

/-- Prescribed parity on the independent integral fiber coordinates,
together with the ordinary base parity class, is exactly sufficient for
the full ambient doubled-lattice condition. -/
theorem integerPoint_sameParity (a α : Lattice n → ℤ) (x : Lattice n)
    (y : Lattice (n - c.fiberIndices.card))
    (hfiber : ∀ i ∈ c.fiberIndices,
      (α (c.basis i) - c.integerHomogeneousWeight a x (c.basis i)) % 2 = 0)
    (hbase : SameParity y (c.integerBasePoint x)) :
    SameParity (c.integerPoint a α y) x := by
  let p := c.integerHomogeneousWeight a x
  let δ : Lattice n → ℤ := fun v => (α v - p v) / 2
  obtain ⟨z, hz⟩ := hbase
  refine ⟨c.integerPoint 0 δ z, ?_⟩
  have hf (i : Fin n) (hi : i ∈ c.fiberIndices) :
      (α - p) (c.basis i) = (δ + δ) (c.basis i) := by
    have h := hfiber i hi
    change α (c.basis i) - p (c.basis i) = δ (c.basis i) + δ (c.basis i)
    dsimp [δ, p] at *
    omega
  calc
    c.integerPoint a α y - x =
        c.integerPoint a α y - c.integerPoint a p (c.integerBasePoint x) := by
      rw [c.integerPoint_homogeneousWeight_basePoint]
    _ = c.integerPoint 0 (α - p) (y - c.integerBasePoint x) := by
      rw [← c.integerPoint_sub, sub_self]
    _ = c.integerPoint 0 (δ + δ) (z + z) := by
      rw [hz]
      exact c.integerPoint_congr_weights 0 (α - p) (δ + δ) hf _
    _ = c.integerPoint 0 δ z + c.integerPoint 0 δ z := by
      simpa only [zero_add] using c.integerPoint_add 0 0 δ δ z z

theorem integerPoint_sum_eq (a b α β : Lattice n → ℤ)
    (m : Lattice n) (y z : Lattice (n - c.fiberIndices.card))
    (hweights : ∀ v ∈ R.positive,
      α v + β v = c.integerHomogeneousWeight (a + b) m v)
    (hbase : y + z = c.integerBasePoint m) :
    c.integerPoint a α y + c.integerPoint b β z = m := by
  rw [← c.integerPoint_add, hbase]
  calc
    c.integerPoint (a + b) (α + β) (c.integerBasePoint m) =
        c.integerPoint (a + b) (c.integerHomogeneousWeight (a + b) m)
          (c.integerBasePoint m) := by
      apply c.integerPoint_congr_weights
      intro i hi
      exact hweights _ (c.fiber_subset_positive (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
    _ = m := c.integerPoint_homogeneousWeight_basePoint _ _

theorem basePoint_mem_interior_sum_support (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a b α β : Lattice n → ℝ) (x : Ambient n)
    (hx : x ∈ interior («Σ».fanPolytope (a + b)))
    (hweights : ∀ v ∈ R.positive,
      α v + β v = c.homogeneousWeight (a + b) x v) :
    c.basePoint x ∈ interior (c.baseFan.fanPolytope
      (c.baseWeight hR hN a α + c.baseWeight hR hN b β)) := by
  have hx' : c.point (a + b) (c.homogeneousWeight (a + b) x) (c.basePoint x) ∈
      interior («Σ».fanPolytope (a + b)) := by
    rw [c.point_homogeneousWeight_basePoint]
    exact hx
  have hbase := ((c.point_mem_interior_fanPolytope_iff hR hN (a + b)
    (c.homogeneousWeight (a + b) x) (c.homogeneousWeight_total hN _ _) _).mp hx').2
  have he := c.baseWeight_congr_weight hR hN (a + b) (α + β)
    (c.homogeneousWeight (a + b) x) hweights
  rw [← he, c.baseWeight_add] at hbase
  exact hbase

theorem integerPoint_mem_fanPolytope_iff (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a α : Lattice n → ℤ)
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v)
    (y : Lattice (n - c.fiberIndices.card)) :
    embed n (c.integerPoint a α y) ∈ «Σ».fanPolytope (fun v => (a v : ℝ)) ↔
      (∀ v ∈ R.positive, 0 ≤ α v) ∧
        embed (n - c.fiberIndices.card) y ∈ c.baseFan.fanPolytope
          (fun q => (c.integerBaseWeight hR hN a α q : ℝ)) := by
  have hαR : (∑ v ∈ R.positive, (α v : ℝ)) = ∑ v ∈ R.positive, (a v : ℝ) := by
    exact_mod_cast hα
  rw [c.integerPoint_compatible, c.point_mem_fanPolytope_iff hR hN _ _ hαR]
  have he : (fun q => (c.integerBaseWeight hR hN a α q : ℝ)) =
      c.baseWeight hR hN (fun v => (a v : ℝ)) (fun v => (α v : ℝ)) := by
    funext q
    exact c.integerBaseWeight_cast hR hN a α q
  rw [he]
  constructor
  · rintro ⟨hα0, hy⟩
    refine ⟨?_, hy⟩
    intro v hv
    have h := hα0 v hv
    change (0 : ℝ) ≤ (α v : ℝ) at h
    exact_mod_cast h
  · rintro ⟨hα0, hy⟩
    refine ⟨?_, hy⟩
    intro v hv
    change (0 : ℝ) ≤ (α v : ℝ)
    exact_mod_cast hα0 v hv

theorem integerPoint_mem_interior_fanPolytope_iff (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a α : Lattice n → ℤ)
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v)
    (y : Lattice (n - c.fiberIndices.card)) :
    embed n (c.integerPoint a α y) ∈ interior («Σ».fanPolytope (fun v => (a v : ℝ))) ↔
      (∀ v ∈ R.positive, 0 < α v) ∧
        embed (n - c.fiberIndices.card) y ∈ interior (c.baseFan.fanPolytope
          (fun q => (c.integerBaseWeight hR hN a α q : ℝ))) := by
  have hαR : (∑ v ∈ R.positive, (α v : ℝ)) = ∑ v ∈ R.positive, (a v : ℝ) := by
    exact_mod_cast hα
  rw [c.integerPoint_compatible, c.point_mem_interior_fanPolytope_iff hR hN _ _ hαR]
  have he : (fun q => (c.integerBaseWeight hR hN a α q : ℝ)) =
      c.baseWeight hR hN (fun v => (a v : ℝ)) (fun v => (α v : ℝ)) := by
    funext q
    exact c.integerBaseWeight_cast hR hN a α q
  rw [he]
  simp only [Int.cast_pos]

theorem integerBasePoint_mem_interior_sum_support (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a b α β : Lattice n → ℤ) (m : Lattice n)
    (hm : embed n m ∈ interior («Σ».fanPolytope (fun v => ((a + b) v : ℝ))))
    (hweights : ∀ v ∈ R.positive,
      α v + β v = c.integerHomogeneousWeight (a + b) m v) :
    embed (n - c.fiberIndices.card) (c.integerBasePoint m) ∈
      interior (c.baseFan.fanPolytope
        ((fun q => (c.integerBaseWeight hR hN a α q : ℝ)) +
          (fun q => (c.integerBaseWeight hR hN b β q : ℝ)))) := by
  rw [c.integerBasePoint_compatible]
  have hsum : (fun v => ((a + b) v : ℝ)) =
      (fun v => (a v : ℝ)) + (fun v => (b v : ℝ)) := by
    funext v
    simp
  rw [hsum] at hm
  have hw (v : Lattice n) (hv : v ∈ R.positive) :
      (α v : ℝ) + (β v : ℝ) =
        c.homogeneousWeight ((fun u => (a u : ℝ)) + (fun u => (b u : ℝ)))
          (embed n m) v := by
    rw [← hsum, ← c.integerHomogeneousWeight_cast]
    exact_mod_cast hweights v hv
  have h := c.basePoint_mem_interior_sum_support hR hN
    (fun v => (a v : ℝ)) (fun v => (b v : ℝ))
    (fun v => (α v : ℝ)) (fun v => (β v : ℝ)) (embed n m) hm hw
  have hA : (fun q => (c.integerBaseWeight hR hN a α q : ℝ)) =
      c.baseWeight hR hN (fun v => (a v : ℝ)) (fun v => (α v : ℝ)) := by
    funext q
    exact c.integerBaseWeight_cast hR hN a α q
  have hB : (fun q => (c.integerBaseWeight hR hN b β q : ℝ)) =
      c.baseWeight hR hN (fun v => (b v : ℝ)) (fun v => (β v : ℝ)) := by
    funext q
    exact c.integerBaseWeight_cast hR hN b β q
  simpa only [hA, hB] using h

end PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation.BundleCoordinates
