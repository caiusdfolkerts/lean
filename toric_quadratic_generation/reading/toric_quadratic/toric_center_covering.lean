module

public import PaperVerification.ToricFanPolytopes
public import PaperVerification.ToricInteriorDecomposition
public import PaperVerification.ToricParityClasses

@[expose] public section

/-!
# Lattice summands from the actual nef center polytopes

The finite box covering theorem is applied to the ordinary integer lattice.
For prescribed parity, the two sets are translated by complementary integral
vectors and divided by two. Thus the selected points give literal integral
summands in the requested coset, without a parity assumption on the centers.
The second set may be an ordinary interior; only convexity is used.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators
open PaperVerification.Toric PaperVerification.ToricExchange

section FiniteBoxes

variable {n : ℕ} {J : Type*} [Fintype J]

/-- An actual integral decomposition from a finite convex average of
matched integral-basis unit boxes. The containing convex sets are arbitrary. -/
theorem integral_summands_of_centered_unit_boxes
    (b : J → Module.Basis (Fin n) ℤ (Lattice n))
    (A B : Set (Ambient n)) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (a c : J → Ambient n)
    (hboxA : ∀ (j : J) (t : Fin n → ℝ), (∀ i, |t i| ≤ 1 / 2) →
      a j + ∑ i, t i • integralBasisReal (b j) i ∈ A)
    (hboxB : ∀ (j : J) (t : Fin n → ℝ), (∀ i, |t i| ≤ 1 / 2) →
      c j + ∑ i, t i • integralBasisReal (b j) i ∈ B)
    (m : Lattice n)
    (hm : embed n m ∈ convexHull ℝ (Set.range fun j => a j + c j)) :
    ∃ x y : Lattice n, embed n x ∈ A ∧ embed n y ∈ B ∧ x + y = m := by
  classical
  obtain ⟨p, hp, hpsum, hpm⟩ :=
    exists_probability_of_mem_convexHull_range (fun j => a j + c j) hm
  let L := standardIntegerLattice n
  letI : DiscreteTopology L := standardIntegerLattice_discreteTopology n
  letI : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  have hclosed : IsClosed (L.toAddSubgroup : Set (Ambient n)) :=
    AddSubgroup.isClosed_of_discreteTopology
  have hbL (j : J) (i : Fin n) : integralBasisReal (b j) i ∈ L.toAddSubgroup := by
    rw [integralBasisReal_apply]
    exact (mem_standardIntegerLattice_iff _).mpr ⟨b j i, rfl⟩
  have hmL : embed n m ∈ L.toAddSubgroup :=
    (mem_standardIntegerLattice_iff _).mpr ⟨m, rfl⟩
  obtain ⟨x, hx, y, hy, hxL, hyL, hxy⟩ :=
    finite_basis_boxes_lattice_decomposition_pi (fun j => integralBasisReal (b j))
      L.toAddSubgroup hclosed hbL A B hA hB p hp hpsum a c
      hboxA hboxB (embed n m) hmL hpm.symm
  obtain ⟨xZ, hxZ⟩ := (mem_standardIntegerLattice_iff x).mp hxL
  obtain ⟨yZ, hyZ⟩ := (mem_standardIntegerLattice_iff y).mp hyL
  refine ⟨xZ, yZ, ?_, ?_, ?_⟩
  · simpa only [hxZ] using hx
  · simpa only [hyZ] using hy
  · apply embed_injective n
    simpa only [map_add, hxZ, hyZ] using hxy

theorem convex_double_translate_preimage (A : Set (Ambient n))
    (hA : Convex ℝ A) (e : Ambient n) :
    Convex ℝ {x | e + (2 : ℝ) • x ∈ A} := by
  intro x hx y hy a b ha hb hab
  have h := hA hx hy ha hb hab
  change e + (2 : ℝ) • (a • x + b • y) ∈ A
  have he : e + (2 : ℝ) • (a • x + b • y) =
      a • (e + (2 : ℝ) • x) + b • (e + (2 : ℝ) • y) := by
    calc
      _ = (a + b) • e + (2 : ℝ) • (a • x + b • y) := by rw [hab, one_smul]
      _ = _ := by module
  rw [he]
  exact h

/-- Side-two boxes produce every prescribed parity of the first actual
lattice summand. The centers need not be integral, half-integral, or equal. -/
theorem prescribed_parity_of_centered_side_two_boxes
    (b : J → Module.Basis (Fin n) ℤ (Lattice n))
    (A B : Set (Ambient n)) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (a c : J → Ambient n)
    (hboxA : ∀ (j : J) (t : Fin n → ℝ), (∀ i, |t i| ≤ 1) →
      a j + ∑ i, t i • integralBasisReal (b j) i ∈ A)
    (hboxB : ∀ (j : J) (t : Fin n → ℝ), (∀ i, |t i| ≤ 1) →
      c j + ∑ i, t i • integralBasisReal (b j) i ∈ B)
    (m ε : Lattice n)
    (hm : embed n m ∈ convexHull ℝ (Set.range fun j => a j + c j)) :
    ∃ x y : Lattice n, embed n x ∈ A ∧ embed n y ∈ B ∧
      x + y = m ∧ SameParity x ε := by
  classical
  let e := embed n ε
  let f := embed n (m - ε)
  let A' : Set (Ambient n) := {x | e + (2 : ℝ) • x ∈ A}
  let B' : Set (Ambient n) := {x | f + (2 : ℝ) • x ∈ B}
  let a' : J → Ambient n := fun j => (1 / 2 : ℝ) • (a j - e)
  let c' : J → Ambient n := fun j => (1 / 2 : ℝ) • (c j - f)
  have hef : e + f = embed n m := by
    dsimp [e, f]
    rw [← map_add]
    congr 1
    abel
  have hboxA' (j : J) (t : Fin n → ℝ) (ht : ∀ i, |t i| ≤ 1 / 2) :
      a' j + ∑ i, t i • integralBasisReal (b j) i ∈ A' := by
    change e + (2 : ℝ) • (a' j + ∑ i, t i • integralBasisReal (b j) i) ∈ A
    have heq : e + (2 : ℝ) • (a' j + ∑ i, t i • integralBasisReal (b j) i) =
        a j + ∑ i, (2 * t i) • integralBasisReal (b j) i := by
      dsimp [a']
      rw [smul_add, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
        one_smul, Finset.smul_sum]
      simp only [smul_smul]
      abel
    rw [heq]
    apply hboxA
    intro i
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith [ht i]
  have hboxB' (j : J) (t : Fin n → ℝ) (ht : ∀ i, |t i| ≤ 1 / 2) :
      c' j + ∑ i, t i • integralBasisReal (b j) i ∈ B' := by
    change f + (2 : ℝ) • (c' j + ∑ i, t i • integralBasisReal (b j) i) ∈ B
    have heq : f + (2 : ℝ) • (c' j + ∑ i, t i • integralBasisReal (b j) i) =
        c j + ∑ i, (2 * t i) • integralBasisReal (b j) i := by
      dsimp [c']
      rw [smul_add, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
        one_smul, Finset.smul_sum]
      simp only [smul_smul]
      abel
    rw [heq]
    apply hboxB
    intro i
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith [ht i]
  obtain ⟨p, hp, hpsum, hpm⟩ :=
    exists_probability_of_mem_convexHull_range (fun j => a j + c j) hm
  have hsum' : ∑ j, p j • (a' j + c' j) = 0 := by
    calc
      (∑ j, p j • (a' j + c' j)) =
          ∑ j, (1 / 2 : ℝ) • (p j • (a j + c j) - p j • (e + f)) := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [a', c']
        simp only [smul_add, smul_sub, smul_smul]
        rw [mul_comm (p j) (1 / 2 : ℝ)]
        abel
      _ = (1 / 2 : ℝ) • ((∑ j, p j • (a j + c j)) -
          (∑ j, p j) • (e + f)) := by
        rw [← Finset.smul_sum, Finset.sum_sub_distrib, ← Finset.sum_smul]
      _ = 0 := by rw [hpm, hpsum, one_smul, hef, sub_self, smul_zero]
  have hzero : embed n (0 : Lattice n) ∈
      convexHull ℝ (Set.range fun j => a' j + c' j) := by
    rw [map_zero, ← hsum']
    exact (convex_convexHull ℝ _).sum_mem (fun j _ => hp j) hpsum
      (fun j _ => subset_convexHull ℝ _ (Set.mem_range_self j))
  obtain ⟨x, y, hx, hy, hxy⟩ := integral_summands_of_centered_unit_boxes b A' B'
    (convex_double_translate_preimage A hA e)
    (convex_double_translate_preimage B hB f) a' c' hboxA' hboxB' 0 hzero
  refine ⟨ε + x + x, (m - ε) + y + y, ?_, ?_, ?_, ⟨x, by abel⟩⟩
  · change e + (2 : ℝ) • embed n x ∈ A at hx
    simpa only [map_add, two_smul, e, add_assoc] using hx
  · change f + (2 : ℝ) • embed n y ∈ B at hy
    simpa only [map_add, two_smul, f, add_assoc] using hy
  · calc
      _ = m + (x + y) + (x + y) := by abel
      _ = m := by rw [hxy]; simp

end FiniteBoxes

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- The covered-target branch of the parity argument, on the actual
nef center polytopes and the original containing convex sets. -/
theorem parity_summands_of_nef_centers (hpure : «Σ».IsPure)
    (A B : Set (Ambient n)) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (a c : Lattice n → ℝ) (ha : «Σ».IsNef a) (hc : «Σ».IsNef c)
    (hboxA : ∀ (s : «Σ».fullCones) (t : Fin n → ℝ), (∀ i, |t i| ≤ 1) →
      «Σ».cartierPoint a s + ∑ i, t i • «Σ».cartierBasis s i ∈ A)
    (hboxB : ∀ (s : «Σ».fullCones) (t : Fin n → ℝ), (∀ i, |t i| ≤ 1) →
      «Σ».cartierPoint c s + ∑ i, t i • «Σ».cartierBasis s i ∈ B)
    (m ε : Lattice n) (hm : embed n m ∈ «Σ».fanPolytope (a + c)) :
    ∃ x y : Lattice n, embed n x ∈ A ∧ embed n y ∈ B ∧
      x + y = m ∧ SameParity x ε := by
  have hhull : embed n m ∈ convexHull ℝ
      (Set.range fun s => «Σ».cartierPoint a s + «Σ».cartierPoint c s) := by
    rw [«Σ».fanPolytope_eq_convexHull_cartier hpure (a + c) (IsNef.add «Σ» ha hc)] at hm
    have hpoint : «Σ».cartierPoint (a + c) =
        fun s => «Σ».cartierPoint a s + «Σ».cartierPoint c s := by
      funext s
      exact «Σ».cartierPoint_add a c s
    rw [hpoint] at hm
    exact hm
  exact prescribed_parity_of_centered_side_two_boxes
    (fun s => integralDualBasis («Σ».fullConeBasis s)) A B hA hB
    («Σ».cartierPoint a) («Σ».cartierPoint c) hboxA hboxB m ε hhull

/-- The covered-target branch for unit boxes. Taking `B` to be the actual
interior of the second polytope gives an interior lattice summand. -/
theorem integral_summands_of_nef_centers (hpure : «Σ».IsPure)
    (A B : Set (Ambient n)) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (a c : Lattice n → ℝ) (ha : «Σ».IsNef a) (hc : «Σ».IsNef c)
    (hboxA : ∀ (s : «Σ».fullCones) (t : Fin n → ℝ), (∀ i, |t i| ≤ 1 / 2) →
      «Σ».cartierPoint a s + ∑ i, t i • «Σ».cartierBasis s i ∈ A)
    (hboxB : ∀ (s : «Σ».fullCones) (t : Fin n → ℝ), (∀ i, |t i| ≤ 1 / 2) →
      «Σ».cartierPoint c s + ∑ i, t i • «Σ».cartierBasis s i ∈ B)
    (m : Lattice n) (hm : embed n m ∈ «Σ».fanPolytope (a + c)) :
    ∃ x y : Lattice n, embed n x ∈ A ∧ embed n y ∈ B ∧ x + y = m := by
  have hhull : embed n m ∈ convexHull ℝ
      (Set.range fun s => «Σ».cartierPoint a s + «Σ».cartierPoint c s) := by
    rw [«Σ».fanPolytope_eq_convexHull_cartier hpure (a + c) (IsNef.add «Σ» ha hc)] at hm
    have hpoint : «Σ».cartierPoint (a + c) =
        fun s => «Σ».cartierPoint a s + «Σ».cartierPoint c s := by
      funext s
      exact «Σ».cartierPoint_add a c s
    rw [hpoint] at hm
    exact hm
  exact integral_summands_of_centered_unit_boxes
    (fun s => integralDualBasis («Σ».fullConeBasis s)) A B hA hB
    («Σ».cartierPoint a) («Σ».cartierPoint c) hboxA hboxB m hhull

end SmoothCompleteFan

end PaperVerification.ToricGeometry
