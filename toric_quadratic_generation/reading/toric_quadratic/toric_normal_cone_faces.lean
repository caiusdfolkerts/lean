module
public import PaperVerification.ToricDualNormalCone
@[expose] public section
/-!
# Intersections of actual normal cones

An intersection with another point's normal cone is the zero-coordinate face
cut out by the displacement to that point. The proof expands a normal in an
actual dual integral basis and uses nonnegativity of every summand.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.LatticePolytope

open Set
open scoped BigOperators

variable {n : ℕ} (P : LatticePolytope n)

/-- A normal supports two carrier points precisely when its support value
agrees at those points. -/
theorem mem_normalCone_inter_iff (v w : Ambient n)
    (hv : v ∈ P.carrier) (hw : w ∈ P.carrier) (u : Ambient n) :
    u ∈ P.normalCone v ∩ P.normalCone w ↔
      u ∈ P.normalCone v ∧ (∑ j, u j * (w j - v j)) = 0 := by
  let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) u
  have hmem (x : Ambient n) :
      u ∈ P.normalCone x ↔ ∀ y ∈ P.carrier, f x ≤ f y := by
    change (∀ y ∈ P.carrier, 0 ≤ f (y - x)) ↔ _
    simp only [map_sub, sub_nonneg]
  have hp : (∑ j, u j * (w j - v j)) = f w - f v := by
    change f (w - v) = _
    exact f.map_sub w v
  change (u ∈ P.normalCone v ∧ u ∈ P.normalCone w) ↔ _
  simp only [hmem v, hmem w, hp]
  constructor
  · rintro ⟨huv, huw⟩
    exact ⟨huv, sub_eq_zero.mpr (le_antisymm (huw v hv) (huv w hw))⟩
  · rintro ⟨huv, heq⟩
    refine ⟨huv, ?_⟩
    intro y hy
    rw [sub_eq_zero.mp heq]
    exact huv y hy

/-- In any genuine integral basis generating the normal cone at v, its
intersection with the cone at w is the coordinate face consisting of those
primitive normals that vanish on w-v. -/
theorem normalCone_inter_eq_latticeRayCone
    (v w : Ambient n) (hv : v ∈ P.carrier) (hw : w ∈ P.carrier)
    (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hcone : P.normalCone v =
      (latticeRayCone (Finset.univ.image d) : Set (Ambient n))) :
    P.normalCone v ∩ P.normalCone w =
      (latticeRayCone ((Finset.univ.filter (fun i =>
        (∑ j, embed n (d i) j * (w j - v j)) = 0)).image d) : Set (Ambient n)) := by
  classical
  let b := integralBasisReal d
  let height : Fin n → ℝ := fun i => ∑ j, embed n (d i) j * (w j - v j)
  have hheight (i : Fin n) : 0 ≤ height i := by
    have hi : embed n (d i) ∈ P.normalCone v := by
      rw [hcone]
      exact latticeRayCone_generator _ (Finset.mem_image.mpr
        ⟨i, Finset.mem_univ i, rfl⟩)
    exact hi w hw
  have hmem (u : Ambient n) :
      u ∈ P.normalCone v ↔ ∀ i, 0 ≤ b.repr u i := by
    rw [hcone]
    change u ∈ latticeRayCone (Finset.univ.image d) ↔ _
    rw [mem_latticeRayCone_basis_iff]
    simp only [Finset.mem_univ, not_true_eq_false, false_implies, implies_true, and_true, b]
  have hpair (u : Ambient n) :
      (∑ j, u j * (w j - v j)) = ∑ i, b.repr u i * height i := by
    let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) (w - v)
    have hf (i : Fin n) : f (b i) = height i := by
      change ((w - v) ⬝ᵥ (b i)) = _
      rw [dotProduct_comm]
      rw [show b i = embed n (d i) from integralBasisReal_apply d i]
      rfl
    have hs := congrArg f (b.sum_repr u)
    have hsum : f u = ∑ i, b.repr u i * f (b i) := by
      simpa only [map_sum, map_smul, smul_eq_mul] using hs.symm
    calc
      (∑ j, u j * (w j - v j)) = f u := dotProduct_comm u (w - v)
      _ = ∑ i, b.repr u i * height i := by simpa only [hf] using hsum
  ext u
  rw [P.mem_normalCone_inter_iff v w hv hw u, hmem u, hpair u]
  change ((∀ i, 0 ≤ b.repr u i) ∧ (∑ i, b.repr u i * height i) = 0) ↔
    u ∈ latticeRayCone ((Finset.univ.filter (fun i => height i = 0)).image d)
  rw [mem_latticeRayCone_basis_iff]
  change ((∀ i, 0 ≤ b.repr u i) ∧ (∑ i, b.repr u i * height i) = 0) ↔
    (∀ i, 0 ≤ b.repr u i) ∧
      ∀ i ∉ Finset.univ.filter (fun i => height i = 0), b.repr u i = 0
  constructor
  · rintro ⟨hu, hsum⟩
    refine ⟨hu, ?_⟩
    intro i hi
    have hne : height i ≠ 0 := by simpa only [Finset.mem_filter, Finset.mem_univ,
      true_and] using hi
    have hp : b.repr u i * height i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_nonneg (hu j) (hheight j))).mp hsum i (Finset.mem_univ i)
    exact (mul_eq_zero.mp hp).resolve_right hne
  · rintro ⟨hu, hz⟩
    refine ⟨hu, Finset.sum_eq_zero (fun i _ => ?_)⟩
    by_cases hi : height i = 0
    · rw [hi, mul_zero]
    · have hnot : i ∉ Finset.univ.filter (fun i => height i = 0) := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
      rw [hz i hnot, zero_mul]

/-- For a primitive edge basis, the vanishing test above is exactly the
corresponding primal coordinate of the displacement. -/
theorem normalCone_inter_eq_dual_coordinate_face
    (vZ : Lattice n) (w : Ambient n)
    (hv : embed n vZ ∈ P.carrier) (hw : w ∈ P.carrier)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (lengths : Fin n → ℕ)
    (hedges : ∀ i, 0 < lengths i ∧
      P.IsEdge (embed n vZ) (embed n (vZ + (lengths i : ℤ) • b i)))
    (hcone : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal b).repr (x - embed n vZ) i) :
    P.normalCone (embed n vZ) ∩ P.normalCone w =
      (latticeRayCone ((Finset.univ.filter (fun i =>
        (integralBasisReal b).repr (w - embed n vZ) i = 0)).image
          (integralDualBasis b)) : Set (Ambient n)) := by
  have h := P.normalCone_inter_eq_latticeRayCone (embed n vZ) w hv hw
    (integralDualBasis b)
    (P.normalCone_eq_latticeRayCone vZ b lengths hedges hcone)
  have he (i : Fin n) :
      (∑ j, embed n (integralDualBasis b i) j * (w j - embed n vZ j)) =
        (integralBasisReal b).repr (w - embed n vZ) i :=
    integralDualBasis_real_pairing b i (w - embed n vZ)
  simpa only [he] using h

end PaperVerification.ToricGeometry.LatticePolytope

