module

public import Recovery.Unimodular.GraphicSectionRing.CoordinateSemigroup

/-!
# Original real polytope dilations and the actual Ehrhart semigroup

Every positive degree is identified with the lattice points in the literal
real dilation. Degree zero is the actual zero exponent. This justifies the
Ehrhart algebra's carrier independently of normal generation or Koszulness.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Pointwise BigOperators

namespace Unimodular.GraphicSectionRing

variable {n d : ℕ}

/-- The reverse implication uses actual division in the real vector space. -/
theorem mem_dilate_iff_scaled_inequalities {k : ℕ} (hk : 0 < k)
    (C : Set (Constraint d)) (m : Lattice d) :
    latticeCast m ∈ (k : ℝ) • body C ↔
      ∀ c ∈ C, difference m c.left c.right ≤ (k : ℤ) * c.bound := by
  constructor
  · exact scaled_inequalities_of_mem_dilate
  · intro hm
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
    apply Set.mem_smul_set.mpr
    refine ⟨(k : ℝ)⁻¹ • latticeCast m, ?_, ?_⟩
    · intro c hc
      rw [realDifference_smul, realDifference_cast]
      have hi : (difference m c.left c.right : ℝ) ≤ (k : ℝ) * (c.bound : ℝ) := by
        exact_mod_cast hm c hc
      calc
        (k : ℝ)⁻¹ * (difference m c.left c.right : ℝ) ≤
            (k : ℝ)⁻¹ * ((k : ℝ) * (c.bound : ℝ)) :=
          mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hkpos.le)
        _ = (c.bound : ℝ) := by rw [← mul_assoc, inv_mul_cancel₀ hkne, one_mul]
    · rw [smul_smul, mul_inv_cancel₀ hkne, one_smul]

/-- Full integer decomposition in the original integral coordinates. -/
theorem coordinate_integer_decomposition (e : Lattice n ≃ₗ[ℤ] Lattice d)
    (C : Set (Constraint d)) {k : ℕ} (hk : 0 < k) (x : Lattice n)
    (hx : latticeCast x ∈ (k : ℝ) • RealCoordinates.coordinateBody e C) :
    ∃ v : Fin k → Lattice n,
      (∀ i, latticeCast (v i) ∈ RealCoordinates.coordinateBody e C) ∧ ∑ i, v i = x := by
  obtain ⟨v, hv, hsum⟩ := integer_decomposition hk (e x)
    ((RealCoordinates.cast_mem_coordinate_dilate e C k x).mp hx)
  refine ⟨fun i => e.symm (v i), ?_, ?_⟩
  · intro i
    apply (RealCoordinates.cast_mem_coordinateBody e C _).mpr
    rw [e.apply_symm_apply]
    exact latticeCast_mem_body.mp (hv i)
  · rw [← map_sum, hsum, e.symm_apply_apply]

/-- Boundedness of the original real polytope proves finiteness in the chosen
coordinates, with no full-dimensionality or interior-point premise. -/
theorem coordinate_points_finite (e : Lattice n ≃ₗ[ℤ] Lattice d)
    (C : Set (Constraint d))
    (hP : Bornology.IsBounded (RealCoordinates.coordinateBody e C)) : Finite (Point C) := by
  letI : Fintype (LatticePoint (RealCoordinates.coordinateBody e C)) :=
    (finite_lattice_points_of_bounded (RealCoordinates.coordinateBody e C) hP).fintype
  exact Finite.of_surjective (coordinatePointEquiv e C) (coordinatePointEquiv e C).surjective

/-- Membership in the ordinary Ehrhart exponent monoid, stated solely using
an actual real set and its actual positive dilations. -/
def EhrhartPoint (P : Set (RealLattice n)) (z : ℕ × Lattice n) : Prop :=
  z = 0 ∨ (0 < z.1 ∧ latticeCast z.2 ∈ (z.1 : ℝ) • P)

theorem coordinateSemigroup_iff_ehrhart (e : Lattice n ≃ₗ[ℤ] Lattice d)
    (C : Set (Constraint d)) (z : ℕ × Lattice n) :
    z ∈ coordinateSemigroup e C ↔ EhrhartPoint (RealCoordinates.coordinateBody e C) z := by
  constructor
  · intro hz
    have h := (mem_coordinateSemigroup e C z).mp hz
    by_cases hk : z.1 = 0
    · exact Or.inl (Prod.ext hk (h.1 hk))
    · refine Or.inr ⟨Nat.pos_of_ne_zero hk, ?_⟩
      apply (RealCoordinates.cast_mem_coordinate_dilate e C z.1 z.2).mpr
      exact (mem_dilate_iff_scaled_inequalities (Nat.pos_of_ne_zero hk) C (e z.2)).mpr h.2
  · rintro (rfl | ⟨hk, hz⟩)
    · exact (coordinateSemigroup e C).zero_mem
    · apply (mem_coordinateSemigroup e C z).mpr
      refine ⟨fun hzero => False.elim ((ne_of_gt hk) hzero), ?_⟩
      exact (mem_dilate_iff_scaled_inequalities hk C (e z.2)).mp
        ((RealCoordinates.cast_mem_coordinate_dilate e C z.1 z.2).mp hz)

/-- The carrier is the literal Ehrhart exponent set of P. The graphic
presentation is used only to prove closure under addition. -/
def ehrhartSemigroup (P : Set (RealLattice n)) (e : Lattice n ≃ₗ[ℤ] Lattice d)
    (C : Set (Constraint d)) (hP : P = RealCoordinates.coordinateBody e C) :
    AddSubmonoid (ℕ × Lattice n) where
  carrier := {z | EhrhartPoint P z}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro x y hx hy
    subst P
    exact (coordinateSemigroup_iff_ehrhart e C (x + y)).mp
      ((coordinateSemigroup e C).add_mem
        ((coordinateSemigroup_iff_ehrhart e C x).mpr hx)
        ((coordinateSemigroup_iff_ehrhart e C y).mpr hy))

def ehrhartSemigroupEquiv (P : Set (RealLattice n)) (e : Lattice n ≃ₗ[ℤ] Lattice d)
    (C : Set (Constraint d)) (hP : P = RealCoordinates.coordinateBody e C) :
    ehrhartSemigroup P e C hP ≃+ coordinateSemigroup e C where
  toFun z := ⟨z.val, (coordinateSemigroup_iff_ehrhart e C z.val).mpr (by
    have hz : EhrhartPoint P z.val := z.property
    simpa only [hP] using hz)⟩
  invFun z := ⟨z.val, by
    change EhrhartPoint P z.val
    rw [hP]
    exact (coordinateSemigroup_iff_ehrhart e C z.val).mp z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

abbrev EhrhartAlgebra (P : Set (RealLattice n)) (e : Lattice n ≃ₗ[ℤ] Lattice d)
    (C : Set (Constraint d)) (hP : P = RealCoordinates.coordinateBody e C)
    (K : Type*) [CommSemiring K] := AddMonoidAlgebra K (ehrhartSemigroup P e C hP)

/-- The exponent correspondence is (degree, inverse integral coordinate map). -/
def sectionEhrhartIndex (P : Set (RealLattice n)) (e : Lattice n ≃ₗ[ℤ] Lattice d)
    (C : Set (Constraint d)) (hP : P = RealCoordinates.coordinateBody e C) :
    sectionSemigroup C ≃+ ehrhartSemigroup P e C hP :=
  (coordinateSemigroupEquiv e C).symm.trans (ehrhartSemigroupEquiv P e C hP).symm

@[simp] theorem sectionEhrhartIndex_val (P : Set (RealLattice n))
    (e : Lattice n ≃ₗ[ℤ] Lattice d) (C : Set (Constraint d))
    (hP : P = RealCoordinates.coordinateBody e C) (z : sectionSemigroup C) :
    (sectionEhrhartIndex P e C hP z).val = (z.val.1, e.symm z.val.2) := rfl

@[simp] theorem sectionEhrhartIndex_degree (P : Set (RealLattice n))
    (e : Lattice n ≃ₗ[ℤ] Lattice d) (C : Set (Constraint d))
    (hP : P = RealCoordinates.coordinateBody e C) (z : sectionSemigroup C) :
    (sectionEhrhartIndex P e C hP z).val.1 = z.val.1 := rfl

/-- An actual equivalence to the Ehrhart algebra of the original real P. -/
def sectionEhrhartEquiv (P : Set (RealLattice n)) (e : Lattice n ≃ₗ[ℤ] Lattice d)
    (C : Set (Constraint d)) (hP : P = RealCoordinates.coordinateBody e C)
    (K : Type*) [CommSemiring K] : SectionAlgebra C K ≃ₐ[K] EhrhartAlgebra P e C hP K :=
  AddMonoidAlgebra.domCongr K K (sectionEhrhartIndex P e C hP)

@[simp] theorem sectionEhrhartEquiv_single (P : Set (RealLattice n))
    (e : Lattice n ≃ₗ[ℤ] Lattice d) (C : Set (Constraint d))
    (hP : P = RealCoordinates.coordinateBody e C) (K : Type*) [CommSemiring K]
    (z : sectionSemigroup C) (a : K) :
    sectionEhrhartEquiv P e C hP K (AddMonoidAlgebra.single z a) =
      AddMonoidAlgebra.single (sectionEhrhartIndex P e C hP z) a :=
  AddMonoidAlgebra.domCongr_single _ _ _

#print axioms mem_dilate_iff_scaled_inequalities
#print axioms coordinate_integer_decomposition
#print axioms coordinate_points_finite
#print axioms coordinateSemigroup_iff_ehrhart
#print axioms sectionEhrhartEquiv

end Unimodular.GraphicSectionRing

#check Unimodular.GraphicSectionRing.coordinateSemigroup_iff_ehrhart
