module

public import ToricPower.RestrictedFanRays

/-! # Shared actual cones, rays and character profiles

The rational subspace and its ray span are indexed by the same ambient fan
cones and rays. The finite chart index is genuinely a small `Fin` type; no
universe restriction is imposed on the ambient real vector space.
-/

@[expose] public noncomputable section
open TauCeti.Toric
open scoped Classical

namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

abbrev rayCoreFan (fan : Fan i) (W : Submodule ℝ V) :=
  restrictedFan fan (linearRayCore fan W)
    (fanRaySpan_rational fan (fanRaysIn fan W))

abbrev retainedFanCones (fan : Fan i) (W : Submodule ℝ V) :=
  {σ : fan.cones // σ.val ≤ (W : PointedCone ℝ V)}

abbrev retainedFanRays (fan : Fan i) (W : Submodule ℝ V) :=
  {ρ : fan.Ray // ρ.toCone.val ≤ (W : PointedCone ℝ V)}

/-- The full cone type of the restricted fan, with the actual ambient cones. -/
def restrictedFanConeEquiv (fan : Fan i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W) :
    (restrictedFan fan W hW).cones ≃ retainedFanCones fan W where
  toFun τ := ⟨⟨τ.val.map W.subtype, restrictedFan_cone_map_mem fan W hW τ⟩, by
    rintro x ⟨y, hy, rfl⟩
    exact y.property⟩
  invFun σ := ⟨σ.val.val.comap W.subtype,
    (mem_restrictedFan_cones fan W hW _).mpr
      ⟨σ.val.val, σ.val.property, σ.property, rfl⟩⟩
  left_inv τ := Subtype.ext (cone_comap_map_subtype W τ.val)
  right_inv σ := by
    apply Subtype.ext
    exact Subtype.ext (cone_map_comap_subtype W σ.val.val σ.property)

/-- Replacing the subspace by its ray span retains every cone and only those cones. -/
def rayCoreRetainedConeEquiv (fan : Fan i) (W : Submodule ℝ V) :
    retainedFanCones fan (linearRayCore fan W) ≃ retainedFanCones fan W where
  toFun σ := ⟨σ.val, σ.property.trans (linearRayCore_le fan W)⟩
  invFun σ := ⟨σ.val, cone_le_linearRayCore fan W σ.val.property σ.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A common finite enumeration of all cones retained by the two tests. -/
def linearRayCoreFiniteCharts (fan : Fan i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W) :
    Fin (Nat.card (retainedFanCones fan W)) → (restrictedFan fan W hW).cones :=
  (restrictedFanConeEquiv fan W hW).symm ∘
    (Finite.equivFin (retainedFanCones fan W)).symm

theorem linearRayCoreFiniteCharts_surjective (fan : Fan i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W) :
    Function.Surjective (linearRayCoreFiniteCharts fan W hW) :=
  (restrictedFanConeEquiv fan W hW).symm.surjective.comp
    (Finite.equivFin (retainedFanCones fan W)).symm.surjective

def rayCoreFanFiniteCharts (fan : Fan i) (W : Submodule ℝ V)
    (_hW : IsRationalSubspace i W) :
    Fin (Nat.card (retainedFanCones fan W)) → (rayCoreFan fan W).cones :=
  (restrictedFanConeEquiv fan (linearRayCore fan W)
    (fanRaySpan_rational fan (fanRaysIn fan W))).symm ∘
      (rayCoreRetainedConeEquiv fan W).symm ∘
        (Finite.equivFin (retainedFanCones fan W)).symm

theorem rayCoreFanFiniteCharts_surjective (fan : Fan i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W) :
    Function.Surjective (rayCoreFanFiniteCharts fan W hW) :=
  (restrictedFanConeEquiv fan (linearRayCore fan W)
    (fanRaySpan_rational fan (fanRaysIn fan W))).symm.surjective.comp
      ((rayCoreRetainedConeEquiv fan W).symm.surjective.comp
        (Finite.equivFin (retainedFanCones fan W)).symm.surjective)

def rayCoreRetainedRayEquiv (fan : Fan i) (W : Submodule ℝ V) :
    retainedFanRays fan (linearRayCore fan W) ≃ retainedFanRays fan W where
  toFun ρ := ⟨ρ.val, ρ.property.trans (linearRayCore_le fan W)⟩
  invFun ρ := ⟨ρ.val, cone_le_linearRayCore fan W ρ.val.toCone.property ρ.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def rayCoreFanRayEquiv (fan : Fan i) (W : Submodule ℝ V) :
    (rayCoreFan fan W).Ray ≃ retainedFanRays fan W :=
  (restrictedFanRayEquiv fan (linearRayCore fan W)
    (fanRaySpan_rational fan (fanRaysIn fan W))).trans (rayCoreRetainedRayEquiv fan W)

/-- Restrict divisor coefficients along the actual ray correspondence. -/
def restrictedFanRayCoefficients (fan : Fan i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W) (b : fan.Ray → ℤ) :
    (restrictedFan fan W hW).Ray → ℤ :=
  fun ρ => b ((restrictedFanRayEquiv fan W hW ρ).val)

theorem restrictedFanRayEquiv_incidence (fan : Fan i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W) (ρ : (restrictedFan fan W hW).Ray)
    (σ : retainedFanCones fan W) :
    ρ.toCone ≤ (restrictedFanConeEquiv fan W hW).symm σ ↔
      (restrictedFanRayEquiv fan W hW ρ).val.toCone ≤ σ.val := by
  change ρ.toCone.val ≤ σ.val.val.comap W.subtype ↔
    ρ.toCone.val.map W.subtype ≤ σ.val.val
  constructor
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact h hy
  · intro h y hy
    exact h ⟨y, hy, rfl⟩

theorem restrictedFan_primitive_value (fan : Fan i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W) (ρ : (restrictedFan fan W hW).Ray) :
    (fanRayPrimitiveGenerator (restrictedFan fan W hW) ρ).val =
      fanRayPrimitiveGenerator fan (restrictedFanRayEquiv fan W hW ρ).val := by
  have h := fanRayPrimitiveGenerator_restrict fan W hW
    (restrictedFanRayEquiv fan W hW ρ).val
    (restrictedFanRayEquiv fan W hW ρ).property
  have he : fanRayRestrict fan W hW
      (restrictedFanRayEquiv fan W hW ρ).val
      (restrictedFanRayEquiv fan W hW ρ).property = ρ :=
    (restrictedFanRayEquiv fan W hW).left_inv ρ
  simpa only [he] using h

def retainedRayPrimitiveInCore (fan : Fan i) (W : Submodule ℝ V)
    (ρ : retainedFanRays fan W) : latticeTrace i (linearRayCore fan W) :=
  ⟨fanRayPrimitiveGenerator fan ρ.val,
    fanRayPrimitiveGenerator_mem_subspace fan (linearRayCore fan W) ρ.val
      (cone_le_linearRayCore fan W ρ.val.toCone.property ρ.property)⟩

def retainedRayPrimitiveInSubspace (fan : Fan i) (W : Submodule ℝ V)
    (ρ : retainedFanRays fan W) : latticeTrace i W :=
  ⟨fanRayPrimitiveGenerator fan ρ.val,
    (linearRayCore_le fan W) (retainedRayPrimitiveInCore fan W ρ).property⟩

/-- Equality of the full character-profile ranges; all integral characters occur. -/
theorem retainedRayProfile_ranges (fan : Fan i) (W : Submodule ℝ V) :
    Set.range (fun m : latticeTrace i W →+ ℤ =>
      fun ρ => m (retainedRayPrimitiveInSubspace fan W ρ)) =
    Set.range (fun m : latticeTrace i (linearRayCore fan W) →+ ℤ =>
      fun ρ => m (retainedRayPrimitiveInCore fan W ρ)) :=
  latticeTrace_characterProfile_ranges fan.lattice (linearRayCore_le fan W)
    (fun ρ : retainedFanRays fan W => fanRayPrimitiveGenerator fan ρ.val)
    (fun ρ => (retainedRayPrimitiveInCore fan W ρ).property)

/-- Incidence expressed only in the common ambient fan cones. -/
def retainedRayIncidence (fan : Fan i) (W : Submodule ℝ V)
    (ρ : retainedFanRays fan W) (j : Fin (Nat.card (retainedFanCones fan W))) : Prop :=
  ρ.val.toCone ≤ ((Finite.equivFin (retainedFanCones fan W)).symm j).val

theorem restricted_ray_incidence (fan : Fan i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W) (ρ : (restrictedFan fan W hW).Ray)
    (j : Fin (Nat.card (retainedFanCones fan W))) :
    ρ.toCone ≤ linearRayCoreFiniteCharts fan W hW j ↔
      retainedRayIncidence fan W (restrictedFanRayEquiv fan W hW ρ) j :=
  restrictedFanRayEquiv_incidence fan W hW ρ _

theorem rayCore_ray_incidence (fan : Fan i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W) (ρ : (rayCoreFan fan W).Ray)
    (j : Fin (Nat.card (retainedFanCones fan W))) :
    ρ.toCone ≤ rayCoreFanFiniteCharts fan W hW j ↔
      retainedRayIncidence fan W (rayCoreFanRayEquiv fan W ρ) j :=
  restrictedFanRayEquiv_incidence fan (linearRayCore fan W)
    (fanRaySpan_rational fan (fanRaysIn fan W)) ρ _

theorem restricted_ray_value (fan : Fan i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W) (m : latticeTrace i W →+ ℤ)
    (ρ : (restrictedFan fan W hW).Ray) :
    m (fanRayPrimitiveGenerator (restrictedFan fan W hW) ρ) =
      m (retainedRayPrimitiveInSubspace fan W (restrictedFanRayEquiv fan W hW ρ)) := by
  congr 1
  exact Subtype.ext (restrictedFan_primitive_value fan W hW ρ)

theorem rayCore_ray_value (fan : Fan i) (W : Submodule ℝ V)
    (m : latticeTrace i (linearRayCore fan W) →+ ℤ) (ρ : (rayCoreFan fan W).Ray) :
    m (fanRayPrimitiveGenerator (rayCoreFan fan W) ρ) =
      m (retainedRayPrimitiveInCore fan W (rayCoreFanRayEquiv fan W ρ)) := by
  congr 1
  exact Subtype.ext (restrictedFan_primitive_value fan (linearRayCore fan W)
    (fanRaySpan_rational fan (fanRaysIn fan W)) ρ)

end ToricPower
