module

public import ToricPower.LinearRaySpanReduction
public import ToricPower.LatticeTraceSplitting
public import ToricPower.FanRayPrimitive
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Actual rays and primitive vectors of a restricted fan

The restricted fan in the saturated trace lattice has exactly the rays of
the original fan contained in the subspace. Its primitive lattice vectors
are the original primitive vectors, viewed in that trace. Consequently the
integer weight profiles on the retained rays are unchanged when a linear
test is reduced to the span of its rays.

These statements concern the actual cone and lattice constructions in
`SchemeCore`, rather than an independent finite combinatorial model. They
do not assert the still-required comparison with sheaf cohomology.

Development source awaiting compilation.
-/

@[expose] public noncomputable section

open TauCeti TauCeti.Toric CategoryTheory

namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

theorem restrictedFan_cone_map_mem (fan : Fan i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W)
    (τ : (restrictedFan fan W hW).cones) :
    τ.val.map W.subtype ∈ fan.cones := by
  obtain ⟨σ, hσ, hσW, hστ⟩ :=
    (mem_restrictedFan_cones fan W hW τ.val).mp τ.property
  rw [← hστ, cone_map_comap_subtype W σ hσW]
  exact hσ

/-- The literal ambient cone of an actual restricted cone. -/
def restrictedFanAmbientCone (fan : Fan i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W) (τ : (restrictedFan fan W hW).cones) : fan.cones :=
  ⟨τ.val.map W.subtype, restrictedFan_cone_map_mem fan W hW τ⟩

theorem restrictedFanInclusion_leastCone (fan : Fan i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W) (τ : (restrictedFan fan W hW).cones) :
    (restrictedFanInclusion fan W hW).leastCone τ.property = τ.val.map W.subtype := by
  apply le_antisymm
  · exact (restrictedFanInclusion fan W hW).leastCone_le τ.property
      (restrictedFan_cone_map_mem fan W hW τ) le_rfl
  · exact (restrictedFanInclusion fan W hW).map_le_leastCone τ.property

/-- The actual affine-chart formula for the restricted-fan scheme morphism. -/
theorem restrictedFanInclusion_affine_chart (fan : Fan i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W) (τ : (restrictedFan fan W hW).cones) :
    (restrictedFan fan W hW).affineToricChartι τ ≫
      (restrictedFanInclusion fan W hW).algebraicMap =
    affineToricSchemeMap (σ := τ.val) (τ := τ.val.map W.subtype)
      (restrictedFan fan W hW).lattice fan.lattice
      (latticeTrace i W).subtype.toAddMonoidHom W.subtype (fun _ => rfl)
      (fun x hx => ⟨x, hx, rfl⟩) ≫
        fan.affineToricChartι (restrictedFanAmbientCone fan W hW τ) :=
  FanHom.affineToricChartι_comp_algebraicMap_of_leastCone_eq
    (restrictedFanInclusion fan W hW) τ (restrictedFanAmbientCone fan W hW τ)
    (restrictedFanInclusion_leastCone fan W hW τ) (fun x hx => ⟨x, hx, rfl⟩)

theorem coneSpan_map_subtype (W : Submodule ℝ V) (τ : PointedCone ℝ W) :
    (Submodule.span ℝ (τ : Set W)).map W.subtype =
      Submodule.span ℝ (τ.map W.subtype : Set V) := by
  rw [Submodule.map_span, PointedCone.coe_map]

/-- An original fan ray contained in the subspace, with exactly the same
cone viewed in the subspace. -/
def fanRayRestrict (fan : Fan i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W) (ρ : fan.Ray)
    (hρW : ρ.toCone.val ≤ (W : PointedCone ℝ V)) :
    (restrictedFan fan W hW).Ray :=
  ⟨⟨ρ.toCone.val.comap W.subtype,
    (mem_restrictedFan_cones fan W hW _).mpr
      ⟨ρ.toCone.val, ρ.toCone.property, hρW, rfl⟩⟩, by
    have hspan := coneSpan_map_subtype W (ρ.toCone.val.comap W.subtype)
    rw [cone_map_comap_subtype W ρ.toCone.val hρW] at hspan
    have hdim := Submodule.finrank_map_subtype_eq W
      (Submodule.span ℝ (ρ.toCone.val.comap W.subtype : Set W))
    rw [hspan] at hdim
    exact hdim.symm.trans ρ.finrank_span⟩

@[simp]
theorem fanRayRestrict_toCone (fan : Fan i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W) (ρ : fan.Ray)
    (hρW : ρ.toCone.val ≤ (W : PointedCone ℝ V)) :
    (fanRayRestrict fan W hW ρ hρW).toCone.val =
      ρ.toCone.val.comap W.subtype := rfl

/-- The literal image of a restricted ray in the ambient space. -/
def restrictedFanRayMap (fan : Fan i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W)
    (ρ : (restrictedFan fan W hW).Ray) :
    {τ : fan.Ray // τ.toCone.val ≤ (W : PointedCone ℝ V)} := by
  refine ⟨⟨⟨ρ.toCone.val.map W.subtype,
    restrictedFan_cone_map_mem fan W hW ρ.toCone⟩, ?_⟩, ?_⟩
  · rw [← coneSpan_map_subtype W ρ.toCone.val,
      Submodule.finrank_map_subtype_eq]
    exact ρ.finrank_span
  · rintro x ⟨y, hy, rfl⟩
    exact y.property

@[simp]
theorem restrictedFanRayMap_toCone (fan : Fan i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W)
    (ρ : (restrictedFan fan W hW).Ray) :
    (restrictedFanRayMap fan W hW ρ).val.toCone.val =
      ρ.toCone.val.map W.subtype := rfl

/-- An equivalence of the complete actual ray types. No new or omitted
rays appear when the ambient lattice is replaced by its saturated trace. -/
def restrictedFanRayEquiv (fan : Fan i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W) :
    (restrictedFan fan W hW).Ray ≃
      {ρ : fan.Ray // ρ.toCone.val ≤ (W : PointedCone ℝ V)} where
  toFun := restrictedFanRayMap fan W hW
  invFun ρ := fanRayRestrict fan W hW ρ.val ρ.property
  left_inv ρ := by
    apply Subtype.ext
    apply Subtype.ext
    exact cone_comap_map_subtype W ρ.toCone.val
  right_inv ρ := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact cone_map_comap_subtype W ρ.val.toCone.val ρ.property

/-- The canonical primitive vector of an ambient fan ray belongs to
every real subspace containing that ray. -/
theorem fanRayPrimitiveGenerator_mem_subspace (fan : Fan i)
    (W : Submodule ℝ V) (ρ : fan.Ray)
    (hρW : ρ.toCone.val ≤ (W : PointedCone ℝ V)) :
    i (fanRayPrimitiveGenerator fan ρ) ∈ W := by
  apply hρW
  exact primitiveGenerator_mem fan.lattice (fan.isToricCone ρ.toCone.property)
    (ρ.toToricRay fan ρ.toCone le_rfl)

/-- Primitivity of a vector remains true in every integral submodule
containing it: restrict the actual integer-valued functional. -/
theorem primitive_in_submodule (S : Submodule ℤ N) (v : N)
    (hv : v ∈ S) (hp : TauCeti.IsPrimitive v) :
    TauCeti.IsPrimitive (⟨v, hv⟩ : S) := by
  obtain ⟨f, hf⟩ := (TauCeti.isPrimitive_def).mp hp
  apply (TauCeti.isPrimitive_def).mpr
  exact ⟨f.comp S.subtype, hf⟩

/-- The primitive vector of a restricted ray is literally the same
integer vector. Saturation prevents any hidden change of lattice index. -/
theorem fanRayPrimitiveGenerator_restrict (fan : Fan i)
    (W : Submodule ℝ V) (hW : IsRationalSubspace i W)
    (ρ : fan.Ray) (hρW : ρ.toCone.val ≤ (W : PointedCone ℝ V)) :
    (fanRayPrimitiveGenerator (restrictedFan fan W hW)
      (fanRayRestrict fan W hW ρ hρW)).val =
      fanRayPrimitiveGenerator fan ρ := by
  let v := fanRayPrimitiveGenerator fan ρ
  have hvW : v ∈ latticeTrace i W :=
    fanRayPrimitiveGenerator_mem_subspace fan W ρ hρW
  have hp : TauCeti.IsPrimitive (⟨v, hvW⟩ : latticeTrace i W) := by
    apply primitive_in_submodule
    exact primitiveGenerator_isPrimitive fan.lattice
      (fan.isToricCone ρ.toCone.property) (ρ.toToricRay fan ρ.toCone le_rfl)
  let τ := fanRayRestrict fan W hW ρ hρW
  have hgen : IsPrimitiveGenerator (latticeTraceMap i W)
      (τ.toToricRay (restrictedFan fan W hW) τ.toCone le_rfl)
      (⟨v, hvW⟩ : latticeTrace i W) := by
    apply (isPrimitiveGenerator_iff).mpr
    refine ⟨?_, hp⟩
    exact primitiveGenerator_mem fan.lattice
      (fan.isToricCone ρ.toCone.property) (ρ.toToricRay fan ρ.toCone le_rfl)
  have heq := hgen.eq_primitiveGenerator (restrictedFan fan W hW).lattice
    ((restrictedFan fan W hW).isToricCone τ.toCone.property)
  exact (congrArg Subtype.val heq).symm

/-- All rays retained by a linear test already lie in its finite ray span. -/
theorem fanRay_le_linearRayCore_iff (fan : Fan i) (W : Submodule ℝ V)
    (ρ : fan.Ray) :
    ρ.toCone.val ≤ (linearRayCore fan W : PointedCone ℝ V) ↔
      ρ.toCone.val ≤ (W : PointedCone ℝ V) :=
  cone_le_linearRayCore_iff fan W ρ.toCone.property

/-- Exact equality of all integer weight profiles on the retained original
rays, before any finite reduction of the cohomology calculation. -/
theorem linearRayCore_weightProfile_ranges (fan : Fan i)
    (W : Submodule ℝ V) :
    Set.range (fun m : latticeTrace i W →+ ℤ =>
      fun ρ : {ρ : fan.Ray // ρ.toCone.val ≤ (linearRayCore fan W : PointedCone ℝ V)} =>
        m ⟨fanRayPrimitiveGenerator fan ρ.val,
          (linearRayCore_le fan W)
            (fanRayPrimitiveGenerator_mem_subspace fan (linearRayCore fan W)
              ρ.val ρ.property)⟩) =
    Set.range (fun m : latticeTrace i (linearRayCore fan W) →+ ℤ =>
      fun ρ : {ρ : fan.Ray // ρ.toCone.val ≤ (linearRayCore fan W : PointedCone ℝ V)} =>
        m ⟨fanRayPrimitiveGenerator fan ρ.val,
          fanRayPrimitiveGenerator_mem_subspace fan (linearRayCore fan W)
            ρ.val ρ.property⟩) := by
  exact latticeTrace_characterProfile_ranges fan.lattice (linearRayCore_le fan W)
    (fun ρ : {ρ : fan.Ray // ρ.toCone.val ≤ (linearRayCore fan W : PointedCone ℝ V)} =>
      fanRayPrimitiveGenerator fan ρ.val)
    (fun ρ => fanRayPrimitiveGenerator_mem_subspace fan (linearRayCore fan W)
      ρ.val ρ.property)

end ToricPower
