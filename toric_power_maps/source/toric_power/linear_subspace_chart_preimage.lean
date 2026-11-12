module

public import ToricPower.LinearSubspaceAffineClosed
public import ToricPower.RestrictedFanRays

/-!
# The literal linear toric inclusion is a closed immersion

The inverse image of an ambient cone chart is the chart of its actual
intersection with the linear subspace in the saturated trace lattice.
This is proved by the basic-open description of face charts and actual
restriction of monomials. The previously verified surjective chart-ring
maps then prove global closedness by Zariski locality on the target.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower
universe u

section GeneralChart
variable {N N' : Type u} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {fan : Fan i} {target : Fan i'}

/-- The chart formula holds for every containing target cone, not only
the least target cone selected in the gluing construction. -/
theorem fanHom_chart_formula_of_mapsTo (f : FanHom fan target)
    (σ : fan.cones) (τ : target.cones)
    (maps : Set.MapsTo f.realMap σ.val τ.val) :
    fan.affineToricChartι σ ≫ f.algebraicMap =
      affineToricSchemeMap fan.lattice target.lattice f.latticeMap f.realMap
        f.map_lattice maps ≫ target.affineToricChartι τ := by
  let least : target.cones := ⟨f.leastCone σ.property,f.leastCone_mem σ.property⟩
  have below : least.val ≤ τ.val := f.leastCone_le σ.property τ.property (by
    rintro _ ⟨x,hx,rfl⟩
    exact maps hx)
  have face : least.val.IsFaceOf τ.val :=
    target.isFaceOf_of_le τ.property least.property below
  rw [FanHom.affineToricChartι_comp_algebraicMap]
  change f.affineToricChartMap σ ≫ target.affineToricChartι least = _
  rw [← Fan.faceAffineToricSchemeMap_comp_affineToricChartι
    (Φ := target) (τ := least) (σ := τ) face]
  rw [← Category.assoc,FanHom.affineToricChartMap_def,
    faceAffineToricSchemeMap_eq_affineToricSchemeMap,affineToricSchemeMap_comp]
  simp only [AddMonoidHom.id_comp,LinearMap.id_comp]

end GeneralChart

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) (W : LinearSubspace fan)

/-- The chart of the actual cone intersection, in the actual trace lattice. -/
def linearSubspaceChart (σ : fan.cones) : (restrictedFan fan W.space W.rational).cones :=
  ⟨σ.val.comap W.space.subtype,W.comap_mem fan σ.property⟩

def linearSubspaceAffineMap (σ : fan.cones) :
    (restrictedFan fan W.space W.rational).affineToricChart (linearSubspaceChart fan W σ) ⟶
      fan.affineToricChart σ :=
  affineToricSchemeMap (restrictedFan fan W.space W.rational).lattice fan.lattice
    (latticeTrace i W.space).subtype.toAddMonoidHom W.space.subtype (fun _ => rfl)
    (fun _ hx => hx)

theorem linearSubspace_chart_formula (σ : fan.cones) :
    (restrictedFan fan W.space W.rational).affineToricChartι (linearSubspaceChart fan W σ) ≫
      linearToricInclusion fan W =
      linearSubspaceAffineMap fan W σ ≫ fan.affineToricChartι σ :=
  fanHom_chart_formula_of_mapsTo (restrictedFanInclusion fan W.space W.rational)
    (linearSubspaceChart fan W σ) σ (fun _ hx => hx)

theorem linearSubspace_chart_apply (σ : fan.cones)
    (x : (restrictedFan fan W.space W.rational).affineToricChart
      (linearSubspaceChart fan W σ)) :
    linearToricInclusion fan W
      ((restrictedFan fan W.space W.rational).affineToricChartι
        (linearSubspaceChart fan W σ) x) =
      fan.affineToricChartι σ (linearSubspaceAffineMap fan W σ x) :=
  congrArg (fun f => f x) (linearSubspace_chart_formula fan W σ)

private theorem face_range_eq_basicOpen {P E : Type*} [AddCommGroup P]
    [AddCommGroup E] [Module ℝ E] {j : P →+ E} (lattice : IsIntegralLattice j)
    {σ τ : PointedCone ℝ E} (finite : σ.FG) (face : τ.IsFaceOf σ)
    (m : dualSemigroup lattice σ)
    (equation : σ ⊓ PointedCone.ofSubmodule (lattice.realCharacter m).ker = τ) :
    Set.range (faceAffineToricSchemeMap lattice face) =
      (PrimeSpectrum.basicOpen (MonoidAlgebra.single (Multiplicative.ofAdd m) (1 : ℂ)) :
        Set (PrimeSpectrum (affineCoordinateRing lattice σ))) := by
  subst τ
  exact range_faceAffineToricSchemeMap lattice finite m

/-- Monomial restriction computes the preimage of every face chart. -/
theorem linearSubspaceAffineMap_mem_face_range (σ : fan.cones)
    {τ : PointedCone ℝ V} (face : τ.IsFaceOf σ.val)
    (x : (restrictedFan fan W.space W.rational).affineToricChart
      (linearSubspaceChart fan W σ)) :
    linearSubspaceAffineMap fan W σ x ∈
        Set.range (faceAffineToricSchemeMap fan.lattice face) ↔
      x ∈ Set.range (faceAffineToricSchemeMap
        (restrictedFan fan W.space W.rational).lattice (face.comap W.space.subtype)) := by
  obtain ⟨m,nonnegative,equation⟩ :=
    (fan.isToricCone σ.property).rational.exists_mem_dualSemigroup_inf_ker_eq fan.lattice face
  let source := restrictedFan fan W.space W.rational
  let restricted : dualSemigroup source.lattice (σ.val.comap W.space.subtype) :=
    dualSemigroupMap source.lattice fan.lattice
      (latticeTrace i W.space).subtype.toAddMonoidHom W.space.subtype (fun _ => rfl)
      (fun _ hx => hx) ⟨m,nonnegative⟩
  have character : (restricted : latticeTrace i W.space →+ ℤ) =
      m.comp (latticeTrace i W.space).subtype.toAddMonoidHom := by
    ext n
    exact dualSemigroupMap_apply ..
  have restrictedEquation : σ.val.comap W.space.subtype ⊓
      PointedCone.ofSubmodule (source.lattice.realCharacter restricted).ker =
        τ.comap W.space.subtype := by
    rw [← equation]
    ext y
    change (y.val ∈ σ.val ∧ source.lattice.realCharacter restricted y = 0) ↔
      (y.val ∈ σ.val ∧ fan.lattice.realCharacter m y.val = 0)
    rw [character,source.lattice.realCharacter_comp fan.lattice
      (latticeTrace i W.space).subtype.toAddMonoidHom W.space.subtype (fun _ => rfl)]
    rfl
  rw [face_range_eq_basicOpen fan.lattice (fan.isToricCone σ.property).fg face
    ⟨m,nonnegative⟩ equation,
    face_range_eq_basicOpen source.lattice
      (source.isToricCone (W.comap_mem fan σ.property)).fg (face.comap W.space.subtype)
      restricted restrictedEquation]
  unfold linearSubspaceAffineMap
  erw [affineToricSchemeMap_def,Spec.map_apply]
  change ¬ MonoidAlgebra.single (Multiplicative.ofAdd (⟨m,nonnegative⟩ :
      dualSemigroup fan.lattice σ.val)) (1 : ℂ) ∈ Ideal.comap _ x.asIdeal ↔ _
  rw [Ideal.mem_comap]
  change ¬ affineCoordinateRingMap _ _ _ _ _ _
      (MonoidAlgebra.single (Multiplicative.ofAdd (⟨m,nonnegative⟩ :
        dualSemigroup fan.lattice σ.val)) (1 : ℂ)) ∈ x.asIdeal ↔ _
  erw [affineCoordinateRingMap_single]
  rfl

theorem exists_linearSubspaceChart_point
    (x : (restrictedFan fan W.space W.rational).algebraicRealization) :
    ∃ (σ : fan.cones) (z : (restrictedFan fan W.space W.rational).affineToricChart
        (linearSubspaceChart fan W σ)),
      (restrictedFan fan W.space W.rational).affineToricChartι
        (linearSubspaceChart fan W σ) z = x := by
  obtain ⟨γ,z,rfl⟩ := (restrictedFan fan W.space W.rational).exists_affineToricChartι_apply_eq x
  obtain ⟨σ,member,_,equation⟩ :=
    (mem_restrictedFan_cones fan W.space W.rational γ.val).mp γ.property
  have same : linearSubspaceChart fan W ⟨σ,member⟩ = γ := Subtype.ext equation
  subst γ
  exact ⟨⟨σ,member⟩,z,rfl⟩

/-- The actual inverse image of an ambient chart is its restricted cone chart. -/
theorem linearToricInclusion_preimage_chart (τ : fan.cones) :
    linearToricInclusion fan W ⁻¹' Set.range (fan.affineToricChartι τ) =
      Set.range ((restrictedFan fan W.space W.rational).affineToricChartι
        (linearSubspaceChart fan W τ)) := by
  ext x
  constructor
  · intro inside
    obtain ⟨σ,z,rfl⟩ := exists_linearSubspaceChart_point fan W x
    obtain ⟨w,equality⟩ := inside
    have samePoint : fan.affineToricChartι σ (linearSubspaceAffineMap fan W σ z) =
        fan.affineToricChartι τ w :=
      (linearSubspace_chart_apply fan W σ z).symm.trans equality.symm
    obtain ⟨common,toLeft,_⟩ :=
      (fan.affineToricChartι_eq_affineToricChartι_iff _ _).mp samePoint
    have inFace : linearSubspaceAffineMap fan W σ z ∈ Set.range
        (faceAffineToricSchemeMap fan.lattice (fan.inf_isFaceOf_left σ.property τ.property)) :=
      ⟨common,by simpa only [Fan.affineToricOverlapLeft_def] using toLeft⟩
    obtain ⟨preimage,evaluates⟩ :=
      (linearSubspaceAffineMap_mem_face_range fan W σ
        (fan.inf_isFaceOf_left σ.property τ.property) z).mp inFace
    let source := restrictedFan fan W.space W.rational
    let meet := linearSubspaceChart fan W (σ ⊓ τ)
    have leftFace : meet.val.IsFaceOf (linearSubspaceChart fan W σ).val :=
      (fan.inf_isFaceOf_left σ.property τ.property).comap W.space.subtype
    have rightFace : meet.val.IsFaceOf (linearSubspaceChart fan W τ).val :=
      (fan.inf_isFaceOf_right σ.property τ.property).comap W.space.subtype
    refine ⟨faceAffineToricSchemeMap source.lattice rightFace preimage,?_⟩
    rw [← evaluates]
    exact congrArg (fun f => f preimage)
      ((Fan.faceAffineToricSchemeMap_comp_affineToricChartι
        (Φ := source) (τ := meet) (σ := linearSubspaceChart fan W τ) rightFace).trans
        (Fan.faceAffineToricSchemeMap_comp_affineToricChartι
          (Φ := source) (τ := meet) (σ := linearSubspaceChart fan W σ) leftFace).symm)
  · rintro ⟨z,rfl⟩
    exact ⟨linearSubspaceAffineMap fan W τ z,(linearSubspace_chart_apply fan W τ z).symm⟩

theorem linearToricInclusion_chart_isPullback (σ : fan.cones) :
    IsPullback (linearSubspaceAffineMap fan W σ)
      ((restrictedFan fan W.space W.rational).affineToricChartι (linearSubspaceChart fan W σ))
      (fan.affineToricChartι σ) (linearToricInclusion fan W) := by
  apply IsOpenImmersion.isPullback
  · exact linearSubspace_chart_formula fan W σ
  · apply TopologicalSpace.Opens.ext
    exact linearToricInclusion_preimage_chart fan W σ

/-- The paper's actual linearity condition suffices for the literal
scheme inclusion to be closed; smoothness or completeness is not added. -/
theorem linearToricInclusion_isClosedImmersion : IsClosedImmersion (linearToricInclusion fan W) := by
  apply (IsZariskiLocalAtTarget.iff_of_openCover
    (P := @IsClosedImmersion.{u}) fan.affineToricOpenCover).mpr
  intro σ
  change IsClosedImmersion (Limits.pullback.snd (linearToricInclusion fan W) (fan.affineToricChartι σ))
  have square := (linearToricInclusion_chart_isPullback fan W σ).flip
  rw [← square.isoPullback_inv_snd]
  letI : IsClosedImmersion (linearSubspaceAffineMap fan W σ) :=
    linearSubspace_affineChart_isClosedImmersion fan W σ
  infer_instance

end ToricPower
end
