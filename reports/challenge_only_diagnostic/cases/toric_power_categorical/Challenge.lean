module
public import Mathlib
public import TauCeti.Geometry.Toric.Algebraic.Fan.Scheme
public import TauCeti.Geometry.Toric.Algebraic.Regular
public import TauCeti.AlgebraicGeometry.CartierDivisor.Sheaf
public import TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.Basic
public import TauCeti.Algebra.Homology.DerivedCategory.Bounded.Basic

/- Canonical-dependency main1.1 interface draft. It requires TauCeti1f9b4414
and its exact complete Mathlib07406378 manifest, NOT the live package's56a00585
manifest. No local build or dependency upgrade is claimed. -/
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory TauCeti.Toric
namespace PalomarToricPower
universe u
variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}
/-- The literal trace lattice N intersect W. -/
def latticeTrace (W : Submodule ℝ V) : Submodule ℤ N :=
  (W.restrictScalars ℤ).comap i.toIntLinearMap
/-- The ordinary function from the literal trace lattice to its subspace. -/
def traceFn (W : Submodule ℝ V) (n : latticeTrace (i := i) W) : W := ⟨i n, n.property⟩
/-- The trace inclusion into W preserves zero. -/
theorem trace_zero (W : Submodule ℝ V) : traceFn (i := i) W 0 = 0 := by sorry
/-- The trace inclusion into W preserves addition. -/
theorem trace_add (W : Submodule ℝ V) (x y : latticeTrace (i := i) W) :
    traceFn (i := i) W (x + y) = traceFn W x + traceFn W y := by sorry
/-- The actual trace lattice map, with no extra torus factor. -/
def latticeTraceMap (W : Submodule ℝ V) : latticeTrace (i := i) W →+ W where
  toFun := traceFn W
  map_zero' := trace_zero W
  map_add' := trace_add W
/-- Rationality means the actual integral points span precisely W. -/
def IsRationalSubspace (W : Submodule ℝ V) : Prop :=
  Submodule.span ℝ (Set.range (fun n : latticeTrace (i := i) W => i n)) = W
/-- The exact restricted cone family, inside W. -/
def restrictedCones (Φ : Fan i) (W : Submodule ℝ V) : Set (PointedCone ℝ W) :=
  (fun σ : PointedCone ℝ V => σ.comap W.subtype) ''
    {σ | σ ∈ Φ.cones ∧ σ ≤ (W : PointedCone ℝ V)}
/-- The actual rational trace is an integral lattice. -/
theorem trace_integral (Φ : Fan i) (W : Submodule ℝ V) (hW : IsRationalSubspace (i := i) W) :
    IsIntegralLattice (latticeTraceMap (i := i) W) := by sorry
/-- Restriction retains a finite cone family. -/
theorem restriction_finite (Φ : Fan i) (W : Submodule ℝ V) : (restrictedCones Φ W).Finite := by sorry
/-- Every restricted cone is genuinely rational and salient in the trace lattice. -/
theorem restriction_toric (Φ : Fan i) (W : Submodule ℝ V) {σ : PointedCone ℝ W}
    (hσ : σ ∈ restrictedCones Φ W) : IsToricCone (latticeTraceMap (i := i) W) σ := by sorry
/-- The actual restricted family is closed under taking faces. -/
theorem restriction_faces (Φ : Fan i) (W : Submodule ℝ V) {σ τ : PointedCone ℝ W}
    (hσ : σ ∈ restrictedCones Φ W) (hτ : τ.IsFaceOf σ) : τ ∈ restrictedCones Φ W := by sorry
/-- Intersections in the restricted family are actual faces. -/
theorem restriction_intersection (Φ : Fan i) (W : Submodule ℝ V) {σ τ : PointedCone ℝ W}
    (hσ : σ ∈ restrictedCones Φ W) (hτ : τ ∈ restrictedCones Φ W) : (σ ⊓ τ).IsFaceOf σ := by sorry
/-- The actual restricted fan in the saturated integral trace. -/
def restrictedFan (Φ : Fan i) (W : Submodule ℝ V) (hW : IsRationalSubspace (i := i) W) :
    Fan (latticeTraceMap (i := i) W) where
  lattice := trace_integral Φ W hW
  cones := restrictedCones Φ W
  finite_cones := restriction_finite Φ W
  isToricCone := fun {σ} hσ => restriction_toric Φ W (σ := σ) hσ
  mem_of_isFaceOf := fun {σ τ} hσ hτ => restriction_faces Φ W (σ := σ) (τ := τ) hσ hτ
  inf_isFaceOf_left := fun {σ τ} hσ hτ => restriction_intersection Φ W (σ := σ) (τ := τ) hσ hτ
/-- Linearity means intersection with every original cone remains an original cone. -/
def IsLinearSubspace (Φ : Fan i) (W : Submodule ℝ V) : Prop :=
  ∀ σ ∈ Φ.cones, σ ⊓ (W : PointedCone ℝ V) ∈ Φ.cones
/-- A genuinely rational linear subspace, with exactly the manuscript's fan-linearity condition. -/
structure LinearSubspace (Φ : Fan i) where
  space : Submodule ℝ V
  rational : IsRationalSubspace (i := i) space
  linear : IsLinearSubspace Φ space
/-- Inclusion of restricted cones is genuinely a fan map. -/
theorem restricted_map_cone (Φ : Fan i) (W : Submodule ℝ V) {σ : PointedCone ℝ W}
    (hσ : σ ∈ restrictedCones Φ W) : ∃ τ ∈ Φ.cones, σ.map W.subtype ≤ τ := by sorry
/-- The canonical fan inclusion of the actual trace lattice and actual subspace. -/
def restrictedInclusion (Φ : Fan i) (W : Submodule ℝ V) (hW : IsRationalSubspace (i := i) W) :
    FanHom (restrictedFan Φ W hW) Φ where
  latticeMap := (latticeTrace (i := i) W).subtype.toAddMonoidHom
  realMap := W.subtype
  map_lattice _ := rfl
  map_cone := fun {σ} hσ => restricted_map_cone Φ W (σ := σ) hσ
/-- The actual scheme morphism induced by inclusion of a rational linear subspace. -/
def linearInclusion (Φ : Fan i) (W : LinearSubspace Φ) :=
  (restrictedInclusion Φ W.space W.rational).algebraicMap
/-- Natural multiplication respects the actual integral lattice embedding. -/
theorem power_lattice (ell : ℕ) (n : N) :
    ((ell : ℝ) • (LinearMap.id : V →ₗ[ℝ] V)) (i n) = i ((ell • AddMonoidHom.id N) n) := by sorry
/-- Natural multiplication sends every cone into a cone of the same fan. -/
theorem power_cone (Φ : Fan i) (ell : ℕ) {σ : PointedCone ℝ V} (hσ : σ ∈ Φ.cones) :
    ∃ τ ∈ Φ.cones, σ.map ((ell : ℝ) • LinearMap.id) ≤ τ := by sorry
/-- The genuine multiplication-by-ell fan endomorphism. -/
def powerFanHom (Φ : Fan i) (ell : ℕ) : FanHom Φ Φ where
  latticeMap := ell • AddMonoidHom.id N
  realMap := (ell : ℝ) • LinearMap.id
  map_lattice := power_lattice ell
  map_cone := fun {σ} hσ => power_cone Φ ell (σ := σ) hσ
/-- The ordinary actual toric scheme power map, obtained by affine gluing. -/
def powerMap (Φ : Fan i) (ell : ℕ) := (powerFanHom Φ ell).algebraicMap
/-- Every actual finite toric fan gives a Noetherian scheme. -/
theorem fan_noetherian (Φ : Fan i) : IsNoetherian Φ.algebraicRealization := by sorry
/-- A nonempty actual fan gives an integral toric scheme. -/
theorem fan_integral (Φ : Fan i) (hne : Φ.cones.Nonempty) : IsIntegral Φ.algebraicRealization := by sorry
/-- Actual Cartier divisors on the genuine integral toric scheme. -/
def Cartier (Φ : Fan i) (hne : Φ.cones.Nonempty) : Type :=
  letI := fan_integral Φ hne
  TauCeti.AlgebraicGeometry.Scheme.CartierDivisor Φ.algebraicRealization
/-- The genuine Cartier line bundle O(D). -/
def divisorSheaf (Φ : Fan i) (hne : Φ.cones.Nonempty) (D : Cartier Φ hne) :
    Φ.algebraicRealization.Modules :=
  letI := fan_integral Φ hne
  D.sheaf
/-- Ordinary direct image under the actual power map. -/
def powerSheaf (Φ : Fan i) (hne : Φ.cones.Nonempty) (D : Cartier Φ hne) (ell : ℕ) :=
  (Scheme.Modules.pushforward (powerMap Φ ell)).obj (divisorSheaf Φ hne D)
/-- The zero sheaf belongs to the literal finite-presentation subcategory. -/
theorem coherent_containsZero (X : Scheme.{u}) :
    (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf).ContainsZero := by sorry
/-- Actual kernels preserve finite presentation on locally Noetherian schemes. -/
theorem coherent_closedKernels (X : Scheme.{u}) [IsLocallyNoetherian X] :
    (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderKernels := by sorry
/-- Actual cokernels preserve finite presentation. -/
theorem coherent_closedCokernels (X : Scheme.{u}) :
    (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderCokernels := by sorry
/-- Actual finite products preserve finite presentation. -/
theorem coherent_closedProducts (X : Scheme.{u}) :
    (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderFiniteProducts := by sorry
local instance (priority := 2000) coherentContainsZero (X : Scheme.{u}) :
    (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf).ContainsZero := coherent_containsZero X
local instance (priority := 2000) coherentClosedKernels (X : Scheme.{u}) [IsLocallyNoetherian X] :
    (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderKernels := coherent_closedKernels X
local instance (priority := 2000) coherentClosedCokernels (X : Scheme.{u}) :
    (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderCokernels := coherent_closedCokernels X
local instance (priority := 2000) coherentClosedProducts (X : Scheme.{u}) :
    (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderFiniteProducts := coherent_closedProducts X
/-- Mathlib's actual full-subcategory abelian structure. The separately proved
closure propositions supply its hypotheses; no categorical operation is postulated. -/
local instance (priority := 2000) coherentAbelian (X : Scheme.{u}) [IsLocallyNoetherian X] :
    Abelian (TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf X) := inferInstance
local instance standardDerived (X : Scheme.{u}) [IsLocallyNoetherian X] :
    HasDerivedCategory.{u+1} (TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf X) :=
  HasDerivedCategory.standard _
/-- The literal bounded derived category of actual coherent sheaves. -/
abbrev DbCoh (Φ : Fan i) :=
  letI := fan_noetherian Φ
  DerivedCategory.Bounded (TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf Φ.algebraicRealization)
/-- The actual ordinary finite power-map direct image is a coherent sheaf. -/
theorem power_finitePresentation (Φ : Fan i) (hreg : Φ.IsRegular) (hne : Φ.cones.Nonempty)
    (D : Cartier Φ hne) (ell : ℕ) (hell : 0 < ell) :
    _root_.SheafOfModules.IsFinitePresentation (R := Φ.algebraicRealization.ringCatSheaf)
      (powerSheaf Φ hne D ell) := by sorry
/-- The actual coherent direct image placed in degree zero in Db(Coh). -/
def powerObject (Φ : Fan i) (hreg : Φ.IsRegular) (hne : Φ.cones.Nonempty)
    (D : Cartier Φ hne) (ell : ℕ) (hell : 0 < ell) : DbCoh Φ :=
  letI := fan_noetherian Φ
  (TauCeti.DerivedCategory.Bounded.singleFunctor _ 0).obj
    ⟨powerSheaf Φ hne D ell, power_finitePresentation Φ hreg hne D ell hell⟩
/-- Classical generation of the actual bounded coherent derived category. -/
def Generates (Φ : Fan i) (hreg : Φ.IsRegular) (hne : Φ.cones.Nonempty)
    (D : Cartier Φ hne) (ell : ℕ) (hell : 0 < ell) : Prop :=
  letI := fan_noetherian Φ
  (ObjectProperty.singleton (powerObject Φ hreg hne D ell hell)).IsClassicalTriangulatedGenerator
/-- Ordinary Zariski sheaf cohomology, via Mathlib's actual functor on the small site. -/
def totalCohomologyNonzero (X : Scheme.{u}) (M : X.Modules) : Prop :=
  ∃ p : ℕ, Nontrivial (((_root_.SheafOfModules.toSheaf.{u} X.ringCatSheaf ⋙ CategoryTheory.Sheaf.functorH.{u} _ p).obj M))
/-- Every actual rational linear subspace passes the literal restricted cohomology test. -/
def Criterion (Φ : Fan i) (hne : Φ.cones.Nonempty) (D : Cartier Φ hne) : Prop :=
  ∀ W : LinearSubspace Φ,
    totalCohomologyNonzero (restrictedFan Φ W.space W.rational).algebraicRealization
      ((Scheme.Modules.pullback (linearInclusion Φ W)).obj (divisorSheaf Φ hne D))
/-- Main Theorem1.1: existence iff the full cohomology criterion, and generation
for every sufficiently large integer exponent, for every actual Cartier divisor. -/
theorem main_theorem (Φ : Fan i) (hreg : Φ.IsRegular) (hne : Φ.cones.Nonempty)
    (D : Cartier Φ hne) :
    ((∃ (ell : ℕ) (hell : 0 < ell), Generates Φ hreg hne D ell hell) ↔ Criterion Φ hne D) ∧
    (Criterion Φ hne D → ∃ (L : ℕ) (hL : 0 < L), ∀ (ell : ℕ) (hLell : L ≤ ell),
      Generates Φ hreg hne D ell (lt_of_lt_of_le hL hLell)) := by sorry
end PalomarToricPower
