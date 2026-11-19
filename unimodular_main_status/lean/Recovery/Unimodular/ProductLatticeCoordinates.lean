module
public import Recovery.Unimodular.NativePort.LiteralRootTransport
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.Logic.Equiv.Set
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open TauCeti.Toric
open scoped NNReal

namespace Unimodular.LatticeCoordinates

section Linear
variable {n : ℕ} {N V E : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {ι : N →+ V}

abbrev coordinateEmbedding (n : ℕ) : Lattice n →+ Ambient n :=
  (Int.castAddHom ℝ).compLeft (Fin n)

def latticeEquiv (b : Module.Basis (Fin n) ℤ N) : N ≃ₗ[ℤ] Lattice n := b.equivFun

def realEquiv (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N) :
    V ≃ₗ[ℝ] Ambient n := (hι.isBaseChange.basis b).equivFun

/-- Integral and real coordinates commute with the given actual lattice
embedding. The real coordinates come from scalar extension of the integral
basis; they are not chosen independently. -/
theorem coordinates_commute (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
    (x : N) : realEquiv hι b (ι x) = coordinateEmbedding n (latticeEquiv b x) := by
  ext i
  simpa [realEquiv, latticeEquiv, coordinateEmbedding] using
    hι.isBaseChange.basis_repr_comp_apply b x i

/-- The coordinate basis is exactly the standard integral basis. -/
theorem basis_map_coordinates (b : Module.Basis (Fin n) ℤ N) :
    b.map (latticeEquiv b) = Pi.basisFun ℤ (Fin n) := by
  ext i j
  simp [latticeEquiv, Module.Basis.map_apply, Module.Basis.equivFun_self,
    Pi.basisFun_apply, Pi.single_apply, eq_comm]

theorem determinant_coordinates (b : Module.Basis (Fin n) ℤ N) (u : Fin n → N) :
    (Pi.basisFun ℤ (Fin n)).det (latticeEquiv b ∘ u) = b.det u := by
  rw [← basis_map_coordinates b, Module.Basis.det_map]
  congr 1
  funext i
  exact (latticeEquiv b).symm_apply_apply (u i)

/-- The full maximal-minor definition of uniform unimodularity is exactly
preserved under coordinates, in both directions and for every labelled family. -/
theorem uniform_coordinates_iff (b : Module.Basis (Fin n) ℤ N) (u : E → N) :
    IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (latticeEquiv b ∘ u) ↔
      IntegralRigidity.Uniform b u := by
  constructor
  · intro h a
    have ha := h a
    change |(Pi.basisFun ℤ (Fin n)).det (latticeEquiv b ∘ (u ∘ a))| ≤ 1 at ha
    rw [determinant_coordinates] at ha
    exact ha
  · intro h a
    change |(Pi.basisFun ℤ (Fin n)).det (latticeEquiv b ∘ (u ∘ a))| ≤ 1
    rw [determinant_coordinates]
    exact h a

/-- Original set labels and coordinate-image labels are genuinely equivalent. -/
def imageLabelEquiv (b : Module.Basis (Fin n) ℤ N) (U : Set N) :
    U ≃ (latticeEquiv b '' U) :=
  Equiv.Set.image (latticeEquiv b) U (latticeEquiv b).injective

@[simp] theorem imageLabelEquiv_val (b : Module.Basis (Fin n) ℤ N)
    (U : Set N) (u : U) : (imageLabelEquiv b U u).val = latticeEquiv b u.val := rfl

/-- Set-indexed coordinate configurations satisfy exactly the original
unimodularity condition; passing to image labels loses no selection of columns. -/
theorem uniform_image_iff (b : Module.Basis (Fin n) ℤ N) (U : Set N) :
    IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun u : latticeEquiv b '' U => u.val) ↔
    IntegralRigidity.Uniform b (fun u : U => u.val) := by
  let e := imageLabelEquiv b U
  rw [← uniform_coordinates_iff b (fun u : U => u.val)]
  constructor
  · intro h a
    exact h (fun i => e (a i))
  · intro h a
    have ha := h (fun i => e.symm (a i))
    have he : (latticeEquiv b ∘ (fun u : U => u.val)) ∘ (fun i => e.symm (a i)) =
        (fun u : latticeEquiv b '' U => u.val) ∘ a := by
      funext i
      exact congrArg Subtype.val (e.apply_symm_apply (a i))
    rwa [he] at ha

/-- Actual positive hulls, not only linear spans, are transported exactly. -/
theorem hull_coordinates (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
    (U : Set N) :
    (PointedCone.hull ℝ (ι '' U)).map (realEquiv hι b : V →ₗ[ℝ] Ambient n) =
      PointedCone.hull ℝ (coordinateEmbedding n '' (latticeEquiv b '' U)) := by
  change Submodule.map ((realEquiv hι b : V →ₗ[ℝ] Ambient n).restrictScalars ℝ≥0)
    (Submodule.span ℝ≥0 (ι '' U)) = _
  rw [Submodule.map_span]
  change PointedCone.hull ℝ (realEquiv hι b '' (ι '' U)) = _
  simp only [Set.image_image]
  congr 1
  apply congrArg (fun f : N → Ambient n => f '' U)
  funext x
  exact coordinates_commute hι b x

/-- Positive spanning of the whole real space is invariant, in both directions. -/
theorem hull_top_coordinates_iff (hι : IsIntegralLattice ι)
    (b : Module.Basis (Fin n) ℤ N) (U : Set N) :
    PointedCone.hull ℝ (coordinateEmbedding n '' (latticeEquiv b '' U)) = ⊤ ↔
      PointedCone.hull ℝ (ι '' U) = ⊤ := by
  have htop : (⊤ : PointedCone ℝ V).map (realEquiv hι b : V →ₗ[ℝ] Ambient n) = ⊤ := by
    change Submodule.map ((realEquiv hι b : V →ₗ[ℝ] Ambient n).restrictScalars ℝ≥0) ⊤ = ⊤
    rw [Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (realEquiv hι b).surjective
  constructor
  · intro h
    apply FanTransport.map_injective (realEquiv hι b)
    change (PointedCone.hull ℝ (ι '' U)).map (realEquiv hι b : V →ₗ[ℝ] Ambient n) =
      (⊤ : PointedCone ℝ V).map (realEquiv hι b : V →ₗ[ℝ] Ambient n)
    rw [hull_coordinates hι b U, h, htop]
  · intro h
    rw [← hull_coordinates hι b U, h, htop]

def coordinateFan (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
    (Φ : Fan ι) : Fan (coordinateEmbedding n) :=
  FanTransport.transport (latticeEquiv b).toAddEquiv (realEquiv hι b)
    (coordinates_commute hι b) Φ

/-- This is an equivalence of actual fans, carrying every cone and the full
integral lattice. It is not a correspondence of selected maximal cones. -/
def coordinateFanEquiv (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
    (Φ : Fan ι) : FanEquiv Φ (coordinateFan hι b Φ) :=
  FanTransport.equivalence (latticeEquiv b).toAddEquiv (realEquiv hι b)
    (coordinates_commute hι b) Φ

theorem coordinateFan_complete_iff (hι : IsIntegralLattice ι)
    (b : Module.Basis (Fin n) ℤ N) (Φ : Fan ι) :
    (coordinateFan hι b Φ).IsComplete ↔ Φ.IsComplete :=
  (coordinateFanEquiv hι b Φ).isComplete_iff

theorem coordinateFan_regular_iff (hι : IsIntegralLattice ι)
    (b : Module.Basis (Fin n) ℤ N) (Φ : Fan ι) :
    (coordinateFan hι b Φ).IsRegular ↔ Φ.IsRegular :=
  (coordinateFanEquiv hι b Φ).isRegular_iff

end Linear

section Rays
variable {n : ℕ} {N V E : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype E]
  {ι : N →+ V}

/-- Exact prescribed rays are preserved with all original labels retained. -/
theorem hasRays_coordinateFan_iff (hι : IsIntegralLattice ι)
    (b : Module.Basis (Fin n) ℤ N) (u : E → N) (Φ : Fan ι) :
    AllowedBlocks.HasRays (coordinateEmbedding n) (latticeEquiv b ∘ u)
        (coordinateFan hι b Φ) ↔ AllowedBlocks.HasRays ι u Φ := by
  letI : FiniteDimensional ℝ V := hι.finiteDimensional
  exact FanTransport.hasRays_equiv_iff (coordinateFanEquiv hι b Φ)
    (fun a => coordinates_commute hι b (u a))

end Rays
end Unimodular.LatticeCoordinates
#print axioms Unimodular.LatticeCoordinates.coordinates_commute
#print axioms Unimodular.LatticeCoordinates.uniform_image_iff
#print axioms Unimodular.LatticeCoordinates.hull_top_coordinates_iff
#print axioms Unimodular.LatticeCoordinates.coordinateFanEquiv
#print axioms Unimodular.LatticeCoordinates.hasRays_coordinateFan_iff
#check Unimodular.LatticeCoordinates.hasRays_coordinateFan_iff
