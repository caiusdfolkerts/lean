module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Equiv
import all TauCeti.Geometry.Toric.Algebraic.Fan.Equiv

public import Recovery.Unimodular.PriorExtensions.NormalFanCoordinateTransport
public import Recovery.Unimodular.NativePort.A3IntegralProjectivity

@[expose] public section

/-!
Actual projective and smooth fan counts in the literal A3 root lattice.
The finite normal-polytope witnesses are explicitly integral on every
lattice vector, and the entire cone family is transported.
UNVERIFIED until the exact native compiler and transitive axiom audit pass.
-/

set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TauCeti.Toric

namespace Unimodular.LiteralA3Projectivity
open NormalFanSupport NormalFanCoordinateTransport LiteralRootCoordinates

section IntegralTransport
variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedAddCommGroup V']
  [NormedSpace ℝ V] [NormedSpace ℝ V']
  [FiniteDimensional ℝ V] [FiniteDimensional ℝ V']
  {ι : N →+ V} {ι' : N' →+ V'} {Φ : Fan ι} {Ψ : Fan ι'}

/-- The actual dual-lattice condition for an arbitrary lattice embedding.
Its normal cones are ordinary maximization cones of a finite convex hull. -/
def HasIntegralNormalFan (Φ : Fan ι) : Prop :=
  ∃ s : Finset (Module.Dual ℝ V),
    (∀ p ∈ s, ∀ x : N, ∃ z : ℤ, p (ι x) = (z : ℝ)) ∧
    ∀ D : PointedCone ℝ V, D ∈ Φ.cones ↔
      ∃ q ∈ convexHull ℝ (s : Set (Module.Dual ℝ V)),
        D = normalCone (convexHull ℝ (s : Set (Module.Dual ℝ V))) q

theorem integral_normalFan_of_equiv (e : FanEquiv Φ Ψ)
    (hΦ : HasIntegralNormalFan Φ) : HasIntegralNormalFan Ψ := by
  classical
  obtain ⟨s,hint,hs⟩ := hΦ
  let t : Finset (Module.Dual ℝ V') := s.image (dualTransport e.realEquiv)
  let Q := convexHull ℝ (s : Set (Module.Dual ℝ V))
  have hQ : convexHull ℝ (t : Set (Module.Dual ℝ V')) =
      dualTransport e.realEquiv '' Q := by
    rw [show (t : Set (Module.Dual ℝ V')) =
      dualTransport e.realEquiv '' (s : Set (Module.Dual ℝ V)) by
        exact Finset.coe_image]
    exact ((dualTransport e.realEquiv).toLinearMap.image_convexHull _).symm
  refine ⟨t,?_,?_⟩
  · intro q hq y
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    rw [dualTransport_apply,
      FanTransport.compatible_inverse e.latticeEquiv e.realEquiv e.map_lattice y]
    exact hint p hp (e.latticeEquiv.symm y)
  · intro D
    rw [hQ]
    constructor
    · intro hD
      have hback : D.map e.realEquiv.symm.toLinearMap ∈ Φ.cones :=
        (e.symm.map_mem D).mpr hD
      obtain ⟨p,hp,he⟩ := (hs _).mp hback
      refine ⟨dualTransport e.realEquiv p,⟨p,hp,rfl⟩,?_⟩
      calc
        D = (D.map e.realEquiv.symm.toLinearMap).map e.realEquiv.toLinearMap :=
          (FanTransport.map_inverse_rev e.realEquiv D).symm
        _ = (normalCone Q p).map e.realEquiv.toLinearMap := by rw [he]
        _ = _ := map_normalCone e.realEquiv Q p
    · rintro ⟨q,⟨p,hp,rfl⟩,he⟩
      have hC : normalCone Q p ∈ Φ.cones := (hs _).mpr ⟨p,hp,rfl⟩
      rw [he,← map_normalCone]
      exact (e.map_mem _).mpr hC

theorem integral_normalFan_equiv_iff (e : FanEquiv Φ Ψ) :
    HasIntegralNormalFan Ψ ↔ HasIntegralNormalFan Φ :=
  ⟨integral_normalFan_of_equiv e.symm,integral_normalFan_of_equiv e⟩

end IntegralTransport

/-- Actual complete fans on the literal twelve roots e_i-e_j in the real
zero-sum hyperplane, with the integral zero-sum lattice. -/
abbrev LiteralCompleteRootFan :=
  {Φ : Fan (rootEmbedding 3) // Φ.IsComplete ∧ HasLiteralRays Φ}

abbrev CoordinateCompleteRootFan := A3RegularFanCount.CompleteRootFan

/-- Restriction of the proved all-fan bijection to the full prescribed ray set. -/
def coordinateEquiv : CoordinateCompleteRootFan ≃ LiteralCompleteRootFan :=
  completeRootFansEquiv 3

def projectiveFansEquiv :
    {Φ : CoordinateCompleteRootFan // HasPolytopeNormalFan Φ.val} ≃
      {Φ : LiteralCompleteRootFan // HasPolytopeNormalFan Φ.val} :=
  Equiv.subtypeEquiv coordinateEquiv (fun Φ => (literalRootFans_normalFan_iff Φ.val).symm)

def projectiveRegularFansEquiv :
    {Φ : CoordinateCompleteRootFan // HasPolytopeNormalFan Φ.val ∧ Φ.val.IsRegular} ≃
      {Φ : LiteralCompleteRootFan // HasPolytopeNormalFan Φ.val ∧ Φ.val.IsRegular} :=
  Equiv.subtypeEquiv coordinateEquiv (fun Φ =>
    ((literalRootFans_normalFan_iff Φ.val).and (allFansEquiv_regular_iff Φ.val)).symm)

def nonprojectiveRegularFansEquiv :
    {Φ : CoordinateCompleteRootFan // Φ.val.IsRegular ∧ ¬HasPolytopeNormalFan Φ.val} ≃
      {Φ : LiteralCompleteRootFan // Φ.val.IsRegular ∧ ¬HasPolytopeNormalFan Φ.val} :=
  Equiv.subtypeEquiv coordinateEquiv (fun Φ =>
    ((allFansEquiv_regular_iff Φ.val).and
      (not_congr (literalRootFans_normalFan_iff Φ.val))).symm)

theorem integral_root_transport_iff (Φ : CoordinateCompleteRootFan) :
    HasIntegralNormalFan (coordinateEquiv Φ).val ↔
      IntegralNormalPolytopes.HasLatticePolytopeNormalFan Φ.val := by
  change HasIntegralNormalFan (allFansEquiv 3 Φ.val) ↔ HasIntegralNormalFan Φ.val
  exact integral_normalFan_equiv_iff
    (FanTransport.equivalence (Heller.TypeA.coordinateEquiv 3).toAddEquiv
      (realCoordinateEquiv 3) (coordinateCompatibility 3) Φ.val)

def latticeProjectiveFansEquiv :
    {Φ : CoordinateCompleteRootFan // IntegralNormalPolytopes.HasLatticePolytopeNormalFan Φ.val} ≃
      {Φ : LiteralCompleteRootFan // HasIntegralNormalFan Φ.val} :=
  Equiv.subtypeEquiv coordinateEquiv (fun Φ => (integral_root_transport_iff Φ).symm)

/-- The real normal-polytope and literal lattice-normal-polytope conditions
are equivalent for every actual complete fan on the literal A3 roots. -/
theorem literal_normalFan_iff_integral (Φ : LiteralCompleteRootFan) :
    HasPolytopeNormalFan Φ.val ↔ HasIntegralNormalFan Φ.val := by
  obtain ⟨Ψ,rfl⟩ := coordinateEquiv.surjective Φ
  rw [integral_root_transport_iff]
  change HasPolytopeNormalFan (allFansEquiv 3 Ψ.val) ↔
    IntegralNormalPolytopes.HasLatticePolytopeNormalFan Ψ.val
  rw [literalRootFans_normalFan_iff]
  exact A3IntegralProjectivity.normalFan_iff_lattice_normalFan Ψ

/-- Exactly 603 actual labelled fans in the literal paper lattice are
normal fans of finite polytopes. -/
theorem literal_projective_fan_count :
    Nat.card {Φ : LiteralCompleteRootFan // HasPolytopeNormalFan Φ.val} = 603 := by
  rw [← Nat.card_congr projectiveFansEquiv]
  exact A3ProjectiveCounts.a3_projective_fan_count

/-- The same count requires actual integral dual vertices. -/
theorem literal_lattice_projective_fan_count :
    Nat.card {Φ : LiteralCompleteRootFan // HasIntegralNormalFan Φ.val} = 603 := by
  rw [← Nat.card_congr latticeProjectiveFansEquiv]
  exact A3IntegralProjectivity.a3_lattice_projective_fan_count

/-- Exactly 62 of the literal complete fans are regular and projective. -/
theorem literal_projective_regular_fan_count :
    Nat.card {Φ : LiteralCompleteRootFan // HasPolytopeNormalFan Φ.val ∧ Φ.val.IsRegular} = 62 := by
  rw [← Nat.card_congr projectiveRegularFansEquiv]
  exact A3ProjectiveCounts.a3_projective_regular_fan_count

/-- Exactly two literal complete regular fans are nonprojective. -/
theorem literal_nonprojective_regular_fan_count :
    Nat.card {Φ : LiteralCompleteRootFan // Φ.val.IsRegular ∧ ¬HasPolytopeNormalFan Φ.val} = 2 := by
  rw [← Nat.card_congr nonprojectiveRegularFansEquiv]
  exact A3ProjectiveCounts.a3_nonprojective_regular_fan_count

#print axioms integral_normalFan_of_equiv
#print axioms integral_normalFan_equiv_iff
#print axioms integral_root_transport_iff
#print axioms literal_normalFan_iff_integral
#print axioms literal_projective_fan_count
#print axioms literal_lattice_projective_fan_count
#print axioms literal_projective_regular_fan_count
#print axioms literal_nonprojective_regular_fan_count

end Unimodular.LiteralA3Projectivity
end

#check "UNIMODULAR_LITERAL_A3_PROJECTIVITY_EOF_V1"
