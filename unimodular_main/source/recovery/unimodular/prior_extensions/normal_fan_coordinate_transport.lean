module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Equiv
import all TauCeti.Geometry.Toric.Algebraic.Fan.Equiv

public import Recovery.Unimodular.NativePort.NormalFanGeometry
public import Recovery.Unimodular.NativePort.LiteralRootTransport

@[expose] public section

/-!
Coordinate invariance of the genuine finite-polytope normal-fan condition.
The finite dual point set, its actual convex hull, and every normal cone are
transported explicitly. No support-function definition is substituted for
normal-fan projectivity.

UNVERIFIED until its own native compiler receipt and axiom audit succeed.
-/

set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TauCeti.Toric

namespace Unimodular.NormalFanCoordinateTransport

section Linear
variable {V V' : Type*} [AddCommGroup V] [AddCommGroup V']
  [Module ℝ V] [Module ℝ V']

/-- The contragredient coordinate map on actual linear functionals. -/
def dualTransport (e : V ≃ₗ[ℝ] V') :
    Module.Dual ℝ V ≃ₗ[ℝ] Module.Dual ℝ V' where
  toFun p := p.comp e.symm.toLinearMap
  invFun q := q.comp e.toLinearMap
  left_inv p := by ext x; simp
  right_inv q := by ext y; simp
  map_add' p q := by ext y; rfl
  map_smul' a p := by ext y; rfl

@[simp] theorem dualTransport_apply (e : V ≃ₗ[ℝ] V')
    (p : Module.Dual ℝ V) (y : V') :
    dualTransport e p y = p (e.symm y) := rfl

/-- Normal cones transform by the primal map when the polytope transforms
by its actual contragredient map. This holds for arbitrary point sets. -/
theorem map_normalCone (e : V ≃ₗ[ℝ] V')
    (Q : Set (Module.Dual ℝ V)) (p : Module.Dual ℝ V) :
    (NormalFanSupport.normalCone Q p).map e.toLinearMap =
      NormalFanSupport.normalCone (dualTransport e '' Q) (dualTransport e p) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩ z ⟨q,hq,rfl⟩
    change q (e.symm (e x)) ≤ p (e.symm (e x))
    simpa only [LinearEquiv.symm_apply_apply] using hx q hq
  · intro hy
    refine ⟨e.symm y,?_,e.apply_symm_apply y⟩
    intro q hq
    exact hy (dualTransport e q) ⟨q,hq,rfl⟩

end Linear

section Fans
variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedAddCommGroup V']
  [NormedSpace ℝ V] [NormedSpace ℝ V']
  [FiniteDimensional ℝ V] [FiniteDimensional ℝ V']
  {ι : N →+ V} {ι' : N' →+ V'} {Φ : Fan ι} {Ψ : Fan ι'}

/-- The whole normal fan of a finite polytope remains the whole normal fan
of the explicitly transported finite polytope. -/
theorem hasPolytopeNormalFan_of_equiv (e : FanEquiv Φ Ψ)
    (hΦ : NormalFanSupport.HasPolytopeNormalFan Φ) :
    NormalFanSupport.HasPolytopeNormalFan Ψ := by
  classical
  obtain ⟨s,hs⟩ := hΦ
  let t : Finset (Module.Dual ℝ V') := s.image (dualTransport e.realEquiv)
  let Q := convexHull ℝ (s : Set (Module.Dual ℝ V))
  have hQ : convexHull ℝ (t : Set (Module.Dual ℝ V')) =
      dualTransport e.realEquiv '' Q := by
    rw [show (t : Set (Module.Dual ℝ V')) =
      dualTransport e.realEquiv '' (s : Set (Module.Dual ℝ V)) by
        exact Finset.coe_image]
    exact ((dualTransport e.realEquiv).toLinearMap.image_convexHull _).symm
  refine ⟨t,?_⟩
  intro D
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
      _ = (NormalFanSupport.normalCone Q p).map e.realEquiv.toLinearMap := by
        rw [he]
      _ = _ := map_normalCone e.realEquiv Q p
  · rintro ⟨q,⟨p,hp,rfl⟩,he⟩
    have hC : NormalFanSupport.normalCone Q p ∈ Φ.cones :=
      (hs _).mpr ⟨p,hp,rfl⟩
    rw [he,← map_normalCone]
    exact (e.map_mem _).mpr hC

/-- Normal-polytope existence is invariant under the proved integral and
real equivalence of actual fans, in both directions. -/
theorem hasPolytopeNormalFan_equiv_iff (e : FanEquiv Φ Ψ) :
    NormalFanSupport.HasPolytopeNormalFan Ψ ↔
      NormalFanSupport.HasPolytopeNormalFan Φ :=
  ⟨hasPolytopeNormalFan_of_equiv e.symm,hasPolytopeNormalFan_of_equiv e⟩

end Fans

/-- The actual normal-polytope condition agrees in the paper's literal
zero-sum lattice and in the rooted incidence coordinate model. -/
theorem literalRootFans_normalFan_iff {n : ℕ}
    (Φ : Fan (FanBridge.standardEmbedding n)) :
    NormalFanSupport.HasPolytopeNormalFan (LiteralRootCoordinates.allFansEquiv n Φ) ↔
      NormalFanSupport.HasPolytopeNormalFan Φ :=
  hasPolytopeNormalFan_equiv_iff
    (FanTransport.equivalence (Heller.TypeA.coordinateEquiv n).toAddEquiv
      (LiteralRootCoordinates.realCoordinateEquiv n)
      (LiteralRootCoordinates.coordinateCompatibility n) Φ)

#print axioms map_normalCone
#print axioms hasPolytopeNormalFan_of_equiv
#print axioms hasPolytopeNormalFan_equiv_iff
#print axioms literalRootFans_normalFan_iff

end Unimodular.NormalFanCoordinateTransport
end

#check "UNIMODULAR_NORMAL_FAN_COORDINATE_TRANSPORT_EOF_V2"
