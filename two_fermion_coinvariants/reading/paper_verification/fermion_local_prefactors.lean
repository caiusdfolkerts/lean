module

public import PaperVerification.FermionLocalCoordinates
public import PaperVerification.FermionOddNormalizationEquiv

/-!
# Residual paired units in the actual local coefficient algebra

The paired product identity is proved first in F[X]. Its cofactor identity is
then evaluated, so the proof never cancels a nilpotent local coordinate.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open Polynomial
open scoped Classical BigOperators

structure SeparatedPairedData (F : Type*) [Field F] (n : ℕ)
    extends SeparatedOrdinaryData F n where
  a : Fin n → Polynomial F
  b : Fin n → Polynomial F
  a_monic : ∀ i,(a i).Monic
  b_monic : ∀ i,(b i).Monic
  paired_product : ∀ i,a i*b i=G.comp (phi i)

theorem unit_coordinate_factorization {A : Type*} [CommRing A]
    (t : A) (w q : Aˣ) (m : ℕ) :
    (t*(w:A))^m*(↑(q*(w⁻¹)^m):A)=t^m*(q:A) := by
  have hw : (w:A)^m*(↑(w⁻¹):A)^m=1 := by
    rw [←mul_pow,Units.mul_inv,one_pow]
  simp only [mul_pow,Units.val_mul,Units.val_pow_eq_pow_val]
  calc
    t^m*(w:A)^m*((q:A)*(↑(w⁻¹):A)^m)=
        t^m*(q:A)*((w:A)^m*(↑(w⁻¹):A)^m) := by ring
    _=t^m*(q:A) := by rw [hw,mul_one]

namespace SeparatedPairedData

variable {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
variable (d : SeparatedPairedData F n)
variable (rho : d.toSeparatedOrdinaryData.SupportPoint)

abbrev O := d.toSeparatedOrdinaryData

def localA (i : Fin n) : d.O.LocalOrdinary rho :=
  Polynomial.aeval (d.O.localX rho i) (d.a i)

def localB (i : Fin n) : d.O.LocalOrdinary rho :=
  Polynomial.aeval (d.O.localX rho i) (d.b i)

def thetaOrder (i : Fin n) : ℕ := (d.a i).rootMultiplicity (rho.1 i)
def xiOrder (i : Fin n) : ℕ := (d.b i).rootMultiplicity (rho.1 i)

theorem local_exponent_balance (i : Fin n) :
    d.thetaOrder rho i+d.xiOrder rho i=
      d.O.ramificationOrder rho i*
        d.O.clusterMultiplicity rho (d.O.pointCluster rho i) :=
  paired_rootMultiplicity_balance d.G (d.phi i) (d.a i) (d.b i) (rho.1 i)
    d.G_monic.ne_zero (d.O.centered_phi_ne_zero rho i) (d.paired_product i)

def coordinateUnit (i : Fin n) : (d.O.LocalOrdinary rho)ˣ :=
  (d.O.coordinate rho i).evaluatedUnit
    (d.O.localCenteredX rho i) (d.O.localCenteredX_nilpotent rho i)

theorem local_cofactor_unit (p : Polynomial F) (hp : p≠0) (i : Fin n) :
    IsUnit (Polynomial.aeval (d.O.localX rho i) (rootCofactor p (rho.1 i))) := by
  apply (unit_iff_residue_ne_zero (F := F) (A := d.O.LocalOrdinary rho)
    (d.O.localResidue rho) _).mpr
  rw [←Polynomial.aeval_algHom_apply,d.O.localResidue_x]
  simpa only [Polynomial.aeval_def,Algebra.algebraMap_self,Polynomial.eval₂_id] using
    rootCofactor_eval_ne_zero p hp (rho.1 i)

def localUnitA (i : Fin n) : (d.O.LocalOrdinary rho)ˣ :=
  (d.local_cofactor_unit rho (d.a i) (d.a_monic i).ne_zero i).unit *
    (d.coordinateUnit rho i)⁻¹^d.thetaOrder rho i

def localUnitB (i : Fin n) : (d.O.LocalOrdinary rho)ˣ :=
  (d.local_cofactor_unit rho (d.b i) (d.b_monic i).ne_zero i).unit *
    (d.coordinateUnit rho i)⁻¹^d.xiOrder rho i

theorem localZ_eq_centered_mul_unit (i : Fin n) :
    d.O.localZ rho i=d.O.localCenteredX rho i*(d.coordinateUnit rho i : d.O.LocalOrdinary rho) :=
  (d.O.coordinate rho i).forward_eq_mul_unit _ _

theorem localA_factorization (i : Fin n) :
    d.localA rho i=d.O.localZ rho i^d.thetaOrder rho i*
      (d.localUnitA rho i : d.O.LocalOrdinary rho) := by
  rw [d.localZ_eq_centered_mul_unit,localUnitA]
  rw [unit_coordinate_factorization (d.O.localCenteredX rho i) (d.coordinateUnit rho i)
    (d.local_cofactor_unit rho (d.a i) (d.a_monic i).ne_zero i).unit
    (d.thetaOrder rho i)]
  rw [IsUnit.unit_spec]
  have he := congrArg (Polynomial.aeval (d.O.localX rho i))
    (rootCofactor_factorization (d.a i) (rho.1 i))
  simpa only [map_mul,map_pow,map_sub,Polynomial.aeval_X,Polynomial.aeval_C,
    thetaOrder,localA,SeparatedOrdinaryData.localCenteredX] using he.symm

theorem localB_factorization (i : Fin n) :
    d.localB rho i=d.O.localZ rho i^d.xiOrder rho i*
      (d.localUnitB rho i : d.O.LocalOrdinary rho) := by
  rw [d.localZ_eq_centered_mul_unit,localUnitB]
  rw [unit_coordinate_factorization (d.O.localCenteredX rho i) (d.coordinateUnit rho i)
    (d.local_cofactor_unit rho (d.b i) (d.b_monic i).ne_zero i).unit
    (d.xiOrder rho i)]
  rw [IsUnit.unit_spec]
  have he := congrArg (Polynomial.aeval (d.O.localX rho i))
    (rootCofactor_factorization (d.b i) (rho.1 i))
  simpa only [map_mul,map_pow,map_sub,Polynomial.aeval_X,Polynomial.aeval_C,
    xiOrder,localB,SeparatedOrdinaryData.localCenteredX] using he.symm

/-- The exact product identity for the two residual units. -/
theorem localUnit_product (i : Fin n) :
    (d.localUnitA rho i : d.O.LocalOrdinary rho)*
      (d.localUnitB rho i : d.O.LocalOrdinary rho)=
        Polynomial.aeval (d.O.localNode rho i)
          (rootCofactor d.G (d.O.clusterCenter rho (d.O.pointCluster rho i))) := by
  let w := d.coordinateUnit rho i
  let u := d.thetaOrder rho i
  let v := d.xiOrder rho i
  let r := d.O.ramificationOrder rho i
  let s := d.O.clusterMultiplicity rho (d.O.pointCluster rho i)
  let qa := Polynomial.aeval (d.O.localX rho i) (rootCofactor (d.a i) (rho.1 i))
  let qb := Polynomial.aeval (d.O.localX rho i) (rootCofactor (d.b i) (rho.1 i))
  let H := Polynomial.aeval (d.O.localNode rho i)
    (rootCofactor d.G ((d.phi i).eval (rho.1 i)))
  have hq : qa*qb=(w : d.O.LocalOrdinary rho)^(r*s)*H := by
    have he := congrArg (Polynomial.aeval (d.O.localX rho i))
      (paired_rootCofactor_product d.G (d.phi i) (d.a i) (d.b i) (rho.1 i)
        d.G_monic.ne_zero (d.O.centered_phi_ne_zero rho i) (d.paired_product i))
    have hw := (d.O.coordinate rho i).evaluatedUnit_power
      (d.O.localCenteredX rho i) (d.O.localCenteredX_nilpotent rho i)
    simp only [SeparatedOrdinaryData.localCenteredX,sub_add_cancel] at hw
    simpa only [map_mul,map_pow,Polynomial.aeval_comp,←hw,←pow_mul,
      qa,qb,w,coordinateUnit,r,s,H,O,SeparatedOrdinaryData.localCenteredX,
      SeparatedOrdinaryData.localNode,
      SeparatedOrdinaryData.ramificationOrder,SeparatedOrdinaryData.clusterMultiplicity,
      SeparatedOrdinaryData.pointCluster] using he
  have huv : u+v=r*s := d.local_exponent_balance rho i
  have hw : (w : d.O.LocalOrdinary rho)^(r*s)*
      (↑(w⁻¹) : d.O.LocalOrdinary rho)^(r*s)=1 := by
    rw [←mul_pow,Units.mul_inv,one_pow]
  change _=H
  simp only [localUnitA,localUnitB,Units.val_mul,Units.val_pow_eq_pow_val,IsUnit.unit_spec]
  change (qa*(↑(w⁻¹) : d.O.LocalOrdinary rho)^u)*
    (qb*(↑(w⁻¹) : d.O.LocalOrdinary rho)^v)=H
  calc
    (qa*(↑(w⁻¹) : d.O.LocalOrdinary rho)^u)*
        (qb*(↑(w⁻¹) : d.O.LocalOrdinary rho)^v)=
        (qa*qb)*(↑(w⁻¹) : d.O.LocalOrdinary rho)^(u+v) := by rw [pow_add]; ring
    _=H := by rw [huv,hq]; calc
      (w : d.O.LocalOrdinary rho)^(r*s)*H*
          (↑(w⁻¹) : d.O.LocalOrdinary rho)^(r*s)=
          H*((w : d.O.LocalOrdinary rho)^(r*s)*
            (↑(w⁻¹) : d.O.LocalOrdinary rho)^(r*s)) := by ring
      _=H := by rw [hw,mul_one]

/-- The local exterior presentation is exactly its homogeneous cluster
presentation after the prescribed paired odd coordinate change. -/
def localOddNormalizationEquiv :
    SeparatedOddQuotient (d.O.localNode rho)
      (fun i ↦ algebraMap F (d.O.LocalOrdinary rho) (d.beta i))
      (d.localA rho) (d.localB rho) ≃ₐ[d.O.LocalOrdinary rho]
    ClusterOddQuotient (d.O.pointCluster rho) (d.O.localZ rho)
      (fun i ↦ algebraMap F (d.O.LocalOrdinary rho) (d.beta i))
      (d.O.ramificationOrder rho) (d.thetaOrder rho) (d.xiOrder rho) := by
  let N := (d.O.local_uniform_nilpotence rho).choose
  have hN := (d.O.local_uniform_nilpotence rho).choose_spec
  exact oddNormalizationEquiv d.G d.G_monic.ne_zero (d.O.clusterCenter rho)
    (d.O.clusterCenter_injective rho) (d.O.pointCluster rho) (d.O.localNode rho)
    (d.O.localZ rho) (fun i ↦ algebraMap F (d.O.LocalOrdinary rho) (d.beta i))
    (d.localA rho) (d.localB rho) (d.O.ramificationOrder rho)
    (d.thetaOrder rho) (d.xiOrder rho) (d.O.localZ_power rho)
    (fun _ ↦ N) (by simpa only [SeparatedOrdinaryData.clusterCenter_pointCluster] using hN)
    (d.localUnitA rho) (d.localUnitB rho)
    (d.localA_factorization rho) (d.localB_factorization rho) (d.localUnit_product rho)

end SeparatedPairedData
end PaperVerification.Fermion

