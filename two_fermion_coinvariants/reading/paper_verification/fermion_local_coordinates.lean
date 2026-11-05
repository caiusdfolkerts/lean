module

public import PaperVerification.FermionLocalOrdinary
public import PaperVerification.FermionClusterOrdinary
public import PaperVerification.FermionEvaluatedCoordinates
public import PaperVerification.FermionOrdinaryCurrentNormalization
public import Mathlib.Data.Set.Finite.Range

/-!
# Exact local coefficient algebra isomorphism

The left-hand algebra is the localization of the original ordinary moment
quotient at an actual support point. The right-hand algebra is the quotient
by the independent homogeneous cluster moments. Both maps are explicitly
constructed from inverse formal coordinates. No isomorphism, dimension, or
normal form theorem is assumed.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open Polynomial
open scoped BigOperators Classical

theorem finite_uniform_nilpotence {A ι : Type*} [MonoidWithZero A] [Fintype ι]
    (x : ι → A) (hx : ∀ i,IsNilpotent (x i)) :
    ∃ N : ℕ,∀ i,x i^N=0 := by
  choose N hN using hx
  refine ⟨Finset.univ.sup N,fun i ↦ ?_⟩
  exact pow_eq_zero_of_le (Finset.le_sup (Finset.mem_univ i)) (hN i)

namespace SeparatedOrdinaryData

variable {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
variable (d : SeparatedOrdinaryData F n) (rho : d.SupportPoint)

abbrev PointCluster := Set.range (fun i : Fin n ↦ (d.phi i).eval (rho.1 i))

local instance FermionLocalCoordinates_clusterDecidableEq : DecidableEq (d.PointCluster rho) :=
  fun a b ↦ Classical.propDecidable (a=b)

def pointCluster (i : Fin n) : d.PointCluster rho :=
  ⟨(d.phi i).eval (rho.1 i),i,rfl⟩

def clusterCenter (c : d.PointCluster rho) : F := c.1

theorem clusterCenter_injective : Function.Injective (d.clusterCenter rho) :=
  Subtype.val_injective

@[simp] theorem clusterCenter_pointCluster (i : Fin n) :
    d.clusterCenter rho (d.pointCluster rho i)=(d.phi i).eval (rho.1 i) := rfl

def ramificationOrder (i : Fin n) : ℕ :=
  (d.phi i-C ((d.phi i).eval (rho.1 i))).rootMultiplicity (rho.1 i)

def clusterMultiplicity (c : d.PointCluster rho) : ℕ :=
  d.G.rootMultiplicity c.1

theorem centered_phi_ne_zero (i : Fin n) :
    d.phi i-C ((d.phi i).eval (rho.1 i))≠0 := by
  intro h
  have he := sub_eq_zero.mp h
  have hp := d.phi_pos i
  rw [he,Polynomial.natDegree_C] at hp
  exact Nat.not_lt_zero _ hp

theorem ramificationOrder_pos (i : Fin n) : 0<d.ramificationOrder rho i :=
  (Polynomial.rootMultiplicity_pos (d.centered_phi_ne_zero rho i)).mpr (by
    simp [Polynomial.IsRoot])

theorem clusterMultiplicity_pos (c : d.PointCluster rho) :
    0<d.clusterMultiplicity rho c := by
  obtain ⟨i,hi⟩ := c.property
  apply (Polynomial.rootMultiplicity_pos d.G_monic.ne_zero).mpr
  change d.G.eval c.1=0
  rw [←hi]
  exact rho.property i

def coordinate (i : Fin n) : RamifiedCoordinate (d.phi i) (rho.1 i) :=
  ramifiedCoordinate (d.phi i) (rho.1 i) (d.centered_phi_ne_zero rho i)

def localCenteredX (i : Fin n) : d.LocalOrdinary rho :=
  d.localX rho i-algebraMap F (d.LocalOrdinary rho) (rho.1 i)

theorem localCenteredX_nilpotent (i : Fin n) : IsNilpotent (d.localCenteredX rho i) :=
  d.localX_centered_nilpotent rho i

def localZ (i : Fin n) : d.LocalOrdinary rho :=
  (d.coordinate rho i).forward (d.localCenteredX rho i) (d.localCenteredX_nilpotent rho i)

theorem localZ_nilpotent (i : Fin n) : IsNilpotent (d.localZ rho i) :=
  (d.coordinate rho i).forward_isNilpotent _ _

theorem localZ_power (i : Fin n) :
    d.localZ rho i^d.ramificationOrder rho i=
      d.localNode rho i-algebraMap F (d.LocalOrdinary rho)
        (d.clusterCenter rho (d.pointCluster rho i)) := by
  simpa only [localZ,localCenteredX,ramificationOrder,sub_add_cancel,
    localNode,clusterCenter_pointCluster] using
    (d.coordinate rho i).forward_power (d.localCenteredX rho i)
      (d.localCenteredX_nilpotent rho i)

abbrev HomogeneousOrdinary :=
  ClusterOrdinary d.beta (d.pointCluster rho) (d.ramificationOrder rho)
    (d.clusterMultiplicity rho)

def homogeneousZ (i : Fin n) : d.HomogeneousOrdinary rho :=
  clusterZ d.beta (d.pointCluster rho) (d.ramificationOrder rho)
    (d.clusterMultiplicity rho) i

theorem homogeneousZ_nilpotent (i : Fin n) : IsNilpotent (d.homogeneousZ rho i) :=
  clusterZ_nilpotent d.beta d.beta_units (d.pointCluster rho) (d.ramificationOrder rho)
    (d.clusterMultiplicity rho) i

def homogeneousResidue : d.HomogeneousOrdinary rho →ₐ[F] F :=
  clusterResidue d.beta (d.pointCluster rho) (d.ramificationOrder rho)
    (d.ramificationOrder_pos rho) (d.clusterMultiplicity rho)
    (fun i ↦ d.clusterMultiplicity_pos rho (d.pointCluster rho i))

@[simp] theorem homogeneousResidue_z (i : Fin n) :
    d.homogeneousResidue rho (d.homogeneousZ rho i)=0 :=
  clusterResidue_z d.beta (d.pointCluster rho) (d.ramificationOrder rho)
    (d.ramificationOrder_pos rho) (d.clusterMultiplicity rho)
    (fun i ↦ d.clusterMultiplicity_pos rho (d.pointCluster rho i)) i

theorem homogeneous_unit_iff_residue (a : d.HomogeneousOrdinary rho) :
    IsUnit a ↔ d.homogeneousResidue rho a≠0 :=
  clusterOrdinary_unit_iff_residue d.beta d.beta_units (d.pointCluster rho)
    (d.ramificationOrder rho) (d.ramificationOrder_pos rho)
    (d.clusterMultiplicity rho)
    (fun i ↦ d.clusterMultiplicity_pos rho (d.pointCluster rho i)) a

theorem localZ_moments (c : d.PointCluster rho) (k : ℕ) :
    ∑ i : {i : Fin n // d.pointCluster rho i=c},
      algebraMap F (d.LocalOrdinary rho) (d.beta i.1) *
        d.localZ rho i.1^(d.ramificationOrder rho i.1*(d.clusterMultiplicity rho c+k))=0 := by
  obtain ⟨N,hN⟩ := d.local_uniform_nilpotence rho
  have he := separated_ordinary_cluster_equivalence d.G d.G_monic.ne_zero d.beta
    (d.clusterCenter rho) (d.clusterCenter_injective rho) (d.pointCluster rho)
    (d.localNode rho) (d.localZ rho) (d.ramificationOrder rho)
    (d.localZ_power rho) (fun _ ↦ N) (by simpa only [clusterCenter_pointCluster] using hN)
  exact he.mp (d.local_moments rho) c k

def homogeneousToLocal : d.HomogeneousOrdinary rho →ₐ[F] d.LocalOrdinary rho :=
  clusterOrdinaryLift d.beta (d.pointCluster rho) (d.ramificationOrder rho)
    (d.clusterMultiplicity rho) (d.localZ rho) (d.localZ_moments rho)

@[simp] theorem homogeneousToLocal_z (i : Fin n) :
    d.homogeneousToLocal rho (d.homogeneousZ rho i)=d.localZ rho i :=
  clusterOrdinaryLift_z _ _ _ _ _ _ i

def inverseX (i : Fin n) : d.HomogeneousOrdinary rho :=
  (d.coordinate rho i).backward (d.homogeneousZ rho i) (d.homogeneousZ_nilpotent rho i)+
    algebraMap F (d.HomogeneousOrdinary rho) (rho.1 i)

def inverseNode (i : Fin n) : d.HomogeneousOrdinary rho :=
  Polynomial.aeval (d.inverseX rho i) (d.phi i)

theorem inverseNode_eq (i : Fin n) :
    d.inverseNode rho i=
      algebraMap F (d.HomogeneousOrdinary rho) (d.clusterCenter rho (d.pointCluster rho i))+
        d.homogeneousZ rho i^d.ramificationOrder rho i := by
  exact (d.coordinate rho i).cover_backward _ _

theorem inverseZ_power (i : Fin n) :
    d.homogeneousZ rho i^d.ramificationOrder rho i=
      d.inverseNode rho i-algebraMap F (d.HomogeneousOrdinary rho)
        (d.clusterCenter rho (d.pointCluster rho i)) := by
  rw [d.inverseNode_eq]
  ring

theorem inverseNode_moments (k : ℕ) :
    ∑ i,algebraMap F (d.HomogeneousOrdinary rho) (d.beta i)*d.inverseNode rho i^k*
      Polynomial.aeval (d.inverseNode rho i) d.G=0 := by
  obtain ⟨N,hN⟩ := finite_uniform_nilpotence
    (fun i ↦ d.homogeneousZ rho i^d.ramificationOrder rho i)
    (fun i ↦ (d.homogeneousZ_nilpotent rho i).pow_of_pos
      (d.ramificationOrder_pos rho i).ne')
  have he := separated_ordinary_cluster_equivalence d.G d.G_monic.ne_zero d.beta
    (d.clusterCenter rho) (d.clusterCenter_injective rho) (d.pointCluster rho)
    (d.inverseNode rho) (d.homogeneousZ rho) (d.ramificationOrder rho)
    (d.inverseZ_power rho) (fun _ ↦ N) (by
      intro i
      rw [←d.inverseZ_power rho i]
      exact hN i)
  apply he.mpr
    (fun c k ↦ clusterZ_moments d.beta (d.pointCluster rho)
      (d.ramificationOrder rho) (d.clusterMultiplicity rho) c k) k

def inverseOrdinary : d.Ordinary →ₐ[F] d.HomogeneousOrdinary rho :=
  Ideal.Quotient.liftₐ (separatedOrdinaryIdeal d.beta d.G d.phi)
    (MvPolynomial.aeval (d.inverseX rho)) (by
      have hle : separatedOrdinaryIdeal d.beta d.G d.phi ≤
          RingHom.ker (MvPolynomial.aeval (R := F) (d.inverseX rho)).toRingHom := by
        apply Ideal.span_le.mpr
        rintro p ⟨k,rfl⟩
        change MvPolynomial.aeval (d.inverseX rho)
          (moment (fun i ↦ Polynomial.aeval (MvPolynomial.X i) (d.phi i))
            (fun i ↦ algebraMap F (MvPolynomial (Fin n) F) (d.beta i)*
              Polynomial.aeval (Polynomial.aeval (MvPolynomial.X i) (d.phi i)) d.G) k)=0
        simpa only [moment,smul_eq_mul,map_sum,map_mul,map_pow,
          (MvPolynomial.aeval (d.inverseX rho)).commutes,
          ←Polynomial.aeval_algHom_apply,MvPolynomial.aeval_X,
          inverseNode,mul_assoc,mul_left_comm] using d.inverseNode_moments rho k
      exact fun p hp ↦ hle hp)

@[simp] theorem inverseOrdinary_x (i : Fin n) :
    d.inverseOrdinary rho (d.ordinaryX i)=d.inverseX rho i := by
  change (MvPolynomial.aeval (R := F) (d.inverseX rho)) (MvPolynomial.X i)=d.inverseX rho i
  exact MvPolynomial.aeval_X (d.inverseX rho) i

@[simp] theorem homogeneousResidue_inverseX (i : Fin n) :
    d.homogeneousResidue rho (d.inverseX rho i)=rho.1 i := by
  have hz : d.homogeneousResidue rho
      ((d.coordinate rho i).backward (d.homogeneousZ rho i)
        (d.homogeneousZ_nilpotent rho i))=0 :=
    isNilpotent_iff_eq_zero.mp
      (((d.coordinate rho i).backward_isNilpotent _ _).map
        (d.homogeneousResidue rho).toRingHom)
  simp only [inverseX,map_add,hz,(d.homogeneousResidue rho).commutes,
    Algebra.algebraMap_self,RingHom.id_apply,zero_add]

theorem inverseOrdinary_residue :
    (d.homogeneousResidue rho).comp (d.inverseOrdinary rho)=d.pointResidue rho := by
  apply Ideal.Quotient.algHom_ext F
  apply MvPolynomial.algHom_ext
  intro i
  change d.homogeneousResidue rho (d.inverseOrdinary rho (d.ordinaryX i))=
    d.pointResidue rho (d.ordinaryX i)
  simp only [inverseOrdinary_x,homogeneousResidue_inverseX,pointResidue_x]

def localToHomogeneous : d.LocalOrdinary rho →ₐ[F] d.HomogeneousOrdinary rho :=
  IsLocalization.liftAlgHom (M := (d.pointMaximal rho).primeCompl)
    (S := d.LocalOrdinary rho) (f := d.inverseOrdinary rho) (by
    intro y
    apply (d.homogeneous_unit_iff_residue rho _).mpr
    have he := AlgHom.congr_fun (d.inverseOrdinary_residue rho) (y : d.Ordinary)
    simp only [AlgHom.comp_apply] at he
    change d.homogeneousResidue rho (d.inverseOrdinary rho (y : d.Ordinary))≠0
    rw [he]
    exact y.property)

@[simp] theorem localToHomogeneous_map (a : d.Ordinary) :
    d.localToHomogeneous rho (d.localMap rho a)=d.inverseOrdinary rho a :=
  IsLocalization.lift_eq _ a

@[simp] theorem localToHomogeneous_x (i : Fin n) :
    d.localToHomogeneous rho (d.localX rho i)=d.inverseX rho i := by
  simp [localX]

@[simp] theorem localToHomogeneous_centeredX (i : Fin n) :
    d.localToHomogeneous rho (d.localCenteredX rho i)=
      (d.coordinate rho i).backward (d.homogeneousZ rho i) (d.homogeneousZ_nilpotent rho i) := by
  simp only [localCenteredX,map_sub,localToHomogeneous_x,
    (d.localToHomogeneous rho).commutes,inverseX,add_sub_cancel_right]

@[simp] theorem localToHomogeneous_z (i : Fin n) :
    d.localToHomogeneous rho (d.localZ rho i)=d.homogeneousZ rho i := by
  rw [localZ,(d.coordinate rho i).forward_map (d.localCenteredX rho i)
    (d.localCenteredX_nilpotent rho i) (d.localToHomogeneous rho)]
  simp only [localToHomogeneous_centeredX,RamifiedCoordinate.forward_backward]

theorem local_homogeneous_inverse :
    (d.homogeneousToLocal rho).comp (d.localToHomogeneous rho)=
      AlgHom.id F (d.LocalOrdinary rho) := by
  apply d.local_hom_ext rho
  intro i
  simp only [AlgHom.comp_apply,AlgHom.id_apply,localToHomogeneous_x,inverseX,map_add,
    (d.homogeneousToLocal rho).commutes]
  have hb : d.homogeneousToLocal rho
      ((d.coordinate rho i).backward (d.homogeneousZ rho i)
        (d.homogeneousZ_nilpotent rho i))=d.localCenteredX rho i := by
    simpa only [homogeneousToLocal_z,localZ,RamifiedCoordinate.backward_forward] using
      ((d.coordinate rho i).backward_map (A := d.HomogeneousOrdinary rho)
        (B := d.LocalOrdinary rho) (d.homogeneousZ rho i)
        (d.homogeneousZ_nilpotent rho i) (d.homogeneousToLocal rho))
  exact (congrArg (fun a : d.LocalOrdinary rho ↦
    a+algebraMap F (d.LocalOrdinary rho) (rho.1 i)) hb).trans
      (sub_add_cancel _ _)

theorem homogeneous_local_inverse :
    (d.localToHomogeneous rho).comp (d.homogeneousToLocal rho)=
      AlgHom.id F (d.HomogeneousOrdinary rho) := by
  apply clusterOrdinary_hom_ext
  intro i
  change d.localToHomogeneous rho (d.homogeneousToLocal rho (d.homogeneousZ rho i))=
    d.homogeneousZ rho i
  rw [d.homogeneousToLocal_z]
  exact d.localToHomogeneous_z rho i

/-- Genuine local coefficient algebra isomorphism at every actual support
point. The cluster exponents are the literal root multiplicities. -/
def localOrdinaryEquivHomogeneous :
    d.LocalOrdinary rho ≃ₐ[F] d.HomogeneousOrdinary rho :=
  AlgEquiv.ofAlgHom (d.localToHomogeneous rho) (d.homogeneousToLocal rho)
    (d.homogeneous_local_inverse rho) (d.local_homogeneous_inverse rho)

@[simp] theorem localOrdinaryEquivHomogeneous_x (i : Fin n) :
    d.localOrdinaryEquivHomogeneous rho (d.localX rho i)=d.inverseX rho i :=
  d.localToHomogeneous_x rho i

@[simp] theorem localOrdinaryEquivHomogeneous_z (i : Fin n) :
    d.localOrdinaryEquivHomogeneous rho (d.localZ rho i)=d.homogeneousZ rho i :=
  d.localToHomogeneous_z rho i

end SeparatedOrdinaryData
end PaperVerification.Fermion

