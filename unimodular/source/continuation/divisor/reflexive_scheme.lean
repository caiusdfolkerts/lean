module

public import Continuation.Divisor.ReverseFanInterface
public import Continuation.Divisor.ProjectiveComparison
public import Continuation.Divisor.FullSupportCriterion
public import Continuation.Divisor.StrictProjectivity
public import Unimodular.PolytopeFans

/-!
# The actual scheme of a smooth reflexive presentation

The complete normal fan is transferred without changing any cone or
primitive ray. Its integral Cartier vertices are the negatives of the
original outward-normal vertices. Strict unit support and the actual
primitive unit steps then give the projective chart comparison.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u
namespace Unimodular.SmoothReflexivePresentation

open Set TauCeti.Toric AlgebraicGeometry CategoryTheory
open Unimodular.FanInterfaces Unimodular.Projectivity
open scoped Classical BigOperators

variable {n : ℕ} (P : SmoothReflexivePresentation n)

def schemeFan : PaperVerification.ToricGeometry.SmoothCompleteFan n :=
  geometricFan P.normalFan P.normalFan_complete P.normalFan_regular

@[simp] theorem schemeFan_all_cones : dictionaryToricFan P.schemeFan = P.normalFan :=
  dictionaryToricFan_geometricFan P.normalFan P.normalFan_complete P.normalFan_regular

@[simp] theorem schemeFan_ray_iff (u : Lattice n) : u ∈ P.schemeFan.rays ↔ u ∈ P.normals := by
  rw [schemeFan, geometricFan_ray_iff, P.normalFan_ray_iff]

/-- Every actual full cone is exactly one original vertex normal cone,
with its primitive integral basis changed only by a permutation. -/
theorem fullCone_vertex_match (s : P.schemeFan.fullCones) :
    ∃ v : {v // v ∈ P.vertices}, ∃ e : Fin n ≃ Fin n,
      PaperVerification.ToricGeometry.latticeRayCone s.val =
        ConeBases.cone (ι := FanBridge.standardEmbedding n) (P.basis v) ∧
      ∀ i, P.schemeFan.fullConeBasis s i = P.basis v (e i) := by
  have hC : PaperVerification.ToricGeometry.latticeRayCone s.val ∈ P.normalFan.cones := by
    rw [← P.schemeFan_all_cones]
    exact ⟨s.val, P.schemeFan.fullCones_mem s, rfl⟩
  obtain ⟨v, hv⟩ := (P.mem_normalFan_cones_iff _).mp hC
  have hfull : Submodule.span ℝ
      (PaperVerification.ToricGeometry.latticeRayCone s.val : Set (Ambient n)) = ⊤ := by
    rw [P.schemeFan.fullConeBasis_ray_set, latticeRayCone_full_basis]
    exact ConeBases.span_cone P.normalFan.lattice (P.schemeFan.fullConeBasis s)
  have hvC : ConeBases.cone (ι := FanBridge.standardEmbedding n) (P.basis v) ∈
      P.normalFan.cones :=
    (P.mem_normalFan_cones_iff _).mpr ⟨v, PointedCone.IsFaceOf.refl _⟩
  have he := (FanMaximalCones.full_iff_maximal P.normalFan P.normalFan_complete hC).mp
    hfull _ hvC hv.le
  have he' : ConeBases.cone (ι := FanBridge.standardEmbedding n) (P.schemeFan.fullConeBasis s) =
      ConeBases.cone (ι := FanBridge.standardEmbedding n) (P.basis v) := by
    rw [← latticeRayCone_full_basis, ← P.schemeFan.fullConeBasis_ray_set]
    exact he
  obtain ⟨e, hperm⟩ := ConeBases.basis_permutation_of_cone_eq P.normalFan.lattice _ _ he'
  exact ⟨v, e, he, hperm⟩

def fullConeVertex (s : P.schemeFan.fullCones) : {v // v ∈ P.vertices} :=
  Classical.choose (P.fullCone_vertex_match s)

def fullConePermutation (s : P.schemeFan.fullCones) : Fin n ≃ Fin n :=
  Classical.choose (Classical.choose_spec (P.fullCone_vertex_match s))

theorem fullConeVertex_cone (s : P.schemeFan.fullCones) :
    PaperVerification.ToricGeometry.latticeRayCone s.val =
      ConeBases.cone (ι := FanBridge.standardEmbedding n) (P.basis (P.fullConeVertex s)) :=
  (Classical.choose_spec (Classical.choose_spec (P.fullCone_vertex_match s))).1

theorem fullConeVertex_basis (s : P.schemeFan.fullCones) (i : Fin n) :
    P.schemeFan.fullConeBasis s i = P.basis (P.fullConeVertex s) (P.fullConePermutation s i) :=
  (Classical.choose_spec (Classical.choose_spec (P.fullCone_vertex_match s))).2 i

/-- The integral Cartier point is identified in the original lattice. -/
theorem unit_cartierLatticePoint (s : P.schemeFan.fullCones) :
    P.schemeFan.cartierLatticePoint (fun _ => (1 : ℤ)) s = -(P.fullConeVertex s).val := by
  symm
  apply P.schemeFan.eq_cartierLatticePoint_of_pairings
  intro u hu
  rw [P.schemeFan.fullConeBasis_ray_set] at hu
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
  rw [P.fullConeVertex_basis]
  have h := P.basis_active (P.fullConeVertex s) (P.fullConePermutation s i)
  rw [pairing_embed] at h
  have hZ : integerPairing (P.fullConeVertex s).val
      (P.basis (P.fullConeVertex s) (P.fullConePermutation s i)) = 1 := by
    exact_mod_cast h
  calc
    PaperVerification.ToricGeometry.integerPairing
        (P.basis (P.fullConeVertex s) (P.fullConePermutation s i))
        (-(P.fullConeVertex s).val) =
      -integerPairing (P.fullConeVertex s).val
        (P.basis (P.fullConeVertex s) (P.fullConePermutation s i)) := by
      simp only [PaperVerification.ToricGeometry.integerPairing, integerPairing,
        Pi.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib, mul_comm]
    _ = -1 := by rw [hZ]

theorem unit_cartierPairing (s : P.schemeFan.fullCones) (u : Lattice n) :
    (dotProductEquiv ℝ (Fin n) (PaperVerification.ToricGeometry.embed n u))
      (P.schemeFan.cartierPoint (fun _ => (1 : ℝ)) s) =
        -pairing (embed (P.fullConeVertex s).val) u := by
  have hcart : PaperVerification.ToricGeometry.embed n
      (P.schemeFan.cartierLatticePoint (fun _ => (1 : ℤ)) s) =
        P.schemeFan.cartierPoint (fun _ => (1 : ℝ)) s := by
    simpa only [Int.cast_one] using
      P.schemeFan.embed_cartierLatticePoint (fun _ => (1 : ℤ)) s
  rw [← hcart, P.unit_cartierLatticePoint]
  simp [dotProductEquiv, dotProduct, PaperVerification.ToricGeometry.embed,
    pairing, embed, mul_comm]

/-- The original reflexive facet equations give strict unit support on
all actual fan cones, including every proper face. -/
theorem schemeFan_strict_unit_support : P.schemeFan.IsStrictSupport (fun _ => 1) := by
  apply P.schemeFan.strictSupport_of_full_cartier_inequalities P.schemeFan.isPure
  intro s u hu hus
  rw [P.unit_cartierPairing]
  have hle := (P.mem_carrier_iff _).mp (P.vertex_mem (P.fullConeVertex s)) u
    ((P.schemeFan_ray_iff u).mp hu)
  have hne : pairing (embed (P.fullConeVertex s).val) u ≠ 1 := by
    intro he
    obtain ⟨j, hj⟩ := P.active_subset (P.fullConeVertex s) u
      ((P.schemeFan_ray_iff u).mp hu) he
    obtain ⟨i, hi⟩ := (P.fullConePermutation s).surjective j
    apply hus
    rw [P.schemeFan.fullConeBasis_ray_set]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i,
      (P.fullConeVertex_basis s i).trans (by rw [hi]; exact hj)⟩
  linarith [lt_of_le_of_ne hle hne]

/-- The integral coefficient function is cast explicitly for support-polytope
constructions; its real values are the same unit support function. -/
theorem schemeFan_strict_unit_support_int :
    P.schemeFan.IsStrictSupport (fun _ => ((1 : ℤ) : ℝ)) := by
  simpa only [Int.cast_one] using P.schemeFan_strict_unit_support

/-- The genuine inward-normal lattice polytope used for the Proj weights. -/
def schemePolytope : PaperVerification.ToricGeometry.LatticePolytope n :=
  P.schemeFan.supportLatticePolytope P.schemeFan.isPure (fun _ => (1 : ℤ))
    P.schemeFan_strict_unit_support_int

/-- Its carrier is exactly the negative of the original outward-normal
polytope. The sign is explicit rather than hidden in a fan convention. -/
theorem mem_schemePolytope_iff (x : Ambient n) :
    x ∈ P.schemePolytope.carrier ↔ -x ∈ P.carrier := by
  rw [schemePolytope, P.schemeFan.supportLatticePolytope_carrier, P.mem_carrier_iff]
  have hneg (u : Lattice n) :
      (∑ i, (-x i) * (u i : ℝ)) = -(∑ i, (u i : ℝ) * x i) := by
    calc
      (∑ i, (-x i) * (u i : ℝ)) = ∑ i, -((u i : ℝ) * x i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = -(∑ i, (u i : ℝ) * x i) := by rw [Finset.sum_neg_distrib]
  constructor
  · intro hx u hu
    have h := hx u ((P.schemeFan_ray_iff u).mpr hu)
    simp only [Int.cast_one] at h
    change -1 ≤ ∑ i, (u i : ℝ) * x i at h
    change ∑ i, (-x i) * (u i : ℝ) ≤ 1
    rw [hneg u]
    linarith
  · intro hx u hu
    have h := hx u ((P.schemeFan_ray_iff u).mp hu)
    change ∑ i, (-x i) * (u i : ℝ) ≤ 1 at h
    simp only [Int.cast_one]
    change -1 ≤ ∑ i, (u i : ℝ) * x i
    rw [hneg u] at h
    linarith

theorem schemePolytope_normalCone (s : P.schemeFan.fullCones) :
    P.schemePolytope.normalCone
      (PaperVerification.ToricGeometry.embed n
        (P.schemeFan.cartierLatticePoint (fun _ => 1) s)) =
      (PaperVerification.ToricGeometry.latticeRayCone s.val : Set (Ambient n)) := by
  rw [P.schemeFan.embed_cartierLatticePoint]
  exact P.schemeFan.supportLatticePolytope_cartier_normalCone P.schemeFan.isPure
    (fun _ => (1 : ℤ)) P.schemeFan_strict_unit_support_int s

/-- Primitive unit-step membership is supplied by the general integral
strict-support argument, with the actual support polytope unchanged. -/
theorem schemePolytope_unitStep (s : P.schemeFan.fullCones) (i : Fin n) :
    PaperVerification.ToricGeometry.embed n
      (P.schemeFan.cartierLatticePoint (fun _ => 1) s +
        PaperVerification.ToricGeometry.integralDualBasis (P.schemeFan.fullConeBasis s) i) ∈
      P.schemePolytope.carrier :=
  P.schemeFan.supportLatticePolytope_unitStep (fun _ => (1 : ℤ))
    P.schemeFan_strict_unit_support_int s i

/-- The actual Proj chart hypotheses follow from strict support. -/
def projectiveVertexData : VertexChartData P.schemeFan P.schemePolytope :=
  strictSupportVertexData P.schemeFan (fun _ => (1 : ℤ))
    P.schemeFan_strict_unit_support_int

variable (k : Type u) [Field k]

/-- The actual smooth-reflexive fan scheme admits the displayed ordinary
finite projective closed immersion. -/
def projectiveEmbedding := P.projectiveVertexData.fanProjectiveEmbedding k

instance projectiveEmbedding_isClosedImmersion : IsClosedImmersion (P.projectiveEmbedding k) :=
  P.projectiveVertexData.fanProjectiveEmbedding_isClosedImmersion k

#print axioms schemeFan_strict_unit_support
#print axioms projectiveVertexData
#print axioms projectiveEmbedding_isClosedImmersion

end Unimodular.SmoothReflexivePresentation
