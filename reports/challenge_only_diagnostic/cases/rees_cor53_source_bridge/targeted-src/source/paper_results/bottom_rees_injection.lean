module
public import paper_results.part005
public import paper_results.part003
public import shared_results.part010

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.BottomReesInjection -/
section

/-! # Minimum multiplication on the actual complete Rees homology algebra

The preceding filtered proof is transported to the genuine upper Koszul
strands. Finite coefficient decomposition then proves injection on the
entire Rees homology algebra, retaining the literal generator throughout.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.FilteredHomology
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
  (μ : E) (hμ : ∀ a : E, μ.val ≤ a.val) (hE : finiteLatticeClosed n E)

theorem bottom_chain_coordinate_d (m : ℕ) (α : Exponent (FiniteVariable.{u} n))
    (x : ChainTotalModule n E m α k) :
    chainTotalEquiv hE m α k (chainTotalOrdinaryDifferential hE m α k x) =
      powerFaceDifferential m α (chainTotalEquiv hE m α k x) := by
  simp only [chainTotalOrdinaryDifferential,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

def bottomPowerFaceMap (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) :
    PowerFaceModule (E:=E) (k:=k) m α →ₗ[k]
      PowerFaceModule (E:=E) (k:=k) (m+1) (α+finiteRowExponent n μ.val) :=
  (chainTotalEquiv hE (m+1) (α+finiteRowExponent n μ.val) k).toLinearMap.comp
    ((bottomChainMap μ hμ m α).comp (chainTotalEquiv hE m α k).symm.toLinearMap)

/-- Under the actual monomial coefficient model this is multiplication by
the minimum generator: it shifts the monomial degree and keeps the face. -/
@[simp] theorem bottomPowerFaceMap_val (m : ℕ) (α : Exponent (FiniteVariable.{u} n))
    (x : PowerFaceModule (E:=E) (k:=k) m α) :
    (bottomPowerFaceMap μ hμ hE m α x).val = x.val := by
  change (chainTotalEquiv hE (m+1) (α+finiteRowExponent n μ.val) k
    (bottomChainMap μ hμ m α ((chainTotalEquiv hE m α k).symm x))).val = x.val
  rw [bottomChainMap_actual_coordinates,LinearEquiv.apply_symm_apply]

/-- A boundary of the literal multiplied cycle reflects to a boundary in
the source fine strand. No homogeneous degree is discarded. -/
theorem bottomPowerFace_reflects_boundaries (m : ℕ)
    (α : Exponent (FiniteVariable.{u} n)) (x : PowerFaceModule (E:=E) (k:=k) m α)
    (hx : powerFaceDifferential m α x = 0)
    (hb : ∃ w, powerFaceDifferential (m+1) (α+finiteRowExponent n μ.val) w =
      bottomPowerFaceMap μ hμ hE m α x) :
    ∃ y, powerFaceDifferential m α y = x := by
  let e := chainTotalEquiv hE m α k
  let e' := chainTotalEquiv hE (m+1) (α+finiteRowExponent n μ.val) k
  let D := chainTotalOrdinaryDifferential hE m α k
  let D' := chainTotalOrdinaryDifferential hE (m+1) (α+finiteRowExponent n μ.val) k
  have hz : D (e.symm x) = 0 := by
    apply e.injective
    rw [e.map_zero]
    change chainTotalEquiv hE m α k (D (e.symm x)) = 0
    rw [bottom_chain_coordinate_d,LinearEquiv.apply_symm_apply,hx]
  obtain ⟨w,hw⟩ := hb
  have hboundary : D' (e'.symm w) = bottomChainMap μ hμ m α (e.symm x) := by
    apply e'.injective
    change chainTotalEquiv hE (m+1) (α+finiteRowExponent n μ.val) k
      (D' (e'.symm w)) = _
    rw [bottom_chain_coordinate_d,LinearEquiv.apply_symm_apply,hw]
    rfl
  have hinj := bottomChainHomologyMap_injective (k := k) μ hμ hE m α
  unfold bottomChainHomologyMap at hinj
  obtain ⟨y, hy⟩ := threeTermHomologyMap_reflects_boundaries_of_injective
    hinj (e.symm x) hz ⟨e'.symm w, hboundary⟩
  refine ⟨e y, ?_⟩
  rw [← bottom_chain_coordinate_d]
  exact (congrArg e hy).trans (e.apply_symm_apply x)

theorem bottom_generator_face_mem :
    (1 : Simplicial.Ambient (FiniteVariable.{u} n) k) ∈
      PowerFaceModule (E:=E) (k:=k) 1 (finiteRowExponent n μ.val) := by
  rw [← faceBasis_empty]
  apply Submodule.subset_span
  refine ⟨∅,?_,rfl⟩
  constructor
  · simp only [faceExponent_empty,zero_le]
  · refine ⟨finiteRowExponent n μ.val,?_,?_⟩
    · change finiteRowExponent n μ.val ∈
        (({0} : Finset (Exponent (FiniteVariable.{u} n))).product (finiteRowFamily n E)).image
          (fun bc => bc.1+bc.2)
      exact Finset.mem_image.mpr ⟨(0,finiteRowExponent n μ.val),
        Finset.mem_product.mpr ⟨Finset.mem_singleton_self 0,
          Finset.mem_image.mpr ⟨μ.val,μ.property,rfl⟩⟩,zero_add _⟩
    · simp only [faceExponent_empty,tsub_zero,le_refl]

def bottomReesCycle : (reesKoszulCoordinateDifferential (k:=k) hE).cycles :=
  reesCycleSingle hE (1,finiteRowExponent n μ.val)
    ⟨⟨1,bottom_generator_face_mem (k:=k) μ⟩,by
      apply Subtype.ext
      exact CliffordAlgebra.contractLeft_one _ _⟩

@[simp] theorem bottomReesCycle_val : (bottomReesCycle (k:=k) μ hE).val.val =
    AddMonoidAlgebra.single (1,finiteRowExponent n μ.val) 1 := rfl

include hμ in
/-- Multiplication by the genuine minimum-generator class is injective on
the entire homology algebra, over every commutative coefficient ring. -/
theorem bottomReesHomologyMul_injective :
    Function.Injective (fun z : ReesKoszulCoordinateHomology (k:=k) hE =>
      (reesKoszulCoordinateDifferential hE).classMap (bottomReesCycle μ hE) * z) := by
  let D := reesKoszulCoordinateDifferential (k:=k) hE
  have hzero : ∀ z : D.Homology, D.classMap (bottomReesCycle μ hE)*z = 0 → z=0 := by
    intro z hz
    obtain ⟨x,rfl⟩ := D.classMap_surjective z
    have hp : D.classMap (bottomReesCycle μ hE*x)=0 := by
      rw [map_mul D.classMap]
      exact hz
    obtain ⟨w,hw⟩ := (D.classMap_eq_zero _).mp hp
    rw [← reesCycle_decomposition (k:=k) hE x, map_sum D.classMap]
    apply Finset.sum_eq_zero
    intro g hg
    obtain ⟨m,α⟩ := g
    let c := reesCycleCoefficient (k:=k) hE (m,α) x
    have hb : ∃ v, powerFaceDifferential (m+1) (α+finiteRowExponent n μ.val) v =
        bottomPowerFaceMap μ hμ hE m α c.val := by
      refine ⟨reesKoszulCoefficient hE (m+1,α+finiteRowExponent n μ.val) w,?_⟩
      apply Subtype.ext
      change (D.d w).val.coeff (m+1,α+finiteRowExponent n μ.val) = _
      rw [hw]
      change (AddMonoidAlgebra.single (1,finiteRowExponent n μ.val) 1*x.val.val).coeff
        (m+1,α+finiteRowExponent n μ.val) = _
      have hindex : (m+1,α+finiteRowExponent n μ.val) =
          (1,finiteRowExponent n μ.val)+(m,α) := by
        simp only [Prod.mk_add_mk,add_comm]
      rw [hindex,AddMonoidAlgebra.coeff_single_mul_add,one_mul,bottomPowerFaceMap_val]
      rfl
    obtain ⟨v,hv⟩ := bottomPowerFace_reflects_boundaries μ hμ hE m α c.val c.property hb
    exact reesHomologyPieceMap_boundary (k:=k) hE (m,α) v c hv
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero
  change D.classMap (bottomReesCycle μ hE) * x =
    D.classMap (bottomReesCycle μ hE) * y at hxy
  rw [mul_sub,hxy,sub_self]

end FourPapers.Sublattice

end
end
end


end
