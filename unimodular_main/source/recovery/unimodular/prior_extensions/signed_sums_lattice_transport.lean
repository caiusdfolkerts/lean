module

public import Recovery.Unimodular.PriorExtensions.SignedSumsPaper
public import Recovery.Unimodular.ProductLatticeCoordinates

/-!
# Literal signed quotients in arbitrary integral lattices

Coordinate changes carry the actual relation subgroup and every surviving
column exactly. Thus freeness, rank, integral spanning and unimodularity of
the coordinate construction refer to the original quotient lattice itself.
The original real vector matroids and full spanning hypotheses are unchanged.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

open TauCeti.Toric

namespace Unimodular.SignedSums

section Naturality
variable {R P N₁ N₂ M₁ M₂ : Type*} [CommRing R]
  [AddCommGroup P] [Module R P]
  [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

theorem originalRelation_map_range (a₁ : P →ₗ[R] N₁) (a₂ : P →ₗ[R] N₂)
    (b₁ : P →ₗ[R] M₁) (b₂ : P →ₗ[R] M₂)
    (e₁ : N₁ ≃ₗ[R] M₁) (e₂ : N₂ ≃ₗ[R] M₂)
    (h₁ : ∀ p, e₁ (a₁ p) = b₁ p) (h₂ : ∀ p, e₂ (a₂ p) = b₂ p) :
    (LinearMap.range (originalRelation a₁ a₂)).map (e₁.prodCongr e₂).toLinearMap =
      LinearMap.range (originalRelation b₁ b₂) := by
  ext y
  constructor
  · rintro ⟨x, ⟨p, rfl⟩, rfl⟩
    exact ⟨p, by simp [originalRelation, h₁, h₂]⟩
  · rintro ⟨p, rfl⟩
    exact ⟨originalRelation a₁ a₂ p, ⟨p, rfl⟩, by simp [originalRelation, h₁, h₂]⟩

def originalQuotientCongr (a₁ : P →ₗ[R] N₁) (a₂ : P →ₗ[R] N₂)
    (b₁ : P →ₗ[R] M₁) (b₂ : P →ₗ[R] M₂)
    (e₁ : N₁ ≃ₗ[R] M₁) (e₂ : N₂ ≃ₗ[R] M₂)
    (h₁ : ∀ p, e₁ (a₁ p) = b₁ p) (h₂ : ∀ p, e₂ (a₂ p) = b₂ p) :
    OriginalQuotient a₁ a₂ ≃ₗ[R] OriginalQuotient b₁ b₂ :=
  Submodule.Quotient.equiv _ _ (e₁.prodCongr e₂)
    (originalRelation_map_range a₁ a₂ b₁ b₂ e₁ e₂ h₁ h₂)

@[simp] theorem originalQuotientCongr_mk (a₁ : P →ₗ[R] N₁) (a₂ : P →ₗ[R] N₂)
    (b₁ : P →ₗ[R] M₁) (b₂ : P →ₗ[R] M₂)
    (e₁ : N₁ ≃ₗ[R] M₁) (e₂ : N₂ ≃ₗ[R] M₂)
    (h₁ : ∀ p, e₁ (a₁ p) = b₁ p) (h₂ : ∀ p, e₂ (a₂ p) = b₂ p)
    (x : N₁ × N₂) :
    originalQuotientCongr a₁ a₂ b₁ b₂ e₁ e₂ h₁ h₂ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (e₁ x.1, e₂ x.2) := rfl

@[simp] theorem originalQuotientCongr_family {L S : Type*}
    (a₁ : P →ₗ[R] N₁) (a₂ : P →ₗ[R] N₂)
    (b₁ : P →ₗ[R] M₁) (b₂ : P →ₗ[R] M₂)
    (e₁ : N₁ ≃ₗ[R] M₁) (e₂ : N₂ ≃ₗ[R] M₂)
    (h₁ : ∀ p, e₁ (a₁ p) = b₁ p) (h₂ : ∀ p, e₂ (a₂ p) = b₂ p)
    (U : L → N₁) (V : S → N₂) (j : L ⊕ S) :
    originalQuotientCongr a₁ a₂ b₁ b₂ e₁ e₂ h₁ h₂ (originalFamily a₁ a₂ U V j) =
      originalFamily b₁ b₂ (e₁ ∘ U) (e₂ ∘ V) j := by
  cases j <;> simp [originalFamily]
end Naturality

section Integral
variable {n₁ n₂ r : ℕ} {N₁ N₂ T L S : Type*} [AddCommGroup N₁] [AddCommGroup N₂]

def latticePortMap {N : Type*} [AddCommGroup N] (u : Fin r → N) :
    (Fin r → ℤ) →ₗ[ℤ] N := (Pi.basisFun ℤ (Fin r)).constr ℤ u

abbrev LatticePortQuotient (τ : Fin r → T) (U : T ⊕ L → N₁) (V : T ⊕ S → N₂) :=
  OriginalQuotient (latticePortMap (fun i => U (.inl (τ i))))
    (latticePortMap (fun i => V (.inl (τ i))))

def latticePortOutput (τ : Fin r → T) (U : T ⊕ L → N₁) (V : T ⊕ S → N₂) :
    L ⊕ S → LatticePortQuotient τ U V :=
  originalFamily (latticePortMap (fun i => U (.inl (τ i))))
    (latticePortMap (fun i => V (.inl (τ i)))) (U ∘ Sum.inr) (V ∘ Sum.inr)

theorem latticePortMap_coordinates {n : ℕ} {N : Type*} [AddCommGroup N]
    (e : N ≃ₗ[ℤ] Lattice n) (u : Fin r → N) (p : Fin r → ℤ) :
    e (latticePortMap u p) = portMap (e ∘ u) p := by
  have h : e.toLinearMap.comp (latticePortMap u) = portMap (e ∘ u) := by
    apply (Pi.basisFun ℤ (Fin r)).ext
    intro i
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, latticePortMap, portMap,
      Module.Basis.constr_basis, Function.comp_apply]
  exact LinearMap.congr_fun h p

def coordinatePortQuotientEquiv (e₁ : N₁ ≃ₗ[ℤ] Lattice n₁)
    (e₂ : N₂ ≃ₗ[ℤ] Lattice n₂) (τ : Fin r → T)
    (U : T ⊕ L → N₁) (V : T ⊕ S → N₂) :
    LatticePortQuotient τ U V ≃ₗ[ℤ] PortQuotient τ (e₁ ∘ U) (e₂ ∘ V) :=
  originalQuotientCongr _ _ _ _ e₁ e₂
    (latticePortMap_coordinates e₁ _) (latticePortMap_coordinates e₂ _)

@[simp] theorem coordinatePortQuotientEquiv_output (e₁ : N₁ ≃ₗ[ℤ] Lattice n₁)
    (e₂ : N₂ ≃ₗ[ℤ] Lattice n₂) (τ : Fin r → T)
    (U : T ⊕ L → N₁) (V : T ⊕ S → N₂) (j : L ⊕ S) :
    coordinatePortQuotientEquiv e₁ e₂ τ U V (latticePortOutput τ U V j) =
      PortOutput τ (e₁ ∘ U) (e₂ ∘ V) j := by
  exact originalQuotientCongr_family _ _ _ _ e₁ e₂
    (latticePortMap_coordinates e₁ _) (latticePortMap_coordinates e₂ _) _ _ j

def LatticeSumConclusion (n₁ n₂ : ℕ) (τ : Fin r → T)
    (U : T ⊕ L → N₁) (V : T ⊕ S → N₂) : Prop :=
  ∃ k : ℕ, ∃ b : Module.Basis (Fin k) ℤ (LatticePortQuotient τ U V),
    k + r = n₁ + n₂ ∧ IntegralRigidity.Uniform b (latticePortOutput τ U V) ∧
    Submodule.span ℤ (Set.range (latticePortOutput τ U V)) = ⊤ ∧
    Matrix.IsTotallyUnimodular (fun i j => b.repr (latticePortOutput τ U V j) i)

/-- Every lattice conclusion descends to the literal arbitrary original
lattices, including an actual basis and integral spanning of surviving columns. -/
theorem latticeSumConclusion_of_coordinates (e₁ : N₁ ≃ₗ[ℤ] Lattice n₁)
    (e₂ : N₂ ≃ₗ[ℤ] Lattice n₂) (τ : Fin r → T)
    (U : T ⊕ L → N₁) (V : T ⊕ S → N₂)
    (h : SumConclusion τ (e₁ ∘ U) (e₂ ∘ V)) : LatticeSumConclusion n₁ n₂ τ U V := by
  classical
  obtain ⟨k, b, hk, _hU, hs, ht⟩ := h
  let e := coordinatePortQuotientEquiv e₁ e₂ τ U V
  let b' := b.map e.symm
  have hcoords : (fun i j => b'.repr (latticePortOutput τ U V j) i) =
      (fun i j => b.repr (PortOutput τ (e₁ ∘ U) (e₂ ∘ V) j) i) := by
    funext i j
    change b.repr (e (latticePortOutput τ U V j)) i = _
    rw [coordinatePortQuotientEquiv_output]
  have ht' : Matrix.IsTotallyUnimodular (fun i j => b'.repr (latticePortOutput τ U V j) i) := by
    rw [hcoords]
    exact ht
  refine ⟨k, b', hk, uniform_of_coordinate_tu b' _ ht', ?_, ht'⟩
  apply (Submodule.map_eq_top_iff (e := e)).mp
  rw [Submodule.map_span, ← Set.range_comp]
  change Submodule.span ℤ (Set.range (e ∘ latticePortOutput τ U V)) = ⊤
  have heq : e ∘ latticePortOutput τ U V = PortOutput τ (e₁ ∘ U) (e₂ ∘ V) :=
    funext (coordinatePortQuotientEquiv_output e₁ e₂ τ U V)
  rw [heq]
  exact hs

end Integral

section RealCoordinates
open LatticeCoordinates
variable {n : ℕ} {N V E : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {ι : N →+ V}

theorem lattice_span_coordinates_iff (hι : IsIntegralLattice ι)
    (b : Module.Basis (Fin n) ℤ N) (U : E → N) :
    Submodule.span ℝ (Set.range (fun j => embed (latticeEquiv b (U j)))) = ⊤ ↔
      Submodule.span ℝ (Set.range (fun j => ι (U j))) = ⊤ := by
  have hmap : (Submodule.span ℝ (Set.range (fun j => ι (U j)))).map
      (realEquiv hι b).toLinearMap =
      Submodule.span ℝ (Set.range (fun j => embed (latticeEquiv b (U j)))) := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact congrArg (fun f : E → Ambient n => Submodule.span ℝ (Set.range f))
      (funext (fun j => coordinates_commute hι b (U j)))
  rw [← hmap]
  exact Submodule.map_eq_top_iff

theorem lattice_matroid_coordinates (hι : IsIntegralLattice ι)
    (b : Module.Basis (Fin n) ℤ N) (U : E → N) :
    VectorMatroid.ofFamily (K := ℝ) (fun j => embed (latticeEquiv b (U j))) =
      VectorMatroid.ofFamily (K := ℝ) (fun j => ι (U j)) := by
  have he : (fun j => embed (latticeEquiv b (U j))) =
      realEquiv hι b ∘ (fun j => ι (U j)) :=
    funext (fun j => (coordinates_commute hι b (U j)).symm)
  rw [he]
  exact matroid_linearEquiv (realEquiv hι b) (fun j => ι (U j))

end RealCoordinates

#print axioms originalQuotientCongr
#print axioms coordinatePortQuotientEquiv_output
#print axioms latticeSumConclusion_of_coordinates
#print axioms lattice_span_coordinates_iff
#print axioms lattice_matroid_coordinates

end Unimodular.SignedSums

#check Unimodular.SignedSums.latticeSumConclusion_of_coordinates
