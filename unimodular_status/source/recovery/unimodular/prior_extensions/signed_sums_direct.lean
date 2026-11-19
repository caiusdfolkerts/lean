/- The zero-port quotient is the literal direct lattice sum. -/
module
public import Recovery.Unimodular.PriorExtensions.SignedSumsProposition
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Unimodular.SignedSums

def withEmptyPort (K M : Type*) [CommRing K] [AddCommGroup M] [Module K M] :
    M ≃ₗ[K] (Fin 0 → K) × M where
  toFun x := (0, x)
  invFun x := x.2
  left_inv _ := rfl
  right_inv x := by apply Prod.ext; exact Subsingleton.elim _ _; rfl
  map_add' _ _ := by simp
  map_smul' _ _ := by simp <;> rfl

def directQuotientEquiv {n₁ n₂ : ℕ} {L R : Type*}
    (U : Fin 0 ⊕ L → Lattice n₁) (V : Fin 0 ⊕ R → Lattice n₂) :
    PortQuotient id U V ≃ₗ[ℤ] Lattice n₁ × Lattice n₂ := by
  let a₁ := portMap (fun i : Fin 0 => U (.inl i))
  let a₂ := portMap (fun i : Fin 0 => V (.inl i))
  have h₁ (p : Fin 0 → ℤ) : withEmptyPort ℤ (Lattice n₁) (a₁ p) = (p, 0) := by
    have hp : p = 0 := Subsingleton.elim _ _
    rw [hp, map_zero]
    rfl
  have h₂ (p : Fin 0 → ℤ) : withEmptyPort ℤ (Lattice n₂) (a₂ p) = (p, 0) := by
    have hp : p = 0 := Subsingleton.elim _ _
    rw [hp, map_zero]
    rfl
  exact (originalQuotientEquiv a₁ a₂ (withEmptyPort ℤ (Lattice n₁))
    (withEmptyPort ℤ (Lattice n₂)) h₁ h₂).trans (withEmptyPort ℤ (Lattice n₁ × Lattice n₂)).symm

@[simp] theorem directQuotientEquiv_mk {n₁ n₂ : ℕ} {L R : Type*}
    (U : Fin 0 ⊕ L → Lattice n₁) (V : Fin 0 ⊕ R → Lattice n₂)
    (x : Lattice n₁ × Lattice n₂) :
    directQuotientEquiv U V (Submodule.Quotient.mk x) = x := by
  let a₁ := portMap (fun i : Fin 0 => U (.inl i))
  let a₂ := portMap (fun i : Fin 0 => V (.inl i))
  have h₁ (p : Fin 0 → ℤ) : withEmptyPort ℤ (Lattice n₁) (a₁ p) = (p, 0) := by
    have hp : p = 0 := Subsingleton.elim _ _
    rw [hp, map_zero]
    rfl
  have h₂ (p : Fin 0 → ℤ) : withEmptyPort ℤ (Lattice n₂) (a₂ p) = (p, 0) := by
    have hp : p = 0 := Subsingleton.elim _ _
    rw [hp, map_zero]
    rfl
  have h := originalQuotientEquiv_mk a₁ a₂ (withEmptyPort ℤ (Lattice n₁))
    (withEmptyPort ℤ (Lattice n₂)) h₁ h₂ x
  exact congrArg Prod.snd h

def directFamily {n₁ n₂ : ℕ} {L R : Type*}
    (U : L → Lattice n₁) (V : R → Lattice n₂) : L ⊕ R → Lattice n₁ × Lattice n₂ :=
  Sum.elim (fun l => (U l, 0)) (fun r => (0, V r))

theorem spanning_equiv {M N E : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) (U : E → M)
    (h : Submodule.span ℤ (Set.range U) = ⊤) :
    Submodule.span ℤ (Set.range (e ∘ U)) = ⊤ := by
  let S := Submodule.span ℤ (Set.range (e ∘ U))
  have hs : Submodule.span ℤ (Set.range U) ≤ S.comap e.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  rw [h] at hs
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := e.surjective y
  exact hs (by trivial)

/-- Proposition 2.2, the actual direct 1-sum, not merely an isomorphic
coordinate replacement. All dimensions and label types are unrestricted. -/
theorem proposition_2_2_one_sum {n₁ n₂ : ℕ} {L R : Type*}
    (U : L → Lattice n₁) (V : R → Lattice n₂)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n₁)) U)
    (hV : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n₂)) V)
    (hspanU : Submodule.span ℝ (Set.range (fun l => embed (U l))) = ⊤)
    (hspanV : Submodule.span ℝ (Set.range (fun l => embed (V l))) = ⊤) :
    ∃ b : Module.Basis (Fin (n₁ + n₂)) ℤ (Lattice n₁ × Lattice n₂),
      IntegralRigidity.Uniform b (directFamily U V) ∧
      Submodule.span ℤ (Set.range (directFamily U V)) = ⊤ ∧
      Matrix.IsTotallyUnimodular (fun i j => b.repr (directFamily U V j) i) := by
  classical
  let U₀ : Fin 0 ⊕ L → Lattice n₁ := Sum.elim Fin.elim0 U
  let V₀ : Fin 0 ⊕ R → Lattice n₂ := Sum.elim Fin.elim0 V
  have hU₀ : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n₁)) U₀ := by
    intro f
    have he : U₀ ∘ f = U ∘ (Sum.elim Fin.elim0 id ∘ f) := by
      funext i
      dsimp only [Function.comp_def, U₀]
      cases f i with
      | inl z => exact Fin.elim0 z
      | inr l => rfl
    rw [he]
    exact hU _
  have hV₀ : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n₂)) V₀ := by
    intro f
    have he : V₀ ∘ f = V ∘ (Sum.elim Fin.elim0 id ∘ f) := by
      funext i
      dsimp only [Function.comp_def, V₀]
      cases f i with
      | inl z => exact Fin.elim0 z
      | inr l => rfl
    rw [he]
    exact hV _
  obtain ⟨k, b, hk, hb, hs, ht⟩ :=
    proposition_2_2_zero_port_sum U₀ V₀ hU₀ hV₀ hspanU hspanV
  have hk' : k = n₁+n₂ := by simpa using hk
  subst k
  let e := directQuotientEquiv U₀ V₀
  have he (j : L ⊕ R) : e (PortOutput id U₀ V₀ j) = directFamily U V j := by
    cases j <;> simp [e, PortOutput, originalFamily, directFamily, U₀, V₀]
  let b' := b.map e
  have hc : (fun i j => b'.repr (directFamily U V j) i) =
      (fun i j => b.repr (PortOutput id U₀ V₀ j) i) := by
    funext i j
    change b.repr (e.symm (directFamily U V j)) i = _
    rw [← he j, e.symm_apply_apply]
  have ht' : Matrix.IsTotallyUnimodular (fun i j => b'.repr (directFamily U V j) i) := by
    rw [hc]
    exact ht
  refine ⟨b', uniform_of_coordinate_tu b' _ ht', ?_, ht'⟩
  have htransport := spanning_equiv e (PortOutput id U₀ V₀) hs
  simpa only [Function.comp_def, he] using htransport

end Unimodular.SignedSums
#print axioms Unimodular.SignedSums.directQuotientEquiv
#print axioms Unimodular.SignedSums.proposition_2_2_one_sum
