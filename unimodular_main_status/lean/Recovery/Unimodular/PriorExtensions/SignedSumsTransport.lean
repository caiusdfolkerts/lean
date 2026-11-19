/- Transport the coordinate gluing back to the literal quotient of the two
original lattices. Every equivalence and output column is explicit. -/
module
public import Recovery.Unimodular.PriorExtensions.SignedSumsQuotient
public import Recovery.Unimodular.PriorExtensions.SignedSumsNormalization
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Unimodular.SignedSums

section GeneralModules
variable {R P A B N₁ N₂ : Type*} [CommRing R]
  [AddCommGroup P] [Module R P] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup N₁] [Module R N₁]
  [AddCommGroup N₂] [Module R N₂]

def originalRelation (a₁ : P →ₗ[R] N₁) (a₂ : P →ₗ[R] N₂) : P →ₗ[R] N₁ × N₂ :=
  a₁.prod (-a₂)

abbrev OriginalQuotient (a₁ : P →ₗ[R] N₁) (a₂ : P →ₗ[R] N₂) :=
  (N₁ × N₂) ⧸ LinearMap.range (originalRelation a₁ a₂)

def originalAmalgamation (e₁ : N₁ ≃ₗ[R] P × A) (e₂ : N₂ ≃ₗ[R] P × B) :
    N₁ × N₂ →ₗ[R] P × (A × B) :=
  amalgamation.comp (e₁.prodCongr e₂).toLinearMap

theorem normalized_originalRelation (a₁ : P →ₗ[R] N₁) (a₂ : P →ₗ[R] N₂)
    (e₁ : N₁ ≃ₗ[R] P × A) (e₂ : N₂ ≃ₗ[R] P × B)
    (h₁ : ∀ p, e₁ (a₁ p) = (p, 0)) (h₂ : ∀ p, e₂ (a₂ p) = (p, 0)) (p : P) :
    e₁.prodCongr e₂ (originalRelation a₁ a₂ p) = portRelation (R := R) p := by
  simp [originalRelation, portRelation, h₁, h₂]

theorem ker_originalAmalgamation (a₁ : P →ₗ[R] N₁) (a₂ : P →ₗ[R] N₂)
    (e₁ : N₁ ≃ₗ[R] P × A) (e₂ : N₂ ≃ₗ[R] P × B)
    (h₁ : ∀ p, e₁ (a₁ p) = (p, 0)) (h₂ : ∀ p, e₂ (a₂ p) = (p, 0)) :
    LinearMap.ker (originalAmalgamation e₁ e₂) =
      LinearMap.range (originalRelation a₁ a₂) := by
  ext x
  change amalgamation (R := R) (e₁.prodCongr e₂ x) = 0 ↔ ∃ p, originalRelation a₁ a₂ p = x
  have hn : amalgamation (R := R) (e₁.prodCongr e₂ x) = 0 ↔
      ∃ p, portRelation (R := R) p = e₁.prodCongr e₂ x := by
    change e₁.prodCongr e₂ x ∈ LinearMap.ker
      (amalgamation (R := R) (P := P) (A := A) (B := B)) ↔ _
    rw [ker_amalgamation]
    rfl
  rw [hn]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, (e₁.prodCongr e₂).injective ?_⟩
    rw [normalized_originalRelation a₁ a₂ e₁ e₂ h₁ h₂]
    exact hp
  · rintro ⟨p, rfl⟩
    exact ⟨p, (normalized_originalRelation a₁ a₂ e₁ e₂ h₁ h₂ p).symm⟩

def originalQuotientEquiv (a₁ : P →ₗ[R] N₁) (a₂ : P →ₗ[R] N₂)
    (e₁ : N₁ ≃ₗ[R] P × A) (e₂ : N₂ ≃ₗ[R] P × B)
    (h₁ : ∀ p, e₁ (a₁ p) = (p, 0)) (h₂ : ∀ p, e₂ (a₂ p) = (p, 0)) :
    OriginalQuotient a₁ a₂ ≃ₗ[R] P × (A × B) := by
  let f : N₁ × N₂ →ₗ[R] P × (A × B) := originalAmalgamation e₁ e₂
  have hf : Function.Surjective f :=
    (amalgamation_surjective (R := R) (P := P) (A := A) (B := B)).comp
      (e₁.prodCongr e₂).surjective
  let h : LinearMap.ker f = LinearMap.range (originalRelation a₁ a₂) :=
    ker_originalAmalgamation a₁ a₂ e₁ e₂ h₁ h₂
  exact (Submodule.quotEquivOfEq _ _ h.symm).trans (f.quotKerEquivOfSurjective hf)

@[simp] theorem originalQuotientEquiv_mk (a₁ : P →ₗ[R] N₁) (a₂ : P →ₗ[R] N₂)
    (e₁ : N₁ ≃ₗ[R] P × A) (e₂ : N₂ ≃ₗ[R] P × B)
    (h₁ : ∀ p, e₁ (a₁ p) = (p, 0)) (h₂ : ∀ p, e₂ (a₂ p) = (p, 0))
    (x : N₁ × N₂) :
    originalQuotientEquiv a₁ a₂ e₁ e₂ h₁ h₂ (Submodule.Quotient.mk x) =
      originalAmalgamation e₁ e₂ x := by
  simp [originalQuotientEquiv]

def originalFamily {L S : Type*} (a₁ : P →ₗ[R] N₁) (a₂ : P →ₗ[R] N₂)
    (U : L → N₁) (V : S → N₂) : L ⊕ S → OriginalQuotient a₁ a₂ :=
  Sum.elim (fun l => Submodule.Quotient.mk (U l, 0))
    (fun s => Submodule.Quotient.mk (0, V s))

/-- Surviving side columns generate the actual integral quotient. -/
theorem originalFamily_spans {L S : Type*} (a₁ : P →ₗ[R] N₁) (a₂ : P →ₗ[R] N₂)
    (U : L → N₁) (V : S → N₂)
    (hU : Submodule.span R (Set.range U) = ⊤)
    (hV : Submodule.span R (Set.range V) = ⊤) :
    Submodule.span R (Set.range (originalFamily a₁ a₂ U V)) = ⊤ := by
  let K := LinearMap.range (originalRelation a₁ a₂)
  let Q := Submodule.span R (Set.range (originalFamily a₁ a₂ U V))
  let q₁ : N₁ →ₗ[R] OriginalQuotient a₁ a₂ := K.mkQ.comp (LinearMap.inl R N₁ N₂)
  let q₂ : N₂ →ₗ[R] OriginalQuotient a₁ a₂ := K.mkQ.comp (LinearMap.inr R N₁ N₂)
  have hl : Submodule.span R (Set.range U) ≤ Q.comap q₁ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, rfl⟩
    exact Submodule.subset_span ⟨Sum.inl l, rfl⟩
  have hr : Submodule.span R (Set.range V) ≤ Q.comap q₂ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    exact Submodule.subset_span ⟨Sum.inr s, rfl⟩
  rw [hU] at hl
  rw [hV] at hr
  apply top_unique
  intro z _
  obtain ⟨⟨x, y⟩, rfl⟩ := K.mkQ_surjective z
  have hx : q₁ x ∈ Q := hl (by trivial)
  have hy : q₂ y ∈ Q := hr (by trivial)
  have he : q₁ x + q₂ y = K.mkQ (x, y) := by
    change K.mkQ (x, 0) + K.mkQ (0, y) = K.mkQ (x, y)
    rw [← map_add]
    simp
  exact he ▸ Q.add_mem hx hy

end GeneralModules

/-- Total unimodularity of genuine basis coordinates implies exactly the
paper's full determinant condition. -/
theorem uniform_of_coordinate_tu {I E M : Type*} [Fintype I] [DecidableEq I]
    [AddCommGroup M] [Module ℤ M] (b : Module.Basis I ℤ M) (U : E → M)
    (hU : Matrix.IsTotallyUnimodular (fun i j => b.repr (U j) i)) :
    IntegralRigidity.Uniform b U := by
  intro a
  obtain ⟨s, hs⟩ := (Matrix.isTotallyUnimodular_iff_fintype _).mp hU I id a
  have he : b.det (U ∘ a) =
      (Matrix.submatrix (fun i j => b.repr (U j) i) id a).det := by
    rw [Module.Basis.det_apply]
    rfl
  rw [he, ← hs]
  cases s <;> simp

end Unimodular.SignedSums
#print axioms Unimodular.SignedSums.originalQuotientEquiv
#print axioms Unimodular.SignedSums.originalFamily_spans
#print axioms Unimodular.SignedSums.uniform_of_coordinate_tu
