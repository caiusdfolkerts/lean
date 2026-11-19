/- The ordinary binary-sum rule for the actual quotient columns, with all
coordinate changes proved to be integral lattice isomorphisms. -/
module
public import Recovery.Unimodular.PriorExtensions.SignedSumsMain
public import Recovery.Unimodular.PriorExtensions.SignedSumsMatroid
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Unimodular.SignedSums

/-- An actual linear equivalence changes none of the represented independent sets. -/
theorem matroid_linearEquiv {K E M N : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (e : M ≃ₗ[K] N) (U : E → M) :
    VectorMatroid.ofFamily (K := K) (e ∘ U) = VectorMatroid.ofFamily (K := K) U := by
  apply Matroid.ext_indep (by simp)
  intro S hS
  rw [VectorMatroid.ofFamily_indep, VectorMatroid.ofFamily_indep]
  exact e.toLinearMap.linearIndepOn_iff_of_injOn e.injective.injOn

def sideCast {P A L : Type*} (U : Matrix (P ⊕ A) L ℤ) :
    L → (P → Binary.F) × (A → Binary.F) :=
  fun l => (fun p => (U (.inl p) l : Binary.F), fun a => (U (.inr a) l : Binary.F))

def packThree (P A B K : Type*) [Semiring K] :
    (P ⊕ (A ⊕ B) → K) ≃ₗ[K] (P → K) × ((A → K) × (B → K)) :=
  (LinearEquiv.sumArrowLequivProdArrow P (A ⊕ B) K K).trans
    ((LinearEquiv.refl K (P → K)).prodCongr (LinearEquiv.sumArrowLequivProdArrow A B K K))

theorem joined_binary_matroid {P A B L R : Type*}
    (U : Matrix (P ⊕ A) L ℤ) (V : Matrix (P ⊕ B) R ℤ) :
    VectorMatroid.ofFamily (K := Binary.F) (fun j i => (joined U V i j : Binary.F)) =
      VectorMatroid.ofFamily (K := Binary.F)
        (joinedFamily (R := Binary.F) (sideCast U) (sideCast V)) := by
  let e := packThree P A B Binary.F
  have he : e ∘ (fun j i => (joined U V i j : Binary.F)) =
      joinedFamily (R := Binary.F) (sideCast U) (sideCast V) := by
    funext j
    cases j <;> ext i <;>
      simp [e, packThree, joinedFamily, sumLeft, sumRight, joined, sideCast]
  have h := matroid_linearEquiv e (fun j i => (joined U V i j : Binary.F))
  rw [he] at h
  exact h.symm

/-- The ordinary real matroid of the glued integer matrix is the unique
binary port sum of its two actual normalized input representations. -/
theorem joined_real_matroid_isPortSum {P A B T L R : Type*}
    [Fintype P] [Fintype A] [Fintype B] [Fintype T] [Fintype L] [Fintype R]
    (C : Matrix P T ℤ)
    (hC : Submodule.span Binary.F (Set.range (fun t p => (C p t : Binary.F))) = ⊤)
    (U : Matrix (P ⊕ A) L ℤ) (V : Matrix (P ⊕ B) R ℤ)
    (ht : (joined U V).IsTotallyUnimodular) :
    Binary.IsPortSum
      (VectorMatroid.ofFamily (K := ℝ) (fun j i => (joined U V i j : ℝ)))
      (fun t p => (C p t : Binary.F)) (sideCast U) (sideCast V) := by
  rw [tu_matroid_field_invariant (F := Binary.F) (joined U V) ht, joined_binary_matroid]
  exact Binary.joined_matroid_isPortSum _ hC _ _

def tripleCoordinates {P A B M E : Type*} [AddCommGroup M] [Module ℤ M]
    (e : M ≃ₗ[ℤ] (P → ℤ) × ((A → ℤ) × (B → ℤ))) (U : E → M) :
    Matrix (P ⊕ (A ⊕ B)) E ℤ :=
  fun i j => Sum.elim (e (U j)).1 (Sum.elim (e (U j)).2.1 (e (U j)).2.2) i

/-- The witnesses record integral coordinates of the original side columns,
an integral isomorphism from the literal quotient, and the ordinary matroid
sum rule for the actual surviving quotient columns. `Binary.F` is exactly ZMod 2. -/
def MatroidConclusion {n₁ n₂ r : ℕ} {T L R : Type*}
    [Fintype T] [Fintype L] [Fintype R]
    (C : Matrix (Fin r) T ℤ) (τ : Fin r → T)
    (U : T ⊕ L → Lattice n₁) (V : T ⊕ R → Lattice n₂) : Prop :=
  ∃ (N₁ : PortNormalization U (fun i => Sum.inl (τ i)))
    (N₂ : PortNormalization V (fun i => Sum.inl (τ i)))
    (eQ : PortQuotient τ U V ≃ₗ[ℤ]
      (Fin r → ℤ) × ((N₁.Complement → ℤ) × (N₂.Complement → ℤ))),
    (∀ j, eQ (PortOutput τ U V j) =
      joinedFamily (R := ℤ) (N₁.equiv ∘ U ∘ Sum.inr) (N₂.equiv ∘ V ∘ Sum.inr) j) ∧
    Binary.IsPortSum
      (VectorMatroid.ofFamily (K := ℝ)
        (fun j i => (tripleCoordinates eQ (PortOutput τ U V) i j : ℝ)))
      (fun t p => (C p t : Binary.F))
      (sideCast (productCoordinates N₁.equiv (U ∘ Sum.inr)))
      (sideCast (productCoordinates N₂.equiv (V ∘ Sum.inr)))

/-- The matroid clause of Proposition 2.2 is established directly for the
literal quotient, retaining every surviving label including parallel labels.
No TU hypothesis occurs: all such bounds are derived from Uniform. -/
theorem signed_port_sum_matroid {n₁ n₂ r : ℕ} {T L R : Type*}
    [Fintype T] [Fintype L] [Fintype R]
    (C : Matrix (Fin r) T ℤ) (hC : PortCompatible C L R)
    (hCspan : Submodule.span Binary.F (Set.range (fun t p => (C p t : Binary.F))) = ⊤)
    (τ : Fin r → T)
    (U : T ⊕ L → Lattice n₁) (V : T ⊕ R → Lattice n₂)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n₁)) U)
    (hV : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n₂)) V)
    (hspanU : Submodule.span ℝ (Set.range (fun l => embed (U (.inr l)))) = ⊤)
    (hspanV : Submodule.span ℝ (Set.range (fun l => embed (V (.inr l)))) = ⊤)
    (haU : LinearIndependent ℝ (fun i => embed (U (.inl (τ i)))))
    (haV : LinearIndependent ℝ (fun i => embed (V (.inl (τ i)))))
    (hportU : ∀ t, U (.inl t) = portMap (fun i => U (.inl (τ i))) (fun i => C i t))
    (hportV : ∀ t, V (.inl t) = portMap (fun i => V (.inl (τ i))) (fun i => C i t)) :
    MatroidConclusion C τ U V := by
  classical
  have hsU : Submodule.span ℝ (Set.range (fun e => embed (U e))) = ⊤ := by
    apply top_unique
    rw [← hspanU]
    apply Submodule.span_mono
    rintro _ ⟨l, rfl⟩
    exact ⟨Sum.inr l, rfl⟩
  have hsV : Submodule.span ℝ (Set.range (fun e => embed (V e))) = ⊤ := by
    apply top_unique
    rw [← hspanV]
    apply Submodule.span_mono
    rintro _ ⟨l, rfl⟩
    exact ⟨Sum.inr l, rfl⟩
  obtain ⟨N₁⟩ := exists_portNormalization U hU hsU (fun i => Sum.inl (τ i)) haU
  obtain ⟨N₂⟩ := exists_portNormalization V hV hsV (fun i => Sum.inl (τ i)) haV
  let a₁ := portMap (fun i => U (.inl (τ i)))
  let a₂ := portMap (fun i => V (.inl (τ i)))
  have he₁ (p : Fin r → ℤ) : N₁.equiv (a₁ p) = (p, 0) := normalized_portMap U _ N₁ p
  have he₂ (p : Fin r → ℤ) : N₂.equiv (a₂ p) = (p, 0) := normalized_portMap V _ N₂ p
  let eQ : PortQuotient τ U V ≃ₗ[ℤ]
      (Fin r → ℤ) × ((N₁.Complement → ℤ) × (N₂.Complement → ℤ)) :=
    originalQuotientEquiv a₁ a₂ N₁.equiv N₂.equiv he₁ he₂
  have hq (x : Lattice n₁ × Lattice n₂) : eQ (Submodule.Quotient.mk x) =
      ((N₁.equiv x.1).1 + (N₂.equiv x.2).1,
        ((N₁.equiv x.1).2, (N₂.equiv x.2).2)) := by
    change originalQuotientEquiv a₁ a₂ N₁.equiv N₂.equiv he₁ he₂
      (Submodule.Quotient.mk x) = _
    rw [originalQuotientEquiv_mk]
    rfl
  let U' := productCoordinates N₁.equiv (U ∘ Sum.inr)
  let V' := productCoordinates N₂.equiv (V ∘ Sum.inr)
  have hU' : (augment C U').IsTotallyUnimodular := by
    convert N₁.totallyUnimodular using 1
    ext i j
    cases j with
    | inr l => rfl
    | inl t =>
        have ht : N₁.equiv (U (.inl t)) = (fun i => C i t, 0) := by rw [hportU]; exact he₁ _
        cases i <;> simp [augment, productCoordinates, ht]
  have hV' : (augment C V').IsTotallyUnimodular := by
    convert N₂.totallyUnimodular using 1
    ext i j
    cases j with
    | inr l => rfl
    | inl t =>
        have ht : N₂.equiv (V (.inl t)) = (fun i => C i t, 0) := by rw [hportV]; exact he₂ _
        cases i <;> simp [augment, productCoordinates, ht]
  have hout (j : L ⊕ R) : eQ (PortOutput τ U V j) =
      joinedFamily (R := ℤ) (N₁.equiv ∘ U ∘ Sum.inr) (N₂.equiv ∘ V ∘ Sum.inr) j := by
    cases j <;> simp [PortOutput, originalFamily, hq, joinedFamily, sumLeft, sumRight]
  refine ⟨N₁, N₂, eQ, hout, ?_⟩
  have hm : tripleCoordinates eQ (PortOutput τ U V) = joined U' V' := by
    ext i j
    simp only [tripleCoordinates, hout]
    cases i with
    | inl p => cases j <;> rfl
    | inr q => cases q <;> cases j <;> rfl
  rw [hm]
  exact joined_real_matroid_isPortSum C hCspan U' V'
    (joined_totallyUnimodular C hC U' V' hU' hV')

end Unimodular.SignedSums
#print axioms Unimodular.SignedSums.joined_real_matroid_isPortSum
#print axioms Unimodular.SignedSums.signed_port_sum_matroid
