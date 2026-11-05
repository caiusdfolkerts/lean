module

public import sunlet.toric_differential

/-! Coordinate vector spaces for the normalized coefficient/torus tangent
variables. Both conversion directions are proved, so choosing a basepoint
does not silently remove any nonconstant tangent direction. -/

@[expose] public section
noncomputable section

namespace Sunlet.NormalizedVariations

variable {ι Ω K : Type*} [Field K] [DecidableEq Ω]

abbrev Index (ι Ω : Type*) (o : Ω) := ι ⊕ {x : Ω // x ≠ o}

def asVariation (o : Ω) : (Index ι Ω o → K) →ₗ[K] ToricDifferential.Variation K ι Ω where
  toFun z := (fun a => z (.inl a), fun x => if h : x = o then 0 else z (.inr ⟨x, h⟩))
  map_add' := by
    intro x y
    apply Prod.ext
    · rfl
    · funext b
      by_cases hb : b = o <;> simp [hb]
  map_smul' := by
    intro r x
    apply Prod.ext
    · rfl
    · funext b
      by_cases hb : b = o <;> simp [hb]

@[simp] theorem asVariation_coefficient (o : Ω) (z : Index ι Ω o → K) (a : ι) :
    (asVariation o z).1 a = z (.inl a) := rfl

@[simp] theorem asVariation_base (o : Ω) (z : Index ι Ω o → K) :
    (asVariation o z).2 o = 0 := by simp [asVariation]

@[simp] theorem asVariation_torus (o : Ω) (z : Index ι Ω o → K) (x : Ω) (hx : x ≠ o) :
    (asVariation o z).2 x = z (.inr ⟨x, hx⟩) := by simp [asVariation, hx]

def coordinates (o : Ω) : ToricDifferential.Variation K ι Ω →ₗ[K] (Index ι Ω o → K) where
  toFun v := Sum.elim v.1 (fun x => v.2 x - v.2 o)
  map_add' := by
    intro x y
    funext j
    cases j <;> simp <;> ring
  map_smul' := by
    intro r x
    funext j
    cases j <;> simp <;> ring

@[simp] theorem coordinates_asVariation (o : Ω) (z : Index ι Ω o → K) :
    coordinates o (asVariation o z) = z := by
  funext j
  cases j with
  | inl a => rfl
  | inr x => simp [coordinates, x.property]

theorem asVariation_coordinates (o : Ω) (v : ToricDifferential.Variation K ι Ω) :
    asVariation o (coordinates o v) = (v.1, fun x => v.2 x - v.2 o) := by
  apply Prod.ext
  · rfl
  · funext x
    by_cases hx : x = o
    · subst x; simp
    · simp [coordinates, hx]

theorem asVariation_injective (o : Ω) : Function.Injective (asVariation (K := K) (ι := ι) o) := by
  intro x y h
  have hh := congrArg (coordinates o) h
  simpa using hh

/-- Every logarithmic test direction is represented, because the omitted
constant torus direction contributes zero to every difference. -/
theorem hessian_coordinates (o : Ω) (π : ι → Equiv.Perm Ω)
    (U : ι → K) (k : Ω → K) (v w : ToricDifferential.Variation K ι Ω) :
    ToricDifferential.hessian π U k v (asVariation o (coordinates o w)) =
      ToricDifferential.hessian π U k v w := by
  rw [asVariation_coordinates]
  funext ab
  simp only [ToricDifferential.hessian]
  ring

variable [Fintype Ω] [DecidableEq ι] [CharZero K]

def component (o : Ω) (b : Bool) :
    (Bool × Index ι Ω o → K) →ₗ[K] (Index ι Ω o → K) where
  toFun z j := z (b, j)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def sparsePair (π : ι → Equiv.Perm Ω) (o : Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] :
    (Bool × Index ι Ω o → K) →ₗ[K] (ι × Ω → K) :=
  (Contact.pairDifferential π o A B).comp
    (((asVariation o).comp (component o false)).prod
      ((asVariation o).comp (component o true)))

@[simp] theorem sparsePair_apply (π : ι → Equiv.Perm Ω) (o : Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (z : Bool × Index ι Ω o → K) :
    sparsePair π o A B z = Contact.pairDifferential π o A B
      (asVariation o (fun j => z (false, j)), asVariation o (fun j => z (true, j))) := rfl

/-- The injective sparse pair theorem in an ordinary finite coordinate vector
space, suitable for the later determinant-specialization argument. -/
theorem sparsePair_injective
    (π : ι → Equiv.Perm Ω) (o : Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (hdis : Disjoint A B) (hmoves : ∀ a, π a o ≠ o)
    (hAtwo : ∃ a ∈ A, ∃ b ∈ A, π a ≠ π b)
    (hBtwo : ∃ a ∈ B, ∃ b ∈ B, π a ≠ π b)
    (hAtrans : TransitiveFamily π A) (hBtrans : TransitiveFamily π B) :
    Function.Injective (sparsePair (K := K) π o A B) := by
  apply (injective_iff_map_eq_zero (sparsePair (K := K) π o A B)).mpr
  intro z hz
  let v := asVariation o (fun j => z (false, j))
  let w := asVariation o (fun j => z (true, j))
  have he : ∀ a x, v.1 a + (if a ∈ A then v.2 x - v.2 (π a x) else 0) +
      TwoRatioRigidity.ratio o (π a) x •
        (w.1 a + if a ∈ B then w.2 x - w.2 (π a x) else 0) = 0 := by
    intro a x
    have hh := congrFun hz (a, x)
    simpa only [sparsePair_apply, Contact.pairDifferential_apply, Algebra.smul_def,
      Pi.zero_apply, v, w] using hh
  obtain ⟨hp, hq, hV, hW⟩ := SparseTangentPair.kernel_eq_zero π o A B hdis hmoves
    hAtwo hBtwo hAtrans hBtrans v.1 w.1 v.2 w.2
    (asVariation_base o _) (asVariation_base o _) he
  funext bj
  rcases bj with ⟨b, j⟩
  cases b <;> cases j with
  | inl a => first | exact hp a | exact hq a
  | inr x => first
      | simpa [v, x.property] using hV x
      | simpa [w, x.property] using hW x

end Sunlet.NormalizedVariations
