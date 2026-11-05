module

public import sunlet.contact_development

/-!
# Direct generic two-summand geometry

This module assembles the checked differential and chord calculations for
the literal ratio map. The sparse witness is explicit supporting data;
the main Latin application must construct it for every allowed order.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix

namespace Sunlet.ToricPairAlgebra

open NormalizedVariations ToricDifferential

variable {k ι Ω : Type*} [Field k] [CharZero k]
  [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]

/-- A proved sparse specialization, retaining the actual Hessian assertion. -/
structure SparseWitness (o : Ω) (π : ι → Equiv.Perm Ω) where
  A : Finset ι
  B : Finset ι
  disjoint : Disjoint (A : Set ι) (B : Set ι)
  Atwo : ∃ a ∈ A, ∃ b ∈ A, π a ≠ π b
  Btwo : ∃ a ∈ B, ∃ b ∈ B, π a ≠ π b
  Atrans : TransitiveFamily π (A : Set ι)
  Btrans : TransitiveFamily π (B : Set ι)
  radial : ∀ v : ToricDifferential.Variation k ι Ω, v.2 o = 0 →
    (∀ w, hessian π (sparseCoefficients (A : Set ι)) (fun _ => 1) v w ∈
      Contact.tangentSpan π o (A : Set ι) (B : Set ι)) →
    ∃ lam : k, v = lam • (sparseCoefficients (A : Set ι), (0 : Ω → k))

variable {F : Type*} [Field F] [CharZero F] [Algebra k F]

def toricPoint (π : ι → Equiv.Perm Ω) (U : ι → F) (h : Ω → Fˣ) : ι × Ω → F :=
  fun ax => coordinate π U (fun x => (h x).val) ax.1 ax.2

def componentDifferential (o : Ω) (π : ι → Equiv.Perm Ω)
    (U : Bool → ι → F) (h : Bool → Ω → Fˣ) (b : Bool) :
    (NormalizedVariations.Index ι Ω o → F) →ₗ[F] (ι × Ω → F) :=
  (differential π (U b) (fun x => (h b x).val)).comp (asVariation o)

@[simp] theorem componentDifferential_apply (o : Ω) (π : ι → Equiv.Perm Ω)
    (U : Bool → ι → F) (h : Bool → Ω → Fˣ) (b : Bool)
    (v : NormalizedVariations.Index ι Ω o → F) :
    componentDifferential o π U h b v =
      differential π (U b) (fun x => (h b x).val) (asVariation o v) := rfl

theorem componentDifferential_radial (o : Ω) (π : ι → Equiv.Perm Ω)
    (U : Bool → ι → F) (h : Bool → Ω → Fˣ) (b : Bool) :
    componentDifferential o π U h b (Sum.elim (U b) (fun _ => 0)) =
      toricPoint π (U b) (h b) := by
  have hv : asVariation o (Sum.elim (U b) (fun _ => (0 : F))) =
      (U b, (0 : Ω → F)) := by
    apply Prod.ext
    · rfl
    · funext x
      by_cases hx : x = o <;> simp [asVariation, hx]
  rw [componentDifferential_apply, hv]
  funext ax
  rcases ax with ⟨a, x⟩
  simp [differential_apply, toricPoint, coordinate, mul_comm]

def joinVariations (o : Ω)
    (v : (NormalizedVariations.Index ι Ω o → F) ×
      (NormalizedVariations.Index ι Ω o → F)) : Index (ι := ι) o → F :=
  fun bj => if bj.1 then v.2 bj.2 else v.1 bj.2

theorem fieldPairDifferential_join (o : Ω) (π : ι → Equiv.Perm Ω)
    (U : Bool → ι → F) (h : Bool → Ω → Fˣ)
    (v : (NormalizedVariations.Index ι Ω o → F) ×
      (NormalizedVariations.Index ι Ω o → F)) :
    fieldPairDifferential o π U h (joinVariations o v) =
      (componentDifferential o π U h false).coprod
        (componentDifferential o π U h true) v := rfl

theorem component_coprod_injective (o : Ω) (π : ι → Equiv.Perm Ω)
    (U : Bool → ι → F) (h : Bool → Ω → Fˣ)
    (hinj : Function.Injective (fieldPairDifferential o π U h)) :
    Function.Injective ((componentDifferential o π U h false).coprod
      (componentDifferential o π U h true)) := by
  intro v w he
  have hj : joinVariations o v = joinVariations o w := hinj (by
    rwa [fieldPairDifferential_join, fieldPairDifferential_join])
  apply Prod.ext
  · funext j
    exact congrFun hj (false, j)
  · funext j
    exact congrFun hj (true, j)

theorem faithfulPairDifferential_injective (o : Ω) (π : ι → Equiv.Perm Ω)
    (W : SparseWitness (k := k) o π) (hmoves : ∀ a, π a o ≠ o)
    (U : Bool → ι → F) (h : Bool → Ω → Fˣ) (hbase : ∀ b, h b o = 1)
    (hfaithful : Function.Injective (evaluate (k := k) o U h)) :
    Function.Injective (fieldPairDifferential o π U h) := by
  have hs : Function.Injective
      ((tangentEntry (k := k) o π).map
        (evaluate (k := k) (F := k) o (sparseCoefficient (k := k) W.A W.B)
          (sparseTorus (k := k) o))).mulVecLin := by
    rw [evaluate_tangentEntry o π _ _ (sparseTorus_base (k := k) o),
      sparse_fieldPairDifferential]
    intro v w hvw
    apply sparsePair_injective π o W.A W.B W.disjoint hmoves W.Atwo W.Btwo W.Atrans W.Btrans
    simpa only [Matrix.mulVecLin_apply, LinearMap.toMatrix'_mulVec] using hvw
  have hg := MatrixSpecialization.injective_of_specialization (tangentEntry (k := k) o π)
    (evaluate (k := k) (F := k) o (sparseCoefficient (k := k) W.A W.B)
      (sparseTorus (k := k) o)) (evaluate o U h).toRingHom hfaithful hs
  intro v w hvw
  apply hg
  change ((tangentEntry (k := k) o π).map (evaluate o U h)) *ᵥ v =
    ((tangentEntry (k := k) o π).map (evaluate o U h)) *ᵥ w
  rw [evaluate_tangentEntry o π U h hbase,
    LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
  exact hvw

theorem toricPoints_independent (o : Ω) (π : ι → Equiv.Perm Ω)
    (U : Bool → ι → F) (h : Bool → Ω → Fˣ)
    (hinj : Function.Injective (fieldPairDifferential o π U h))
    (a : ι) (hU : ∀ b, U b a ≠ 0) :
    ∀ r s : F, r • toricPoint π (U false) (h false) +
      s • toricPoint π (U true) (h true) = 0 → r = 0 ∧ s = 0 := by
  intro r s he
  have hi := component_coprod_injective o π U h hinj
  have hv : (r • Sum.elim (U false) (fun _ : {x : Ω // x ≠ o} => (0 : F)),
      s • Sum.elim (U true) (fun _ : {x : Ω // x ≠ o} => (0 : F))) = (0, 0) := by
    apply hi
    simpa only [LinearMap.coprod_apply, map_smul, componentDifferential_radial,
      map_zero, add_zero] using he
  have hr := congrArg (fun v => v.1 (Sum.inl a)) hv
  have hs := congrArg (fun v => v.2 (Sum.inl a)) hv
  change r * U false a = 0 at hr
  change s * U true a = 0 at hs
  exact ⟨(mul_eq_zero.mp hr).resolve_right (hU false),
    (mul_eq_zero.mp hs).resolve_right (hU true)⟩

theorem derivative_toricPoint_mem (o : Ω) (π : ι → Equiv.Perm Ω)
    (D : Derivation k F F) (U : Bool → ι → F) (h : Bool → Ω → Fˣ)
    (hbase : ∀ b, h b o = 1) (b : Bool) :
    DerivativeChords.vectorDerivative D (toricPoint π (U b) (h b)) ∈
      LinearMap.range (componentDifferential o π U h b) := by
  refine ⟨coordinates o (logarithmicVelocity D (U b) (fun x => (h b x).val)), ?_⟩
  rw [componentDifferential_apply, normalized_logVelocity o D (U b) (h b) (hbase b)]
  funext ax
  exact (derivation_coordinate D π (U b) (fun x => (h b x).val)
    (fun x => Units.ne_zero (h b x)) ax.1 ax.2).symm

theorem derivative_sum_mem (o : Ω) (π : ι → Equiv.Perm Ω)
    (D : Derivation k F F) (U : Bool → ι → F) (h : Bool → Ω → Fˣ)
    (hbase : ∀ b, h b o = 1) :
    DerivativeChords.vectorDerivative D
      (toricPoint π (U false) (h false) + toricPoint π (U true) (h true)) ∈
      LinearMap.range (fieldPairDifferential o π U h) := by
  obtain ⟨v, hv⟩ := derivative_toricPoint_mem o π D U h hbase false
  obtain ⟨w, hw⟩ := derivative_toricPoint_mem o π D U h hbase true
  refine ⟨joinVariations o (v, w), ?_⟩
  rw [fieldPairDifferential_join, LinearMap.coprod_apply, hv, hw]
  funext ax
  exact (map_add D _ _).symm

/-- Equality of actual sums identifies their tangent ranges. The derivations
are supplied by the original independent parameter variables in the application. -/
theorem pair_ranges_eq_of_sum (o : Ω) (π : ι → Equiv.Perm Ω)
    (U V : Bool → ι → F) (h g : Bool → Ω → Fˣ)
    (hgbase : ∀ b, g b o = 1)
    (hinj : Function.Injective (fieldPairDifferential o π U h))
    (D : Bool → NormalizedVariations.Index ι Ω o → Derivation k F F)
    (hD : ∀ b j c, DerivativeChords.vectorDerivative (D b j)
      (toricPoint π (U c) (h c)) =
      if c = b then componentDifferential o π U h c (Pi.single j 1) else 0)
    (hsum : toricPoint π (U false) (h false) + toricPoint π (U true) (h true) =
      toricPoint π (V false) (g false) + toricPoint π (V true) (g true)) :
    LinearMap.range (fieldPairDifferential o π U h) =
      LinearMap.range (fieldPairDifferential o π V g) := by
  have hle : LinearMap.range (fieldPairDifferential o π U h) ≤
      LinearMap.range (fieldPairDifferential o π V g) := by
    have hc : (LinearMap.range (fieldPairDifferential o π V g)).comap
        (fieldPairDifferential o π U h) = ⊤ := by
      apply (Submodule.eq_top_iff_forall_basis_mem (Pi.basisFun F (Index (ι := ι) o))).mpr
      rintro ⟨b, j⟩
      change fieldPairDifferential o π U h ((Pi.basisFun F _) (b, j)) ∈
        LinearMap.range (fieldPairDifferential o π V g)
      rw [Pi.basisFun_apply, fieldPairDifferential_single]
      change componentDifferential o π U h b (Pi.single j 1) ∈
        LinearMap.range (fieldPairDifferential o π V g)
      have he : DerivativeChords.vectorDerivative (D b j)
          (toricPoint π (U false) (h false) + toricPoint π (U true) (h true)) =
          componentDifferential o π U h b (Pi.single j 1) := by
        have hadd : DerivativeChords.vectorDerivative (D b j)
            (toricPoint π (U false) (h false) + toricPoint π (U true) (h true)) =
            DerivativeChords.vectorDerivative (D b j) (toricPoint π (U false) (h false)) +
            DerivativeChords.vectorDerivative (D b j) (toricPoint π (U true) (h true)) := by
          funext ax
          exact map_add (D b j) _ _
        rw [hadd, hD, hD]
        cases b <;> simp
      rw [← he, hsum]
      exact derivative_sum_mem o π (D b j) V g hgbase
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ (LinearMap.range (fieldPairDifferential o π V g)).comap
        (fieldPairDifferential o π U h) := by rw [hc]; trivial
    exact hv
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [LinearMap.finrank_range_of_inj hinj]
  exact (fieldPairDifferential o π V g).finrank_range_le

theorem euler_toricPoint (π : ι → Equiv.Perm Ω) (D : Derivation k F F)
    (U : Bool → ι → F) (h : Bool → Ω → Fˣ)
    (hU : ∀ b a, D (U b a) = if b then 0 else U b a)
    (hh : ∀ b x, D (h b x).val = 0) (b : Bool) :
    DerivativeChords.vectorDerivative D (toricPoint π (U b) (h b)) =
      if b then 0 else toricPoint π (U b) (h b) := by
  funext ax
  simp only [DerivativeChords.vectorDerivative, toricPoint, coordinate, ratio,
    D.leibniz, D.leibniz_div, hU, hh, smul_eq_mul, zero_mul, sub_self,
    zero_div, mul_zero, add_zero]
  cases b <;> simp [toricPoint, coordinate, ratio, mul_comm]

/-- The actual pair is unordered-identifiable once the sparse calculation
and the genuine original coordinate derivations have been supplied. -/
theorem unordered_of_actual_derivations (o : Ω) (π : ι → Equiv.Perm Ω)
    (W : SparseWitness (k := k) o π) (hmoves : ∀ a, π a o ≠ o)
    (U V : Bool → ι → F) (h g : Bool → Ω → Fˣ)
    (hbase : ∀ b, h b o = 1) (hgbase : ∀ b, g b o = 1)
    (hfaithful : Function.Injective (evaluate (k := k) o U h))
    (hgfaithful : Function.Injective (evaluate (k := k) o V g))
    (hUne : ∀ b a, U b a ≠ 0)
    (hdim : 2 < Fintype.card (NormalizedVariations.Index ι Ω o))
    (D : Bool → NormalizedVariations.Index ι Ω o → Derivation k F F)
    (hD : ∀ b j c, DerivativeChords.vectorDerivative (D b j)
      (toricPoint π (U c) (h c)) =
      if c = b then componentDifferential o π U h c (Pi.single j 1) else 0)
    (E : Derivation k F F)
    (hEU : ∀ b a, E (U b a) = if b then 0 else U b a)
    (hEh : ∀ b x, E (h b x).val = 0)
    (hsum : toricPoint π (U false) (h false) + toricPoint π (U true) (h true) =
      toricPoint π (V false) (g false) + toricPoint π (V true) (g true)) :
    (toricPoint π (V false) (g false) = toricPoint π (U false) (h false) ∧
      toricPoint π (V true) (g true) = toricPoint π (U true) (h true)) ∨
    (toricPoint π (V false) (g false) = toricPoint π (U true) (h true) ∧
      toricPoint π (V true) (g true) = toricPoint π (U false) (h false)) := by
  obtain ⟨a₀, ha₀, _⟩ := W.Atwo
  have hinj := faithfulPairDifferential_injective o π W hmoves U h hbase hfaithful
  have hind := toricPoints_independent o π U h hinj a₀ (fun b => hUne b a₀)
  have hrange := pair_ranges_eq_of_sum o π U V h g hgbase hinj D hD hsum
  have hstable : ∀ z ∈ LinearMap.range (fieldPairDifferential o π V g),
      DerivativeChords.vectorDerivative E z ∈ LinearMap.range (fieldPairDifferential o π V g) := by
    intro z hz
    rw [← hrange] at hz ⊢
    exact euler_tangent_range o π E U h hEU hEh z hz
  have hr : ∀ b, ∃ lam : F, DerivativeChords.vectorDerivative E
      (toricPoint π (V b) (g b)) = lam • toricPoint π (V b) (g b) := by
    intro b
    exact radial_derivative_of_stable_pair o π E V g hgbase hgfaithful
      W.A W.B a₀ ha₀ W.disjoint hmoves W.Atwo W.Btwo W.Atrans W.Btrans W.radial hstable b
  obtain ⟨a, ha⟩ := hr false
  obtain ⟨b, hb⟩ := hr true
  obtain ⟨_, hx, hy⟩ := DerivativeChords.same_chord_of_radial_derivatives E
    _ _ _ _ a b hind hsum (euler_toricPoint π E U h hEU hEh false)
    (euler_toricPoint π E U h hEU hEh true) ha hb
  have hpair := component_coprod_injective o π U h hinj
  have hmixed : ∀ (c : Bool) (r s : F), toricPoint π (V c) (g c) =
      r • toricPoint π (U false) (h false) + s • toricPoint π (U true) (h true) →
      r = 0 ∨ s = 0 := by
    intro c r s hc
    apply DerivativeChords.no_mixed_chord _ _ _ r s hc
      (componentDifferential o π U h false) (componentDifferential o π U h true)
      (componentDifferential o π V g c) (D false) (D true) hdim hpair
    · intro j; simpa using hD false j false
    · intro j; simpa using hD false j true
    · intro j; simpa using hD true j false
    · intro j; simpa using hD true j true
    · intro j; exact derivative_toricPoint_mem o π (D false j) V g hgbase c
    · intro j; exact derivative_toricPoint_mem o π (D true j) V g hgbase c
  exact DerivativeChords.unordered_eq_of_unmixed_chords _ _ _ _ _ _ _ _ hind hsum
    hx hy (hmixed false _ _ hx) (hmixed true _ _ hy)

end Sunlet.ToricPairAlgebra
