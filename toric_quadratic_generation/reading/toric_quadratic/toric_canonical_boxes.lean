module

public import PaperVerification.ToricSelectedBoxAssembly
public import PaperVerification.ToricMixedPolytopeBridges

@[expose] public section

/-!
# The complete boxes at the canonical centers

Every full cone uses its actual chosen Cartier basis. The two parity
boxes have radius one. The two adjoint boxes have radius one half, with
the second box contained in the actual topological interior. The only
hypotheses are the original polytopes, their literal edge bounds and the
nonempty-focus branch of the exhaustive obstruction selection.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem canonical_parity_boxes (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n)
    (hne : ∀ i, («Σ».parityFamily P Q i).negative.Nonempty) :
    let Γ := «Σ».selectedFan («Σ».parityFamily P Q) hne
      («Σ».parityFamily_disjoint hpure P Q hP hQ hfanP hfanQ hboundP hboundQ)
    (∀ (s : Γ.fullCones) (t : Fin n → ℝ), (∀ i, |t i| ≤ 1) →
      Γ.cartierPoint («Σ».parityCenter P Q P hne) s +
        ∑ i, t i • Γ.cartierBasis s i ∈ P.carrier) ∧
    (∀ (s : Γ.fullCones) (t : Fin n → ℝ), (∀ i, |t i| ≤ 1) →
      Γ.cartierPoint («Σ».parityCenter P Q Q hne) s +
        ∑ i, t i • Γ.cartierBasis s i ∈ Q.carrier) := by
  let R := «Σ».parityFamily P Q
  have hR : ∀ i, (R i).IsCombinatoriallyContractible :=
    «Σ».parityFamily_contractible P Q
  have hlarge : ∀ i, n < 2 * (R i).fiberDimension :=
    «Σ».parityFamily_large hpure P Q hP hQ hfanP hfanQ hboundP hboundQ
  let hdisj := «Σ».parityFamily_disjoint hpure P Q hP hQ hfanP hfanQ hboundP hboundQ
  have make_box (L : LatticePolytope n) (hL : L.Smooth)
      (hfanL : «Σ».realCones = L.normalFan) (hboundL : L.EdgesAtLeast n)
      (hinactive : ∀ S : «Σ».PrimitiveRelation, S.IsCombinatoriallyContractible →
        (∀ i, S.positive ≠ (R i).positive) →
        2 * (S.fiberDimension : ℝ) ≤ S.degree (fun u => (L.integralSupport u : ℝ)))
      (s : («Σ».selectedFan R hne hdisj).fullCones)
      (t : Fin n → ℝ) (ht : ∀ i, |t i| ≤ 1) :
      («Σ».selectedFan R hne hdisj).cartierPoint («Σ».parityCenter P Q L hne) s +
        ∑ i, t i • («Σ».selectedFan R hne hdisj).cartierBasis s i ∈ L.carrier := by
    change («Σ».selectedFan R hne hdisj).cartierPoint
      («Σ».selectedCenteredSupport R (fun u => (L.integralSupport u : ℝ)) 1
        (fun i => («Σ».parityDisplacements P Q L hne i : ℝ))) s + _ ∈ _
    apply «Σ».selected_centered_box_of_charts R hne hdisj L hfanL 1 1
      (fun i => («Σ».parityDisplacements P Q L hne i : ℝ)) L.carrier ?_ ?_ s t ht
    · intro b hfull hnone v hv hcone «λ» «hλ»
      apply L.outside_side_two_box «Σ» hpure hL hfanL hboundL v hv b hfull hcone
      · intro S hS hbad hsub
        have hno : ∀ i, S.positive ≠ (R i).positive := by
          intro i he
          exact hnone i ((S.negative_unique (R i) he) ▸ hsub)
        exact (not_lt_of_ge (hinactive S hS hno)) hbad
      · intro k
        obtain ⟨hlo, hhi⟩ := abs_le.mp («hλ» k)
        constructor <;> linarith
    · intro i b I hfull hI j hj v hv hcone «λ» «hλ»
      have hb := (R i).parityDisplacement_bounds (hR i) (hne i) (hlarge i)
        hpure L hL hfanL hboundL
      have hq : 1 ≤ (R i).negative.card := Finset.card_pos.mpr (hne i)
      have hqcast : (((R i).negative.card - 1 : ℕ) : ℝ) =
          ((R i).negative.card : ℝ) - 1 := by rw [Nat.cast_sub hq, Nat.cast_one]
      have he : 0 < n := by
        have hd := (R i).contractible_dimension_bound (hR i)
        have hr := (R i).fiberDimension_pos
        omega
      have hbox := «Σ».shifted_box_mem hpure L.integralSupport
        (L.integralSupport_isStrictSupport «Σ» hfanL) he
        (L.supportReconstruction_edgesAtLeast «Σ» hpure hfanL hboundL)
        (R i) (hR i) (hne i) b I hI hfull j hj v
        (L.normal_basis_vertex_active «Σ» v hv b hcone)
        2 ((R i).parityDisplacement (hne i) L.integralSupport : ℝ)
        (by norm_num) (by rw [hqcast]; exact hb.2.1)
        (by change _ + 2 + 2 * (R i).baseDimension ≤ (n : ℝ); linarith [hb.2.2.1])
        hb.2.2.2.2 (fun k => 1 + «λ» k)
        (by intro k; obtain ⟨hlo, hhi⟩ := abs_le.mp («hλ» k); constructor <;> linarith)
      rw [L.fanPolytope_integralSupport_eq «Σ» hfanL] at hbox
      simpa only [parityDisplacements, add_assoc] using hbox
  constructor
  · intro s t ht
    apply make_box P hP hfanP hboundP ?_ s t ht
    intro S hS hn
    exact («Σ».parity_unselected_degree_bounds _ _ S hS hn).1
  · intro s t ht
    apply make_box Q hQ hfanQ hboundQ ?_ s t ht
    intro S hS hn
    exact («Σ».parity_unselected_degree_bounds _ _ S hS hn).2

theorem canonical_adjoint_boxes (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast (n + 1)) (hboundQ : Q.EdgesAtLeast (n + 1))
    (hne : ∀ i, («Σ».adjointFamily Q i).negative.Nonempty) :
    let Γ := «Σ».selectedFan («Σ».adjointFamily Q) hne
      («Σ».adjointFamily_disjoint hpure Q hQ hfanQ hboundQ)
    (∀ (s : Γ.fullCones) (t : Fin n → ℝ), (∀ i, |t i| ≤ 1 / 2) →
      Γ.cartierPoint («Σ».firstAdjointCenter P Q) s +
        ∑ i, t i • Γ.cartierBasis s i ∈ P.carrier) ∧
    (∀ (s : Γ.fullCones) (t : Fin n → ℝ), (∀ i, |t i| ≤ 1 / 2) →
      Γ.cartierPoint («Σ».secondAdjointCenter Q hne) s +
        ∑ i, t i • Γ.cartierBasis s i ∈ interior Q.carrier) := by
  let R := «Σ».adjointFamily Q
  have hR : ∀ i, (R i).IsCombinatoriallyContractible := «Σ».adjointFamily_contractible Q
  let hdisj := «Σ».adjointFamily_disjoint hpure Q hQ hfanQ hboundQ
  constructor
  · intro s t ht
    change («Σ».selectedFan R hne hdisj).cartierPoint
      («Σ».selectedCenteredSupport R (fun u => (P.integralSupport u : ℝ)) (1 / 2)
        (fun i => ((R i).negative.card : ℝ) - 1)) s + _ ∈ _
    apply «Σ».selected_centered_box_of_charts R hne hdisj P hfanP (1 / 2) (1 / 2)
      (fun i => ((R i).negative.card : ℝ) - 1) P.carrier ?_ ?_ s t ht
    · intro b hfull hnone v hv hcone «λ» «hλ»
      apply P.unit_box_of_edge_bound «Σ» hpure hP hfanP hboundP (by omega)
        v hv b hfull hcone (fun k => 1 / 2 + «λ» k)
      intro k
      obtain ⟨hlo, hhi⟩ := abs_le.mp («hλ» k)
      constructor <;> linarith
    · intro i b I hfull hI j hj v hv hcone «λ» «hλ»
      have hq : 1 ≤ (R i).negative.card := Finset.card_pos.mpr (hne i)
      have hqcast : (((R i).negative.card - 1 : ℕ) : ℝ) =
          ((R i).negative.card : ℝ) - 1 := by rw [Nat.cast_sub hq, Nat.cast_one]
      have hdim : (n : ℝ) = (R i).fiberDimension + (R i).negative.card +
          (R i).baseDimension := by exact_mod_cast (R i).dimension_eq (hR i)
      have hdegree := P.contractible_degree_lower_bound hP «Σ» hpure hfanP hboundP (R i) (hR i)
      have hshift0 : (0 : ℝ) ≤ ((R i).negative.card : ℝ) - 1 := by
        have hqR : (1 : ℝ) ≤ (R i).negative.card := by exact_mod_cast hq
        linarith
      have hmul : (0 : ℝ) ≤ (R i).minimumCoefficient (hne i) *
          (((R i).negative.card : ℝ) - 1) := mul_nonneg (Nat.cast_nonneg _) hshift0
      have hr : (R i).fiberDimension ≤ n := by
        have hd := (R i).contractible_dimension_bound (hR i)
        omega
      have hrR : ((R i).fiberDimension : ℝ) ≤ n := by exact_mod_cast hr
      have hbox := «Σ».shifted_box_mem hpure P.integralSupport
        (P.integralSupport_isStrictSupport «Σ» hfanP) (Nat.succ_pos n)
        (P.supportReconstruction_edgesAtLeast «Σ» hpure hfanP hboundP)
        (R i) (hR i) (hne i) b I hI hfull j hj v
        (P.normal_basis_vertex_active «Σ» v hv b hcone)
        1 (((R i).negative.card : ℝ) - 1) zero_le_one
        (by rw [one_mul, hqcast])
        (by change _ + 1 + 1 * (R i).baseDimension ≤ ((n + 1 : ℕ) : ℝ)
            simp only [one_mul, Nat.cast_add, Nat.cast_one]
            have hr0 : (0 : ℝ) ≤ (R i).fiberDimension := Nat.cast_nonneg _
            linarith)
        (by simp only [one_mul, Nat.cast_add, Nat.cast_one] at *; linarith)
        (fun k => 1 / 2 + «λ» k)
        (by intro k; obtain ⟨hlo, hhi⟩ := abs_le.mp («hλ» k); constructor <;> linarith)
      rw [P.fanPolytope_integralSupport_eq «Σ» hfanP] at hbox
      simpa only [add_assoc] using hbox
  · intro s t ht
    change («Σ».selectedFan R hne hdisj).cartierPoint
      («Σ».selectedCenteredSupport R (fun u => (Q.integralSupport u : ℝ)) (3 / 2)
        (fun i => («Σ».adjointDisplacements Q hne i : ℝ))) s + _ ∈ _
    apply «Σ».selected_centered_box_of_charts R hne hdisj Q hfanQ (3 / 2) (1 / 2)
      (fun i => («Σ».adjointDisplacements Q hne i : ℝ)) (interior Q.carrier) ?_ ?_ s t ht
    · intro b hfull hnone v hv hcone «λ» «hλ»
      have hout : ∀ S : «Σ».PrimitiveRelation, S.IsCombinatoriallyContractible →
          0 < 2 * (S.fiberDimension : ℝ) + 1 -
            S.degree (fun u => (Q.integralSupport u : ℝ)) - S.negativeCoefficientSum →
          ¬ S.negative ⊆ Finset.univ.image b := by
        intro S hS hbad hsub
        have hno : ∀ i, S.positive ≠ (R i).positive := by
          intro i he
          exact hnone i ((S.negative_unique (R i) he) ▸ hsub)
        have hbound := «Σ».adjoint_unselected_degree_bound
          (fun u => (Q.integralSupport u : ℝ)) S hS hno
        rw [S.coefficientSum_cast] at hbound
        linarith
      have hbox := Q.outside_inner_unit_box «Σ» hpure hQ hfanQ hboundQ
        v hv b hfull hcone hout (fun k => 1 / 2 + «λ» k)
        (by intro k; obtain ⟨hlo, hhi⟩ := abs_le.mp («hλ» k); constructor <;> linarith)
      have hcoeff (k : Fin n) : (3 / 2 : ℝ) + «λ» k = 1 + (1 / 2 + «λ» k) := by ring
      simpa only [hcoeff, add_smul, one_smul, Finset.sum_add_distrib, add_assoc] using hbox
    · intro i b I hfull hI j hj v hv hcone «λ» «hλ»
      have hb := (R i).adjointDisplacement_bounds (hR i) (hne i)
        hpure Q hQ hfanQ hboundQ («Σ».selectionRelation_test _ i)
      have hq : 1 ≤ (R i).negative.card := Finset.card_pos.mpr (hne i)
      have hqcast : (((R i).negative.card - 1 : ℕ) : ℝ) =
          ((R i).negative.card : ℝ) - 1 := by rw [Nat.cast_sub hq, Nat.cast_one]
      have hbox := «Σ».shifted_inner_unit_box_mem hpure Q.integralSupport
        (Q.integralSupport_isStrictSupport «Σ» hfanQ) (Nat.succ_pos n)
        (Q.supportReconstruction_edgesAtLeast «Σ» hpure hfanQ hboundQ)
        (R i) (hR i) (hne i) b I hI hfull j hj v
        (Q.normal_basis_vertex_active «Σ» v hv b hcone)
        ((R i).adjointDisplacement (hne i) Q.integralSupport : ℝ)
        (by rw [hqcast]; exact hb.2.1)
        (by change _ + 2 + ((2 * (R i).baseDimension + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ)
            simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
            linarith [hb.2.2.1])
        (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hb.2.2.2)
        (fun k => 1 / 2 + «λ» k)
        (by intro k; obtain ⟨hlo, hhi⟩ := abs_le.mp («hλ» k); constructor <;> linarith)
      rw [Q.fanPolytope_integralSupport_eq «Σ» hfanQ] at hbox
      have hcoeff (k : Fin n) : (1 : ℝ) + (1 / 2 + «λ» k) = 3 / 2 + «λ» k := by ring
      simpa only [adjointDisplacements, hcoeff, add_assoc] using hbox

end SmoothCompleteFan

end PaperVerification.ToricGeometry
