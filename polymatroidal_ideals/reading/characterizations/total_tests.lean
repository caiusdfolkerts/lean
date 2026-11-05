import Characterizations.Triangular
import Characterizations.Regularity
import CommAlg.KoszulComplex.DerivedDecomposition

/-! # Total-degree Tor formulations of the homological tests

The total-degree piece is the sum, inside genuine derived Tor, of its actual
multigraded submodules of that total degree.  Vanishing is proved equivalent
both to fine-degree vanishing and to the finite sum of Betti dimensions.
-/

noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid CommAlg.Koszul Finset
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

def totalDegreeTor (B : Family V) (i j : ℕ) :=
  ⨆ (a : Exponent V) (_ : a.degree = j), gradedTor (k := k) B a i

theorem totalDegreeTor_eq_bot_iff (B : Family V) (i j : ℕ) :
    totalDegreeTor (k := k) B i j = ⊥ ↔
      ∀ a : Exponent V, a.degree = j → bettiNumber (k := k) B a i = 0 := by
  simp only [totalDegreeTor,iSup_eq_bot,bettiNumber,Submodule.finrank_eq_zero]

theorem iSup_totalDegreeTor (B : Family V) (i : ℕ) :
    (⨆ j : ℕ, totalDegreeTor (k := k) B i j) = ⊤ := by
  rw [← iSup_gradedTor B i]
  apply le_antisymm
  · apply iSup_le
    intro j
    apply iSup_le
    intro a
    apply iSup_le
    intro _
    exact le_iSup (fun a => gradedTor (k := k) B a i) a
  · apply iSup_le
    intro a
    exact le_iSup_of_le a.degree (le_iSup_of_le a (le_iSup_of_le rfl le_rfl))

theorem totalBettiNumber_eq_zero_iff (B : Family V) (i j : ℕ) :
    Strands.totalBettiNumber (k := k) B i j = 0 ↔
      ∀ a : Exponent V, a.degree = j → bettiNumber (k := k) B a i = 0 := by
  constructor
  · intro hz a ha
    apply Nat.eq_zero_of_not_pos
    intro hp
    have hh := (totalBettiNumber_pos_iff B i j).mpr ⟨a,ha,hp⟩
    omega
  · intro h
    apply Nat.eq_zero_of_not_pos
    intro hp
    obtain ⟨a,ha,hpa⟩ := (totalBettiNumber_pos_iff B i j).mp hp
    have hz := h a ha
    omega

theorem totalBettiNumber_zero_iff_totalDegreeTor (B : Family V) (i j : ℕ) :
    Strands.totalBettiNumber (k := k) B i j = 0 ↔ totalDegreeTor (k := k) B i j = ⊥ :=
  (totalBettiNumber_eq_zero_iff B i j).trans (totalDegreeTor_eq_bot_iff B i j).symm

theorem retainedLinearThrough_iff_totalBetti (B : Family V) (U : Finset V) (e t : ℕ) :
    RetainedLinearThrough (k := k) B U e t ↔
      ∀ i : ℕ, i ≤ t → ∀ j : ℕ, j ≠ e+i →
        Strands.totalBettiNumber (k := k) (localFamily B U) i j = 0 := by
  constructor
  · intro h i hi j hj
    apply (totalBettiNumber_eq_zero_iff _ _ _).mpr
    intro a ha
    exact h a i hi (by rwa [ha])
  · intro h a i hi hoff
    exact (totalBettiNumber_eq_zero_iff _ _ _).mp (h i hi a.degree hoff) a rfl

def RetainedTorLinearThrough (B : Family V) (U : Finset V) (e t : ℕ) : Prop :=
  ∀ i : ℕ, i ≤ t → ∀ j : ℕ, j ≠ e+i →
    totalDegreeTor (k := k) (localFamily B U) i j = ⊥

theorem retainedLinearThrough_iff_totalTor (B : Family V) (U : Finset V) (e t : ℕ) :
    RetainedLinearThrough (k := k) B U e t ↔ RetainedTorLinearThrough (k := k) B U e t := by
  rw [retainedLinearThrough_iff_totalBetti]
  simp only [RetainedTorLinearThrough,totalBettiNumber_zero_iff_totalDegreeTor]

def TotalTriangularTests (B : Family V) (d : ℕ) : Prop :=
  ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-1 →
    ∃ e, Equigenerated (localFamily B U) e ∧
      (0 < e → RetainedTorLinearThrough (k := k) B U e
        (min (e-1) (min (d-1-(Fintype.card V-U.card)) (U.card-1))))

def TotalDegreeBoundedTests (B : Family V) : Prop :=
  ∀ U : Finset V, ∃ e, Equigenerated (localFamily B U) e ∧
    (0 < e → RetainedTorLinearThrough (k := k) B U e (e-1))

def TotalDegreeDimensionBoundedTests (B : Family V) : Prop :=
  ∀ U : Finset V, ∃ e, Equigenerated (localFamily B U) e ∧
    (0 < e → RetainedTorLinearThrough (k := k) B U e (min (e-1) (U.card-1)))

/-- Theorem4.9 as literal vanishing of total-degree submodules of genuine
derived Tor over the retained-variable polynomial rings. -/
theorem polymatroidal_iff_triangular_totalTor {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hd2 : 2 ≤ d) :
    IsPolymatroidal B ↔ TotalTriangularTests (k := k) B d := by
  rw [polymatroidal_iff_triangular (k := k) hB hd hd2]
  simp only [RetainedTriangularTests,TotalTriangularTests,retainedLinearThrough_iff_totalTor]

/-- The displayed Tor-vanishing statement of Theorem4.2. -/
theorem polymatroidal_iff_degree_tests_totalTor {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) : IsPolymatroidal B ↔ TotalDegreeBoundedTests (k := k) B := by
  rw [polymatroidal_iff_degree_tests (k := k) hB hanti]
  simp only [DegreeBoundedTests,TotalDegreeBoundedTests,retainedLinearThrough_iff_totalTor]

/-- The equivalent smaller cutoff from Theorem4.2, with actual total Tor. -/
theorem polymatroidal_iff_degree_dimension_tests_totalTor {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) : IsPolymatroidal B ↔ TotalDegreeDimensionBoundedTests (k := k) B := by
  rw [polymatroidal_iff_degree_dimension_tests (k := k) hB hanti]
  simp only [DegreeDimensionBoundedTests,TotalDegreeDimensionBoundedTests,
    retainedLinearThrough_iff_totalTor]

end Characterizations
