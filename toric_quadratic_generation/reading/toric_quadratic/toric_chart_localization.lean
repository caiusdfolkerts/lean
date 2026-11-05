module

public import PaperVerification.ToricPrincipalChartModules
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

/-!
# Localization of actual semigroup chart subalgebras

All maps below are the literal inclusions of subalgebras of k[M]. A
finite Laurent polynomial has one common character denominator whenever
each of its finitely many exponents does. This proves the localization
property, without replacing the inclusion by an abstract ring isomorphism.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open Set AddMonoidAlgebra
open scoped BigOperators Classical

variable (k : Type*) [CommSemiring k]
variable {G : Type*} [AddCommGroup G]

theorem monoidChartAlgebra_mono {S T : AddSubmonoid G} (hST : S ≤ T) :
    monoidChartAlgebra k S ≤ monoidChartAlgebra k T := by
  intro f hf
  rw [mem_monoidChartAlgebra] at hf ⊢
  exact fun m hm => hST (hf hm)

def monoidChartInclusion {S T : AddSubmonoid G} (hST : S ≤ T) :
    monoidChartAlgebra k S →ₐ[k] monoidChartAlgebra k T :=
  Subalgebra.inclusion (monoidChartAlgebra_mono k hST)

@[simp] theorem monoidChartInclusion_coe {S T : AddSubmonoid G} (hST : S ≤ T)
    (f : monoidChartAlgebra k S) :
    ((monoidChartInclusion k hST f : monoidChartAlgebra k T) : AddMonoidAlgebra k G) = f := rfl

theorem monoidChartInclusion_injective {S T : AddSubmonoid G} (hST : S ≤ T) :
    Function.Injective (monoidChartInclusion k hST) :=
  Subalgebra.inclusion_injective (monoidChartAlgebra_mono k hST)

@[simp] theorem monoidChartInclusion_comp {S T U : AddSubmonoid G}
    (hST : S ≤ T) (hTU : T ≤ U) :
    (monoidChartInclusion k hTU).comp (monoidChartInclusion k hST) =
      monoidChartInclusion k (hST.trans hTU) := by
  ext f
  rfl

@[simp] theorem monoidChartInclusion_self (S : AddSubmonoid G) :
    monoidChartInclusion k (le_refl S) = AlgHom.id k (monoidChartAlgebra k S) := by
  ext f
  rfl

def chartCharacter (S : AddSubmonoid G) (v : G) (hv : v ∈ S) : monoidChartAlgebra k S :=
  ⟨single v (1 : k), ⟨single ⟨v, hv⟩ (1 : k), by simp⟩⟩

@[simp] theorem chartCharacter_coe (S : AddSubmonoid G) (v : G) (hv : v ∈ S) :
    ((chartCharacter k S v hv : monoidChartAlgebra k S) : AddMonoidAlgebra k G) =
      single v (1 : k) := rfl

@[simp] theorem monoidChartInclusion_character {S T : AddSubmonoid G}
    (hST : S ≤ T) (v : G) (hv : v ∈ S) :
    monoidChartInclusion k hST (chartCharacter k S v hv) =
      chartCharacter k T v (hST hv) := rfl

theorem finite_character_denominator {S T : AddSubmonoid G}
    (v : G) (hv : v ∈ S)
    (hclear : ∀ m ∈ T, ∃ N : ℕ, m + N • v ∈ S)
    (F : Finset G) (hF : ∀ m ∈ F, m ∈ T) :
    ∃ N : ℕ, ∀ m ∈ F, m + N • v ∈ S := by
  revert hF
  induction F using Finset.induction_on with
  | empty =>
      intro hF
      exact ⟨0, by simp⟩
  | @insert m F hm ih =>
      intro hF
      obtain ⟨N, hN⟩ := ih (fun z hz => hF z (Finset.mem_insert_of_mem hz))
      obtain ⟨L, hL⟩ := hclear m (hF m (Finset.mem_insert_self m F))
      refine ⟨L + N, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · simpa only [add_nsmul, add_assoc] using S.add_mem hL (S.nsmul_mem hv N)
      · have hh := S.add_mem (hN z hz) (S.nsmul_mem hv L)
        simpa only [add_nsmul, add_assoc, add_comm, add_left_comm] using hh

/-- One common monomial clears every denominator of the actual finite
Laurent polynomial, not only of each monomial separately. -/
theorem polynomial_character_denominator {S T : AddSubmonoid G}
    (v : G) (hv : v ∈ S)
    (hclear : ∀ m ∈ T, ∃ N : ℕ, m + N • v ∈ S)
    (f : monoidChartAlgebra k T) :
    ∃ N : ℕ, (f : AddMonoidAlgebra k G) * single (N • v) (1 : k) ∈
      monoidChartAlgebra k S := by
  have hf : ∀ m ∈ (f : AddMonoidAlgebra k G).coeff.support, m ∈ T :=
    (mem_monoidChartAlgebra k T f).mp f.property
  obtain ⟨N, hN⟩ := finite_character_denominator v hv hclear
    (f : AddMonoidAlgebra k G).coeff.support hf
  refine ⟨N, (mem_monoidChartAlgebra k S _).mpr ?_⟩
  intro z hz
  have hsupport := AddMonoidAlgebra.support_coeff_mul_single_subset
    (f : AddMonoidAlgebra k G) (1 : k) (N • v)
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp (hsupport hz)
  exact hN m hm

/-- The literal inclusion is a localization map at the specified
character. The kernel condition follows from actual injectivity. -/
theorem monoidChartInclusion_isLocalizationMap {S T : AddSubmonoid G}
    (hST : S ≤ T) (v : G) (hv : v ∈ S) (hneg : -v ∈ T)
    (hclear : ∀ m ∈ T, ∃ N : ℕ, m + N • v ∈ S) :
    (Submonoid.powers (chartCharacter k S v hv)).IsLocalizationMap
      (monoidChartInclusion k hST) := by
  have hunit : IsUnit (monoidChartInclusion k hST (chartCharacter k S v hv)) := by
    exact (chartCharacterUnit k T v (hST hv) hneg).isUnit
  refine ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨N, hN⟩ := (Submonoid.mem_powers_iff _ _).mp y.property
    rw [← hN, map_pow]
    exact hunit.pow N
  · intro f
    obtain ⟨N, hN⟩ := polynomial_character_denominator k v hv hclear f
    let g : monoidChartAlgebra k S :=
      ⟨(f : AddMonoidAlgebra k G) * single (N • v) (1 : k), hN⟩
    let y : Submonoid.powers (chartCharacter k S v hv) :=
      ⟨(chartCharacter k S v hv) ^ N, (Submonoid.mem_powers_iff _ _).mpr ⟨N, rfl⟩⟩
    refine ⟨(g, y), ?_⟩
    apply Subtype.ext
    change (f : AddMonoidAlgebra k G) * (single v (1 : k)) ^ N =
      (f : AddMonoidAlgebra k G) * single (N • v) (1 : k)
    simp only [AddMonoidAlgebra.single_pow, one_pow]
  · intro x y hxy
    have heq := monoidChartInclusion_injective k hST hxy
    subst y
    exact ⟨1, rfl⟩

end PaperVerification.ToricCharacters
