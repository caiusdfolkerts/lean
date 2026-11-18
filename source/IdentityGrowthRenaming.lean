module
prelude
public import OrbitGrowthDAG

@[expose] public section

namespace Papers.RationalityTen.GrowthRenaming

def Bijection.identity (α : Type) : Bijection α where
  forward := id
  inverse := id
  left_inverse _ := rfl
  right_inverse _ := rfl

def Renaming.identity {n r : Nat} (ridges : Fin n → Fin r → Bool)
    (compatible : Fin n → Fin n → Bool) (kind : Fin n → Nat) :
    Renaming ridges compatible kind where
  cells := Bijection.identity _
  ridgeMap := Bijection.identity _
  incidence _ _ := rfl
  compatibility _ _ := rfl
  kind_preserved _ := rfl

theorem applyWord_identity {n r g : Nat} (ridges : Fin n → Fin r → Bool)
    (compatible : Fin n → Fin n → Bool) (kind : Fin n → Nat)
    (word : List (Fin g)) (B : List (Fin n)) :
    OrbitGrowthDAG.applyWord (fun _ : Fin g => Renaming.identity ridges compatible kind)
      word B = B := by
  induction word generalizing B with
  | nil => rfl
  | cons p word ih =>
    rw [OrbitGrowthDAG.applyWord, ih]
    exact List.map_id B

end Papers.RationalityTen.GrowthRenaming
