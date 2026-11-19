module
import RootedBulk

open Papers.RationalityTen Papers.RationalityTen.RootedBulk

private def w : PackedRawNatGrowth.Widths := ⟨2, 2, 2, 2⟩

example : sparseChild w (fun _ c => c + 1) (fun _ => 450) [1] 1 ⟨2, 0, 0⟩ = true := by
  decide +kernel

example : sparseChild w (fun _ c => c + 1) (fun _ => 450) [0] 1 ⟨2, 0, 0⟩ = false := by
  decide +kernel

example : sparseChild w (fun _ c => c + 1) (fun _ => 450) [1] 0 ⟨2, 0, 0⟩ = false := by
  decide +kernel

example : sparseChild w (fun _ c => c) (fun _ => 0) [1] 1 ⟨2, 0, 0⟩ = false := by
  decide +kernel

private def codes (i : Nat) : Nat :=
  if i = 0 then 290 else 33 + 2^7 + 2^18 + 2^28 + 2 * 2^44

private def trial (candidates counter : Nat) : Bool :=
  checkNode w 4 1 1 1 2 (fun _ => candidates) (fun _ => 0) (fun _ => 0) []
    (fun _ => 0) (fun _ => 0) (fun _ c => c) (fun _ => [1, 2]) codes (fun _ => counter) 1

example : trial 6 1 = true := by decide +kernel
example : trial 14 1 = false := by decide +kernel
example : trial 6 2 = false := by decide +kernel
