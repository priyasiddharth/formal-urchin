def add (m: Nat) (n: Nat) : Nat :=
match m,n with
| m, Nat.zero => m
| m, (n+1) => (add m n) + 1

theorem add_comm_zero : add 2 0 = add 0 2 := by
  rw [add, add]
  -- Now the goal is x = y
  -- Since x and y are both equal to 2, we can use `rfl` (reflexivity) to finish the proof
  rw [add, add]
