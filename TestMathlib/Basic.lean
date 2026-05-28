def hello := "world"

theorem mul_assoc (a b c : Nat) : (a * b) * c = a * (b * c) := by
induction c with
| zero =>
show a * b * 0 = a * (b * 0)
repeat rw [Nat.mul_zero]
| succ d hd =>
show a * b * (d + 1) = a * (b * (d + 1))
repeat rw [Nat.mul_add]
repeat rw [Nat.mul_one]
rw [hd]
