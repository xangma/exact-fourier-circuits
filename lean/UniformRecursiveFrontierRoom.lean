import Mathlib

namespace ExactFourierCircuits.UniformRecursiveFrontierRoom

/-- A node's workspace and one strictly smaller child's complete reserve fit
inside the original body's reserve. -/
theorem room (payload reserve k q V T : ℕ)
    (one : 1 ≤ V) (smaller : q < k) (width : T ≤ V)
    (reserveFit : payload + 5 ≤ reserve) :
    payload + 5 * V + reserve * (q + 1) * T ≤ reserve * (k + 1) * V := by
  have payloadV : payload ≤ payload * V := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left payload one
  have reserveV := Nat.mul_le_mul_right V reserveFit
  have node : payload + 5 * V ≤ reserve * V := by
    nlinarith only [payloadV, reserveV]
  have child : reserve * (q + 1) * T ≤ reserve * k * V := by
    exact Nat.mul_le_mul (Nat.mul_le_mul_left reserve (by omega : q + 1 ≤ k)) width
  calc
    payload + 5 * V + reserve * (q + 1) * T
        ≤ reserve * V + reserve * k * V := Nat.add_le_add node child
    _ = reserve * (k + 1) * V := by ring

theorem pow_room (payload reserve k q : ℕ)
    (smaller : q < k) (reserveFit : payload + 5 ≤ reserve) :
    payload + 5 * 2 ^ k + reserve * (q + 1) * 2 ^ q
      ≤ reserve * (k + 1) * 2 ^ k := by
  apply room payload reserve k q (2 ^ k) (2 ^ q) _ smaller _ reserveFit
  · exact Nat.one_le_pow k 2 (by omega)
  · exact Nat.pow_le_pow_right (by omega) (Nat.le_of_lt smaller)

/-- The concrete child frontier `entryF + payload + 5 * 2^k` inherits the
parent's bounded reserve, without another descent or child-room premise. -/
theorem child_room (entryF payload reserve k q B : ℕ)
    (smaller : q < k) (reserveFit : payload + 5 ≤ reserve)
    (parentRoom : entryF + reserve * (k + 1) * 2 ^ k ≤ B) :
    (entryF + payload + 5 * 2 ^ k) + reserve * (q + 1) * 2 ^ q ≤ B := by
  have h := Nat.add_le_add_left (pow_room payload reserve k q smaller reserveFit) entryF
  calc
    (entryF + payload + 5 * 2 ^ k) + reserve * (q + 1) * 2 ^ q
        ≤ entryF + reserve * (k + 1) * 2 ^ k := by
          simpa only [Nat.add_assoc] using h
    _ ≤ B := parentRoom

end ExactFourierCircuits.UniformRecursiveFrontierRoom
