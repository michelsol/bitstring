import BitString.Basic

namespace Nat

theorem log2_def_of_ge_two {n : Nat} (hn : n ≥ 2) : n.log2 = (n / 2).log2 + 1 := by
  conv => lhs; unfold Nat.log2
  simp [hn]

theorem log2_two_mul {n : Nat} (hn : n ≠ 0) : (2 * n).log2 = n.log2 + 1 := by
  conv => lhs; unfold Nat.log2
  simp [show 2 * n ≥ 2 by omega]

theorem pow_ne_zero {a : Nat} (ha : a > 1) (n : Nat) : a ^ n ≠ 0 := by
  exact not_eq_zero_of_lt $ Nat.pow_le_pow_of_le ha n.zero_le

theorem pow_sub_one {n m : Nat} (hn : n > 0) (hm : m ≠ 0) : n ^ (m - 1) = n ^ m / n := by
  have hm : 1 ≤ m := by omega
  rw [←Nat.pow_div hm hn]
  simp only [Nat.pow_one]

theorem or_shiftLeft (n : Nat) : ∀ x y, (x ||| y) <<< n = x <<< n ||| y <<< n := by
  intro x y
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : n ≤ i <;> simp [h]

end Nat

namespace BitString

/-! ### shiftLeft and shiftRight -/

theorem shiftLeft_succ_inside (x : BitString) (n : Nat) : x <<< (n + 1) = x <<< 1 <<< n := by
    let ⟨size, x, h⟩ := x
    rw [mk.injEq]
    simp_arith [Nat.shiftLeft_succ_inside]

theorem shiftLeft_succ (x : BitString) (n : Nat) : x <<< (n + 1) = x <<< n <<< 1 := by
  let ⟨size, x, h⟩ := x
  rw [mk.injEq]
  simp_arith [Nat.shiftLeft_succ]

theorem shiftRight_succ_inside (x : BitString) (n : Nat) : x >>> (n + 1) = x >>> 1 >>> n := by
    let ⟨size, x, h⟩ := x
    rw [mk.injEq]
    simp [Nat.Simproc.sub_add_eq_comm, Nat.shiftRight_succ_inside]

theorem shiftRight_succ (x : BitString) (n : Nat) : x >>> (n + 1) = x >>> n >>> 1 := by
    let ⟨size, x, h⟩ := x
    rw [mk.injEq]
    simp [Nat.shiftRight_succ]
    rfl

theorem zeros_shiftLeft (n k : Nat) : zeros n <<< k = zeros (n + k) := by
  induction k
  case zero => rfl
  case succ k ih => rw [←Nat.add_assoc, shiftLeft_succ, ih]; rfl

theorem shiftLeft_add (x : BitString) (n k : Nat) : x <<< (n + k) = x <<< n <<< k := by
  induction k
  case zero => rfl
  case succ k ih => rw [←Nat.add_assoc, shiftLeft_succ, ih, ←shiftLeft_succ]

theorem ofNat_shiftRight_one (n : Nat) : ofNat n >>> 1 = ofNat (n >>> 1) := by
  rw [mk.injEq]
  simp [ofNat]
  by_cases hn : n = 0
  . simp [hn]
  . simp [hn]
    split
    . have : n = 1 := by omega
      simp [this, Nat.log2]
    . have : n ≥ 2 := by omega
      simp [Nat.log2_def_of_ge_two this]
      rfl

theorem ofNat_shiftRight (n k : Nat) : ofNat n >>> k = ofNat (n >>> k) := by
  induction k
  case zero => rfl
  case succ k ih =>
    rw [Nat.shiftRight_succ]
    rw [shiftRight_succ, ih]
    rw [ofNat_shiftRight_one]
    rfl

theorem ofNat_shiftLeft_one {n : Nat} (hn : n ≠ 0) : ofNat n <<< 1 = ofNat (n <<< 1) := by
  have : n <<< 1 ≠ 0 := by omega
  rw [mk.injEq]
  simp [ofNat]
  simp [hn]
  simp [this]
  erw [Nat.log2_two_mul hn]

theorem ofNat_shiftLeft (n k : Nat) (hn : n ≠ 0) : ofNat n <<< k = ofNat (n <<< k) := by
  induction k
  case zero => rfl
  case succ k ih =>
    rw [Nat.shiftLeft_succ]
    rw [shiftLeft_succ, ih]
    have : n <<< k ≠ 0 := by
      by_cases hk : k = 0
      . simp [*]
      . simp [Nat.shiftLeft_eq, Nat.mul_ne_zero_iff, hn, Nat.pow_ne_zero]
    rw [ofNat_shiftLeft_one this]
    rfl

/-! ### or -/

theorem or_assoc (x y z : BitString) : x ||| y ||| z = x ||| (y ||| z) := by
  rw [mk.injEq]
  simp [Nat.max_assoc, Nat.or_assoc]

theorem or_shiftLeft (n : Nat) (x y : BitString) : (x ||| y) <<< n = x <<< n ||| y <<< n := by
  rw [mk.injEq]
  simp [Nat.add_max_add_right, Nat.or_shiftLeft]

/-! ### append -/

def append (x y : BitString) := (x <<< y.size) ||| y

instance : Append BitString := ⟨append⟩

@[simp] theorem append_eq (x y : BitString) : x.append y = x ++ y := rfl

@[simp] theorem size_append (x y : BitString) : (x ++ y).size = x.size + y.size := by
  show size ((_ <<< _) ||| _) = _
  simp

theorem append_assoc (x y z : BitString) : x ++ y ++ z = x ++ (y ++ z) := by
  show (x <<< y.size ||| y) <<< z.size ||| z
    = x <<< (y ++ z).size ||| (y <<< z.size ||| z)
  simp [or_shiftLeft, shiftLeft_add, or_assoc]

end BitString
