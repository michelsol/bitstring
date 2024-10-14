structure BitString where
  size : Nat
  toNat : Nat
  isLt : toNat < 2 ^ size -- Fin is probably less nice as mk.injEq would have HEq's

namespace BitString

instance : DecidableEq BitString := by
  intro x y; rw [mk.injEq]; infer_instance

def toFin (x : BitString) : Fin (2 ^ x.size) := ⟨x.toNat, x.isLt⟩

def ofNat (n : Nat) : BitString where
  toNat := n
  size := if n = 0 then 0 else n.log2 + 1
  isLt := by split <;> simp [*, Nat.lt_log2_self]

def ofBool (x : Bool) : BitString where
  toNat := x.toNat
  size := 1
  isLt := by by_cases hx : x = true <;> simp [hx]

def toBitVec (s : BitString) := BitVec.ofFin s.toFin

def ofBitVec {size} (v : BitVec size) : BitString where
  toNat := v.toNat
  size := size
  isLt := v.isLt

def nil : BitString := ofNat 0

@[simp] theorem size_nil : nil.size = 0 := rfl

@[simp] theorem toNat_nil : nil.toNat = 0 := rfl

def zeros (size : Nat) : BitString where
  toNat := 0
  size := size
  isLt := size.two_pow_pos

def ones (size : Nat) : BitString where
  toNat := 2 ^ size - 1
  size := size
  isLt := Nat.sub_one_lt_of_lt size.two_pow_pos


/-- Return the `i`-th least significant bit or `false` if `i ≥ w`. -/
@[simp, inline] def getLsbD (x : BitString) (i : Nat) : Bool := x.toNat.testBit i

/-- Return the `i`-th least significant bit. -/
@[inline] def getLsb (x : BitString) (i : Fin x.size) : Bool := x.getLsbD i.val

/-- Return the `i`-th least significant bit or `none` if `i ≥ w`. -/
@[inline] def getLsb? (x : BitString) (i : Nat) : Option Bool :=
  if i < x.size then some (x.getLsbD i) else none

/-- Return the `i`-th most significant bit. -/
@[inline] def getMsbD (x : BitString) (i : Nat) : Bool := x.getLsbD (x.size - 1 - i)

/-- Return the `i`-th most significant bit. -/
@[inline] def getMsb (x : BitString) (i : Fin x.size) : Bool := x.getMsbD i.val

/-- Return the `i`-th most significant bit or `none` if `i ≥ w`. -/
@[inline] def getMsb? (x : BitString) (i : Nat) : Option Bool :=
  if i < x.size then some (x.getMsbD i) else none

/-! ### shiftLeft -/

def shiftLeft (x : BitString) (n : Nat) : BitString where
  size := x.size + n
  toNat := x.toNat <<< n
  isLt := by
    induction n
    case zero => exact x.isLt
    case succ n ih => rw [Nat.shiftLeft_succ, ←Nat.add_assoc]; omega

instance : HShiftLeft BitString Nat BitString := ⟨shiftLeft⟩

@[simp] theorem shiftLeft_simp (x : BitString) (n : Nat) : x.shiftLeft n = x <<< n := rfl

@[simp] theorem size_shiftLeft (x : BitString) (n : Nat) : (x <<< n).size = x.size + n := rfl

@[simp] theorem toNat_shiftLeft (x : BitString) (n : Nat) : (x <<< n).toNat = x.toNat <<< n := rfl

@[simp] theorem shiftLeft_zero (x : BitString) : x <<< 0 = x := rfl

/-! ### shiftRight -/

def shiftRight (x : BitString) (n : Nat) : BitString where
  size := x.size - n
  toNat := x.toNat >>> n
  isLt := by
    induction n
    case zero => exact x.isLt
    case succ n ih =>
      rw [Nat.shiftRight_succ, Nat.div_lt_iff_lt_mul Nat.zero_lt_two]
      rw [Nat.sub_add_eq, ←Nat.pow_succ, Nat.succ_eq_add_one]
      by_cases hn : x.size - n = 0
      . simp [hn] at *; omega
      . rwa [Nat.sub_one_add_one hn]

instance : HShiftRight BitString Nat BitString := ⟨shiftRight⟩

@[simp] theorem shiftRight_simp (x : BitString) (n : Nat) : x.shiftRight n = x >>> n := rfl

@[simp] theorem size_shiftRight (x : BitString) (n : Nat) : (x >>> n).size = x.size - n := rfl

@[simp] theorem toNat_shiftRight (x : BitString) (n : Nat) : (x >>> n).toNat = x.toNat >>> n := rfl

@[simp] theorem shiftRight_zero (x : BitString) : x >>> 0 = x := rfl

/-! ### push -/

def push (x : BitString) (b : Bool) : BitString where
  size := x.size + 1
  toNat := x.toNat <<< 1 + b.toNat
  isLt := by
    have := x.isLt
    by_cases hb : b = true <;> (simp [hb]; omega)

@[simp] theorem size_push (x : BitString) (b : Bool) : (x.push b).size = x.size + 1 := rfl

@[simp] theorem toNat_push (x : BitString) (b : Bool) :
    (x.push b).toNat = x.toNat <<< 1 + b.toNat := rfl

/-! ### bitwise -/

theorem eq_nil_iff_size_eq_zero {x : BitString} : x = nil ↔ x.size = 0 := by
  constructor
  . intro hx
    simp [hx]
  . intro hx
    rw [mk.injEq]
    have := x.isLt
    simp [hx] at *
    omega

def bitwise (f : Bool → Bool → Bool) (n m : BitString) : BitString :=
  if n = nil then
    if f false true then m else nil
  else if m = nil then
    if f true false then n else nil
  else
    (bitwise f (n >>> 1) (m >>> 1)).push $ f (n.getLsbD 0) (m.getLsbD 0)
termination_by n.size
decreasing_by simp_wf; rw [eq_nil_iff_size_eq_zero] at *; omega

@[simp] theorem toNat_bitwise (f : Bool → Bool → Bool) (hf : f false false = false)
    (x y : BitString) : (bitwise f x y).toNat = Nat.bitwise f x.toNat y.toNat := by
  induction x, y using bitwise.induct f with
  | case1 x | case2 x | case4 x => simp [bitwise, Nat.bitwise, *]
  | case3 x hx h => by_cases x.toNat = 0 <;> simp [bitwise, Nat.bitwise, *]
  | case5 x y hx hy ih =>
    unfold Nat.bitwise bitwise
    simp [hx, hy, ih]
    dsimp only [(.>>>.), ShiftRight.shiftRight, Nat.shiftRight]
    dsimp only [(.<<<.), ShiftLeft.shiftLeft, Nat.shiftLeft]
    by_cases f false true = true; all_goals
    by_cases f true false = true; all_goals
    by_cases f true true = true; all_goals
    by_cases x.toNat = 0
    . by_cases y.toNat % 2 = 1 <;> (simp [Nat.bitwise, *]; try omega)
    . by_cases y.toNat = 0
      . by_cases x.toNat % 2 = 1 <;> by_cases x.toNat / 2 = 0 <;> (simp [Nat.bitwise, *]; try omega)
      . by_cases x.toNat % 2 = 1 <;> by_cases y.toNat % 2 = 1 <;> (simp [*]; omega)

/-! ### or -/
def or (x y : BitString) := bitwise Bool.or x y

instance : OrOp BitString := ⟨or⟩

@[simp] theorem or_simp (x y : BitString) : x.or y = x ||| y := rfl

@[simp] theorem toNat_or (x y : BitString) : (x ||| y).toNat = x.toNat ||| y.toNat :=
  toNat_bitwise _ rfl x y

@[simp] theorem size_or (x y : BitString) : (x ||| y).size = max x.size y.size := by
  show size (bitwise ..) = _
  induction x, y using bitwise.induct Bool.or with
  | case1 x | case2 x => simp [bitwise]
  | case3 x hx => simp [bitwise, hx]
  | case4 x => contradiction
  | case5 x y hx hy ih =>
    unfold bitwise
    simp [hx, hy, ih]
    simp [eq_nil_iff_size_eq_zero] at hx hy
    omega

/-! ### and -/

def and (x y : BitString) := bitwise Bool.and x y

instance : AndOp BitString := ⟨and⟩

@[simp] theorem and_simp (x y : BitString) : x.and y = x &&& y := rfl

@[simp] theorem toNat_and (x y : BitString) : (x &&& y).toNat = x.toNat &&& y.toNat :=
  toNat_bitwise _ rfl x y

@[simp] theorem size_and (x y : BitString) : (x &&& y).size = min x.size y.size := by
  show size (bitwise ..) = _
  induction x, y using bitwise.induct Bool.and with
  | case1 y | case2 y => simp [bitwise]
  | case3 x hx => simp [bitwise, hx]
  | case4 x => simp [bitwise]
  | case5 x y hx hy ih =>
    unfold bitwise
    simp [hx, hy, ih]
    simp [eq_nil_iff_size_eq_zero] at hx hy
    omega

/-! ### xor -/

def xor (x y : BitString) := bitwise Bool.xor x y

instance : Xor BitString := ⟨xor⟩

@[simp] theorem xor_simp (x y : BitString) : x.xor y = x ^^^ y := rfl

@[simp] theorem toNat_xor (x y : BitString) : (x ^^^ y).toNat = x.toNat ^^^ y.toNat :=
  toNat_bitwise _ rfl x y

@[simp] theorem size_xor (x y : BitString) : (x ^^^ y).size = max x.size y.size := by
  show size (bitwise ..) = _
  induction x, y using bitwise.induct Bool.and with
  | case1 y | case2 y => simp [bitwise]
  | case3 x hx => simp [bitwise, hx]
  | case4 x hx => simp [bitwise, hx]
  | case5 x y hx hy ih =>
    unfold bitwise
    simp [hx, hy, ih]
    simp [eq_nil_iff_size_eq_zero] at hx hy
    omega

end BitString
