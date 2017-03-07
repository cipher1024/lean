/-
Copyright (c) 2015 Joe Hendrix. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Sebastian Ullrich

Basic operations on bitvectors.

This is a work-in-progress, and contains additions to other theories.
-/
import data.vector

@[reducible] def bitvec (n : ℕ) := vector bool n

namespace bitvec
open nat
open vector

local infix `++ₜ`:65 := vector.append

-- Create a zero bitvector
@[reducible] protected def zero (n : ℕ) : bitvec n := repeat ff n

-- Create a bitvector with the constant one.
@[reducible] protected def one : Π (n : ℕ), bitvec n
| 0        := []
| (succ n) := repeat ff n ++ₜ [tt]

protected def cong {a b : ℕ} (h : a = b) : bitvec a → bitvec b
| ⟨x, p⟩ := ⟨x, h ▸ p⟩

-- bitvec specific version of vector.append
def append {m n} : bitvec m → bitvec n → bitvec (m + n) := vector.append

section shift
  variable {n : ℕ}

  def shl (x : bitvec n) (i : ℕ) : bitvec n :=
  bitvec.cong (by simp) $
    dropn i x ++ₜ repeat ff (min n i)

  local attribute [ematch] nat.add_sub_assoc sub_le le_of_not_ge sub_eq_zero_of_le
  def fill_shr (x : bitvec n) (i : ℕ) (fill : bool) : bitvec n :=
  bitvec.cong (by async { begin [smt] by_cases (i ≤ n), eblast end }) $
    repeat fill (min n i) ++ₜ taken (n-i) x

  -- unsigned shift right
  def ushr (x : bitvec n) (i : ℕ) : bitvec n :=
  fill_shr x i ff

  -- signed shift right
  def sshr : Π {m : ℕ}, bitvec m → ℕ → bitvec m
  | 0        _ _ := []
  | (succ m) x i := head x :: fill_shr (tail x) i (head x)

end shift

section bitwise
  variable {n : ℕ}

  def not : bitvec n → bitvec n := map bnot
  def and : bitvec n → bitvec n → bitvec n := map₂ band
  def or  : bitvec n → bitvec n → bitvec n := map₂ bor
  def xor : bitvec n → bitvec n → bitvec n := map₂ bxor

end bitwise

section arith
  variable {n : ℕ}

  protected def xor3 (x y c : bool) := bxor (bxor x y) c
  protected def carry (x y c : bool) :=
  x && y || x && c || y && c

  protected def neg (x : bitvec n) : bitvec n :=
  let f := λ y c, (y || c, bxor y c) in
  prod.snd (map_accumr f x ff)

  -- Add with carry (no overflow)
  def adc (x y : bitvec n) (c : bool) : bitvec (n+1) :=
  let f := λ x y c, (bitvec.carry x y c, bitvec.xor3 x y c) in
  let ⟨c, z⟩ := vector.map_accumr₂ f x y c in
  c :: z

  protected def add (x y : bitvec n) : bitvec n := tail (adc x y ff)

  protected def borrow (x y b : bool) :=
  bnot x && y || bnot x && b || y && b

  -- Subtract with borrow
  def sbb (x y : bitvec n) (b : bool) : bool × bitvec n :=
  let f := λ x y c, (bitvec.borrow x y c, bitvec.xor3 x y c) in
  vector.map_accumr₂ f x y b

  protected def sub (x y : bitvec n) : bitvec n := prod.snd (sbb x y ff)

  instance : has_zero (bitvec n) := ⟨bitvec.zero n⟩
  instance : has_one (bitvec n)  := ⟨bitvec.one n⟩
  instance : has_add (bitvec n)  := ⟨bitvec.add⟩
  instance : has_sub (bitvec n)  := ⟨bitvec.sub⟩
  instance : has_neg (bitvec n)  := ⟨bitvec.neg⟩

  protected def mul (x y : bitvec n) : bitvec n :=
  let f := λ r b, cond b (r + r + y) (r + r) in
  (to_list x)^.foldl f 0

  instance : has_mul (bitvec n)  := ⟨bitvec.mul⟩
end arith

section comparison
  variable {n : ℕ}

  def uborrow (x y : bitvec n) : bool := prod.fst (sbb x y ff)

  def ult (x y : bitvec n) : Prop := uborrow x y
  def ugt (x y : bitvec n) : Prop := ult y x

  def ule (x y : bitvec n) : Prop := ¬ (ult y x)
  def uge (x y : bitvec n) : Prop := ule y x

  def sborrow : Π {n : ℕ}, bitvec n → bitvec n → bool
  | 0        _ _ := ff
  | (succ n) x y :=
    match (head x, head y) with
    | (tt, ff) := tt
    | (ff, tt) := ff
    | _        := uborrow (tail x) (tail y)
    end

  def slt (x y : bitvec n) : Prop := sborrow x y
  def sgt (x y : bitvec n) : Prop := slt y x
  def sle (x y : bitvec n) : Prop := ¬ (slt y x)
  def sge (x y : bitvec n) : Prop := sle y x

end comparison

section conversion
  variable {α : Type}

  protected def of_nat : Π (n : ℕ), nat → bitvec n
  | 0        x := nil
  | (succ n) x := of_nat n (x / 2) ++ₜ [to_bool (x % 2 = 1)]

  protected def of_int : Π (n : ℕ), int → bitvec (succ n)
  | n (int.of_nat m)          := ff :: bitvec.of_nat n m
  | n (int.neg_succ_of_nat m) := tt :: not (bitvec.of_nat n m)

  def bits_to_nat (v : list bool) : nat :=
  v^.foldl (λ r b, r + r + cond b 1 0) 0

  lemma cond_to_bool_mod_two (x k : ℕ)
  : cond (to_bool (x % 2 = 1)) k 0 = k * (x % 2) := sorry

  protected def to_nat {n : nat} (v : bitvec n) : nat :=
  bits_to_nat (to_list v)

  protected def to_int : Π {n : nat}, bitvec n → int
  | 0        _ := 0
  | (succ n) v :=
    cond (head v)
      (int.neg_succ_of_nat $ bitvec.to_nat $ not $ tail v)
      (int.of_nat $ bitvec.to_nat $ tail v)

end conversion

private def to_string {n : nat} : bitvec n → string
| ⟨bs, p⟩ :=
  "0b" ++ (bs^.reverse^.map (λ b, if b then #"1" else #"0"))

instance (n : nat) : has_to_string (bitvec n) :=
⟨to_string⟩
end bitvec

instance {n} {x y : bitvec n} : decidable (bitvec.ult x y) := bool.decidable_eq _ _
instance {n} {x y : bitvec n} : decidable (bitvec.ugt x y) := bool.decidable_eq _ _

-- theorem bits_to_nat_list_of_nat
-- : ∀ {k n : ℕ}, n ≤ 2 ^ k - 1 → bitvec.bits_to_nat (bitvec.list_of_nat k n) = n
--  | nat.zero n :=
--         begin
--           intro Hn_le,
--           assert Hn_eq : n = 0,
--           { apply nat.le_zero_of_eq_zero Hn_le },
--           subst n, refl
--         end
--  | (nat.succ k) n :=
--         begin
--           intro H,
--           assert H' : n / 2 ≤ 2^k - 1,
--           { apply div_mul_sub_one_cancel (nat.le_succ _) H },
--           unfold bitvec.list_of_nat,
--           simp [ bitvec.bits_to_nat_over_append
--                , bits_to_nat_list_of_nat H'
--                , bits_to_nat_of_to_bool
--                , nat.mod_add_div n 2 ],
--         end

-- theorem to_nat_of_nat {k n : ℕ} (h : n ≤ 2 ^ k - 1) :
--    bitvec.to_nat (bitvec.of_nat k n) = n
-- := by simp [to_nat_eq_bits_to_nat,bits_to_nat_list_of_nat h]

open nat

-- def bit_n (n k : ℕ) : bool := n % 2^succ k - n % 2^k = 2^k
def nth_bit : ℕ → ℕ → bool
  | 0 k := k % 2 = 1
  | (succ n) k := nth_bit n (k / 2)

def nth_bit_weight (n k : ℕ) : ℕ := cond (nth_bit n k) (2^n) 0

-- lemma mod_two_eq_zero_or_one (n : ℕ) :

-- lemma foo (n k : ℕ) : n % 2^succ k - n % 2^k = 2^k ∨ n % 2^succ k - n % 2^k = 0 :=
-- begin
--   induction k with k,
--   { simp [mod_one],
--     note h := @mod_lt n 2 (le_succ _),
--     cases nat.eq_or_lt_of_le (le_of_succ_le_succ h) with h₀ h₀,
--     { apply or.inl h₀ },
--     cases nat.eq_or_lt_of_le (le_of_succ_le_succ h₀) with h₀ h₀,
--     { apply or.inr h₀ },
--     cases not_lt_zero _ h₀ },
--   { simp }
-- end

lemma bitvec.of_nat_succ (k n : ℕ)
: bitvec.of_nat (succ k) n = nth_bit k n :: bitvec.of_nat k n := sorry

lemma bitvec.to_nat_cons {n : ℕ} (v : bitvec n) (b : bool)
: bitvec.to_nat (b :: v) = cond b (2^n) 0 + bitvec.to_nat v := sorry

lemma {u} fun_app_cond {α β : Type u} (f : α → β) (b : bool) (x y : α)
: f (cond b x y) = cond b (f x) (f y) := sorry

lemma bitvec.j {n k : ℕ} : 2^k ≤ n → n < 2^succ k → nth_bit k n = true := sorry

lemma bitvec.i {n k : ℕ} : n < 2^k → nth_bit k n = false := sorry

set_option pp.implicit true

lemma decidable.to_bool.eq_to_iff : ∀ (p q : Prop) [dp : decidable p] [dq : decidable q]
(h : p ↔ q), @to_bool p dp = @to_bool q dq
  | p q dp dq Hiff :=
   begin
     assert h : ite p (tt) (ff) = ite q (tt) (ff),
     { cases decidable.em p with hp hp,
       rw [if_pos hp,if_pos (Hiff^.mp hp)],
       rw [if_neg hp,if_neg ((not_iff_not_of_iff Hiff)^.mp hp)], },
     unfold ite decidable.rec_on at h,
     apply h,
   end

lemma nat.sub_div (n k p : ℕ) : (n - k) / p = n / p - (k + p - 1) / p :=
sorry

lemma nat.mul_add_div (n k p : ℕ) : (p*n + k) / p = n + k / p :=
sorry

lemma sub_pow_mod_pow (x k n : ℕ)
  (h₀ : 0 < n)
  (h₁ : k*n ≤ x)
: (x - k*n) % n = x % n :=
begin
  induction k with k,
  { simp },
  { assert h₂ : k * n ≤ x,
    { rw [succ_mul] at h₁,
      transitivity,
      { apply le_add_right _ n },
      { apply h₁ } },
    assert h₄ : x - k * n ≥ n,
    { apply @nat.le_of_add_le_add_right (k*n),
      rw [nat.sub_add_cancel h₂],
      simp [succ_mul] at h₁, simp [h₁] },
    rw [succ_mul,-nat.sub_sub,-mod_eq_sub_mod h₀ h₄,ih_1 h₂] }
end

lemma bitvec.h (k n : ℕ) (h : 2^succ k ≤ n)
: nth_bit k (n - 2^succ k) = nth_bit k n :=
begin
  revert n,
  induction k with k ; intros n h,
  { note h' := (le_succ 1),
    unfold nth_bit,
    apply decidable.to_bool.eq_to_iff,
    simp [@mod_eq_sub_mod n 2 h' h],  },
  { assert h'' : 1 / 2 = (0 : ℕ), { refl },
    unfold nth_bit,
    rw [nat.sub_div,nat.add_sub_assoc,pow_succ,nat.mul_add_div],
    simp [h''],
    apply ih_1,
    { apply indirect_le_right,
      intros z h''',
      rw le_div_iff_mul_le,
      transitivity,
      { apply mul_le_mul_right _ h''' },
      { dsimp at h, simp [h] },
      apply le_succ },
    apply le_succ }
end

-- lemma foo (p m n : ℕ) : ∃ k, p^m = k*p^n := sorry


lemma nth_bit_weight_add_mod (p n : ℕ)
: nth_bit_weight n p + p % (2^n) = p % (2^succ n) :=
begin
  unfold nth_bit_weight,
  apply nat.strong_induction_on p,
  clear p,
  intros p IH,
  cases lt_or_ge p (2^succ n) with h₁ h₁,
  -- base case
  { rw [mod_eq_of_lt h₁],
    cases lt_or_ge p (2^n) with h₂ h₂,
    -- case n < 2^k
    { simp [mod_eq_of_lt h₂,bitvec.i h₂], refl },
    -- case n ≥ 2^k
    { assert h₃ : p - 2^n < 2^n,
      { apply @nat.lt_of_add_lt_add_right (2^n),
        rw [nat.sub_add_cancel h₂],
        simp [succ_mul] at h₁,
        apply h₁ },
      assert h₄ : 0 < 2^n, { apply pos_pow_succ },
      simp [mod_eq_sub_mod h₄ h₂,mod_eq_of_lt h₃,bitvec.j h₂ h₁],
      unfold decidable.to_bool cond,
      rw [nat.sub_add_cancel h₂] } },
  -- step
  { assert h₀ : 2^succ n > 0, { apply pos_pow_succ },
    assert h₂ : p - 2^succ n < p,
    { apply @nat.lt_of_add_lt_add_right (2^succ n),
      rw [nat.sub_add_cancel h₁],
      apply lt_add_of_pos_right _ h₀ },
    rw [mod_eq_sub_mod h₀ h₁,-IH _ h₂],
    apply congr, apply congr_arg,
    { rw bitvec.h _ _ h₁  },
    { rw [pow_succ,sub_pow_mod_pow],
      apply pos_pow_succ,
      apply h₁ } },
end

theorem to_nat_of_nat {k n : ℕ} :
   bitvec.to_nat (bitvec.of_nat k n) = n % 2^k :=
begin
  induction k with k,
  { unfold pow, simp [nat.mod_one], refl },
  { simp [bitvec.of_nat_succ,bitvec.to_nat_cons,ih_1],
    rw [add_comm], apply nth_bit_weight_add_mod, }
end
