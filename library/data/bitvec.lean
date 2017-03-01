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
@[reducible]
def append {m n : ℕ} : bitvec m → bitvec n → bitvec (m + n) := vector.append

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
  list.foldl f 0 (to_list x)

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

  protected def list_of_nat : ℕ → ℕ → list bool
  | 0        x := list.nil
  | (succ n) x := list_of_nat n (x / 2) ++ [to_bool (x % 2 = 1)]

  protected lemma length_list_of_nat : ∀ m n : ℕ,
    list.length (bitvec.list_of_nat m n) = m
  | 0 _ := rfl
  | (succ m) n :=
  begin
    unfold list_of_nat,
    simp [length_list_of_nat]
  end

  protected def of_nat (m n : ℕ) : bitvec m
  := ⟨ bitvec.list_of_nat m n, bitvec.length_list_of_nat m n ⟩

  @[simp]
  protected lemma of_nat_to_list (m n : ℕ)
  : (bitvec.of_nat m n)^.to_list = bitvec.list_of_nat m n := rfl

  protected def of_int : Π (n : ℕ), int → bitvec (succ n)
  | n (int.of_nat m)          := ff :: bitvec.of_nat n m
  | n (int.neg_succ_of_nat m) := tt :: not (bitvec.of_nat n m)

  def add_lsb (r : ℕ) (b : bool) : ℕ := r + r + cond b 1 0

  @[simp]
  lemma add_lsb_zero (b : bool) : add_lsb 0 b = cond b 1 0 :=
  begin unfold add_lsb, simp end

  def bits_to_nat (v : list bool) : nat :=
  list.foldl add_lsb 0 v

  protected def to_nat {n : nat} (v : bitvec n) : nat :=
  bits_to_nat (to_list v)

  @[simp]
  lemma to_nat_eq_bits_to_nat {n : ℕ} (x : bitvec n)
  : bitvec.to_nat x = bits_to_nat x^.to_list :=
  begin
    cases x with x Px,
    refl,
  end

  protected def to_int : Π {n : ℕ}, bitvec n → int
  | 0        _ := 0
  | (succ n) v :=
    cond (head v)
      (int.neg_succ_of_nat $ bitvec.to_nat $ not $ tail v)
      (int.of_nat $ bitvec.to_nat $ tail v)

end conversion

private def to_string {n : ℕ} : bitvec n → string
| ⟨bs, p⟩ :=
  "0b" ++ (bs^.reverse^.for (λ b, if b then #"1" else #"0"))

instance (n : nat) : has_to_string (bitvec n) :=
⟨to_string⟩

theorem bits_to_nat_of_to_bool (n : ℕ)
: bitvec.bits_to_nat [to_bool (n % 2 = 1)] = n % 2
:=
   or.elim (nat.mod_2_or n)
     (assume h : n % 2 = 0, begin rw h, refl end)
     (assume h : n % 2 = 1, begin rw h, refl end)

section list

open list
open subtype

theorem bits_to_nat_over_append (xs : list bool) (y : bool)
: bitvec.bits_to_nat (xs ++ [y]) = bitvec.bits_to_nat xs * 2 + bitvec.bits_to_nat [y]  :=
      begin
        simp, unfold bitvec.bits_to_nat,
        simp [foldl_to_cons],
        unfold bitvec.add_lsb,
        simp [nat.two_mul],
      end

end list

lemma div_mul_sub_one_cancel {n p k : ℕ} (Hp : 1 ≤ p)
  (H : n ≤ p * p^k - 1)
:  n / p ≤ p^k - 1 :=
begin
  assert H' : n / p ≤ (p*p^k - 1) / p,
  { apply nat.div_le_div H _ },
  rw nat.div_pred_to_pred_div (p^k) Hp at H',
  apply H'
end

theorem bits_to_nat_list_of_nat
: ∀ {k n : ℕ}, n ≤ 2 ^ k - 1 → bitvec.bits_to_nat (bitvec.list_of_nat k n) = n
 | nat.zero n :=
        begin
          intro Hn_le,
          assert Hn_eq : n = 0,
          { apply nat.le_zero_of_eq_zero Hn_le },
          subst n, refl
        end
 | (nat.succ k) n :=
        begin
          intro H,
          assert H' : n / 2 ≤ 2^k - 1,
          { apply div_mul_sub_one_cancel (nat.le_succ _) H },
          unfold bitvec.list_of_nat,
          simp [ bitvec.bits_to_nat_over_append
               , bits_to_nat_list_of_nat H'
               , bits_to_nat_of_to_bool
               , nat.mod_add_div n 2 ],
        end

theorem to_nat_of_nat {k n : ℕ} (h : n ≤ 2 ^ k - 1) :
   bitvec.to_nat (bitvec.of_nat k n) = n
:= by simp [to_nat_eq_bits_to_nat,bits_to_nat_list_of_nat h]

theorem to_nat_of_to_bool (n : ℕ)
: bitvec.to_nat [to_bool (n % 2 = 1)] = n % 2
:=
   or.elim (nat.mod_2_or n)
     (assume h : n % 2 = 0, begin rw h, refl end)
     (assume h : n % 2 = 1, begin rw h, refl end)

theorem to_nat_cons_ff
: ∀ xs : list bool, bitvec.bits_to_nat (ff :: xs) = bitvec.bits_to_nat xs :=
  take xs,
  begin
    unfold bitvec.bits_to_nat,
    assert h : add_lsb 0 ff = 0, { simp, refl },
    simp [h]
  end

theorem to_nat_append_zero {n : ℕ}
: ∀ {m} k : bitvec n, bitvec.to_nat (bitvec.append (bitvec.zero m) k) = bitvec.to_nat k
  | nat.zero ⟨k, Pk⟩ := rfl
  | (nat.succ n) ⟨k, Pk⟩ :=
  begin
    simp [to_nat_eq_bits_to_nat,to_nat_cons_ff],
    apply to_nat_append_zero ⟨k,Pk⟩
  end

definition join : Π {m n : ℕ}, vector (bitvec m) n → bitvec (m * n) := @vector.join bool

definition split : Π (m : ℕ) {n : ℕ}, bitvec (m * n) → vector (bitvec m) n := @vector.split bool

@[reducible]
definition join_list : Π {m : ℕ}, list (bitvec m) → list bool := @vector.join_list bool

@[reducible]
definition split_vector : Π {m : ℕ} (n : ℕ), bitvec (m * n) → list (bitvec m) := @vector.split_vector bool

end bitvec

instance {n} {x y : bitvec n} : decidable (bitvec.ult x y) := bool.decidable_eq _ _
instance {n} {x y : bitvec n} : decidable (bitvec.ugt x y) := bool.decidable_eq _ _
