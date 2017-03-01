/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Tuples are lists of a fixed size.
It is implemented as a subtype.
-/
import data.list

universes u v w

def vector (α : Type u) (n : ℕ) := { l : list α // l^.length = n }

namespace vector
variables {α : Type u} {β : Type v} {φ : Type w}
variable {m : ℕ}
variable {n : ℕ}

instance [decidable_eq α] : decidable_eq (vector α n) :=
begin unfold vector, apply_instance end

@[pattern] def nil : vector α 0 := ⟨[],  rfl⟩

@[pattern] def cons : α → vector α n → vector α (nat.succ n)
| a ⟨ v, h ⟩ := ⟨ a::v, congr_arg nat.succ h ⟩

@[reducible] def length (v : vector α n) : ℕ := n

notation a :: b := cons a b
notation `[` l:(foldr `, ` (h t, cons h t) nil `]`) := l

open nat

def head : vector α (nat.succ n) → α
| ⟨ [],     h ⟩ := by contradiction
| ⟨ a :: v, h ⟩ := a

theorem head_cons (a : α) : Π (v : vector α n), head (a :: v) = a
| ⟨ l, h ⟩ := rfl

def tail : vector α (succ n) → vector α n
| ⟨ [],     h ⟩ := by contradiction
| ⟨ a :: v, h ⟩ := ⟨ v, congr_arg pred h ⟩

theorem tail_cons (a : α) : Π (v : vector α n), tail (a :: v) = v
| ⟨ l, h ⟩ := rfl

def to_list : vector α n → list α | ⟨ l, h ⟩ := l

def append {n m : nat} : vector α n → vector α m → vector α (n + m)
| ⟨ l₁, h₁ ⟩ ⟨ l₂, h₂ ⟩ := ⟨ l₁ ++ l₂, by simp_using_hs ⟩

/- map -/

def map (f : α → β) : vector α n → vector β n
| ⟨ l, h ⟩  := ⟨ list.map f l, by simp_using_hs ⟩

@[simp] lemma map_nil (f : α → β) : map f nil = nil := rfl

lemma map_cons (f : α → β) (a : α) : Π (v : vector α n), map f (a::v) = f a :: map f v
| ⟨l,h⟩ := rfl

def map₂ (f : α → β → φ) : vector α n → vector β n → vector φ n
| ⟨ x, _ ⟩ ⟨ y, _ ⟩ := ⟨ list.map₂ f x y, by simp_using_hs ⟩

def repeat (a : α) (n : ℕ) : vector α n :=
⟨ list.repeat a n, list.length_repeat a n ⟩

def dropn (i : ℕ) : vector α n → vector α (n - i)
| ⟨l, p⟩ := ⟨ list.dropn i l, by simp_using_hs ⟩

def taken (i : ℕ) : vector α n → vector α (min i n)
| ⟨l, p⟩ := ⟨ list.taken i l, by simp_using_hs ⟩

section accum
  open prod
  variable {σ : Type}

  def map_accumr (f : α → σ → σ × β) : vector α n → σ → σ × vector β n
  | ⟨ x, px ⟩ c :=
    let res := list.map_accumr f x c in
    ⟨ res.1, res.2, by simp_using_hs ⟩

  def map_accumr₂ {α β σ φ : Type} (f : α → β → σ → σ × φ)
   : vector α n → vector β n → σ → σ × vector φ n
  | ⟨ x, px ⟩ ⟨ y, py ⟩ c :=
    let res := list.map_accumr₂ f x y c in
    ⟨ res.1, res.2, by simp_using_hs ⟩

end accum

protected lemma eq {n : ℕ} : ∀ (a1 a2 : vector α n), to_list a1 = to_list a2 → a1 = a2
| ⟨x, h1⟩ ⟨.x, h2⟩ rfl := rfl


@[simp] lemma to_list_nil : to_list [] = @list.nil α :=
rfl

@[simp] lemma to_list_cons (a : α) (v : vector α n) : to_list (a :: v) = a :: to_list v :=
begin cases v, reflexivity end

@[simp] lemma to_list_append {n m : ℕ} (v : vector α n) (w : vector α m) : to_list (append v w) = to_list v ++ to_list w :=
begin cases v, cases w, reflexivity end

@[simp] lemma to_list_dropn {n m : ℕ} (v : vector α m) : to_list (dropn n v) = list.dropn n (to_list v) :=
begin cases v, reflexivity end

@[simp] lemma to_list_taken {n m : ℕ} (v : vector α m) : to_list (taken n v) = list.taken n (to_list v) :=
begin cases v, reflexivity end

def take_le (n : ℕ) (l : list α) (p : n ≤ list.length l) : vector α n :=
  ⟨list.taken n l, eq.trans (list.length_taken n l) (min_eq_left p)⟩

lemma to_list_take_le (n : ℕ) (l : list α) (p : n ≤ list.length l) : to_list (take_le n l p) = list.taken n l := rfl

-- 'bounded_chunk_list n m l' splits 'l' into at most 'n' 'm'-element chunks.
definition bounded_chunk_list : Π(n m : ℕ), list α → list (vector α m)
| nat.zero m l := list.nil
| (nat.succ n) m l :=
  if p : list.length l ≥ m then
    list.cons (take_le m l p) (bounded_chunk_list n m (list.dropn m l))
  else
    list.nil

lemma bounded_chunk_list_zero (m : ℕ) (l : list α) : bounded_chunk_list 0 m l = [] := rfl

lemma bounded_chunk_list_succ_next (n m : ℕ) (l : list α) (p : list.length l ≥ m)
: bounded_chunk_list (nat.succ n) m l = list.cons (take_le m l p) (bounded_chunk_list n m (list.dropn m l)) :=
begin
  unfold bounded_chunk_list,
  rw [dif_pos p]
end

lemma length_bounded_chunk_list : ∀(n m : ℕ) (l : list α), (list.length l = m * n) → list.length (bounded_chunk_list n m l) = n
| nat.zero m t  :=
  begin
    intros,
    simp [bounded_chunk_list_zero],
  end
| (nat.succ n) m t :=
  if p : list.length t ≥ m then
    begin
      rw [nat.mul_succ],
      intro h,
      assert q : list.length (list.dropn m t) = m * n,
         { rw [list.length_dropn, h, nat.add_sub_cancel] },
      unfold bounded_chunk_list,
      rw [dif_pos p],
      simp [length_bounded_chunk_list n m _ q]
    end
  else
    begin
      simp [nat.mul_succ],
      intro h,
      assert t_ge : list.length t ≥ m,
        { rw [h], apply nat.le_add_right },
      contradiction
    end

/- join -/

theorem length_to_list {n : ℕ} : ∀ l : vector α n, list.length (to_list l) = n
| ⟨ l, h ⟩ := h

definition join_list : list (vector α m) → list α
| list.nil := list.nil
| (list.cons a v) := list.append (to_list a) (join_list v)

theorem length_join_list : ∀ l : list (vector α m), list.length (join_list l) = m * list.length l
| list.nil := rfl
| (list.cons a v) := calc
  list.length (list.append (to_list a) (join_list v))
        = list.length (to_list a) + list.length (join_list v) : list.length_append (to_list a) (join_list v)
    ... = m + list.length (join_list v) : congr_arg (λ i, i + list.length (join_list v)) (length_to_list a)
    ... = m + m * list.length v         : congr_arg (λ i, m + i) (length_join_list v)
    ... = m * list.length v + m         : nat.add_comm _ _

definition join : vector (vector α m) n → vector α (m * n)
| ⟨ l, h ⟩ :=
  let p := calc
     list.length (join_list l)
           = m * list.length l : length_join_list l
       ... = m * n : congr_arg (λ i, m * i) h
  in ⟨ join_list l, p ⟩

@[simp]
lemma to_list_join : ∀ x : vector (vector α m) n, to_list (join x) = join_list (to_list x)
| ⟨ l, h ⟩ := rfl

/- split -/

definition split_vector {m : ℕ} : Π(n : ℕ), vector α (m * n) → list (vector α m)
| n ⟨ l, p ⟩ := bounded_chunk_list n m l

theorem length_split_vector {m : ℕ} : ∀ (n : ℕ) (t : vector α (m * n)), (split_vector n t)^.length = n
| n ⟨ l, p ⟩ :=
begin
  unfold split_vector,
  simp [length_bounded_chunk_list n m l p]
end

definition split : Π {n : ℕ}, vector α (m * n) → vector (vector α m) n
| n v := ⟨ split_vector n v, length_split_vector n v ⟩

/- join_list & split_list -/

theorem join_list_of_bounded_chunk_list
: ∀ (n m) (l : list α) (p : list.length l = m * n), vector.join_list (vector.bounded_chunk_list n m l) = l
| 0 m l :=
begin
  unfold bounded_chunk_list,
  simp [nat.mul_zero],
  intros,
  cases l, refl, contradiction,
end
| (nat.succ n) m l :=
if q : list.length l ≥ m then
begin
  unfold bounded_chunk_list,
  rw [dif_pos q],
  unfold join_list,
  intros,
  assert h : list.length (list.dropn m l) = m * n,
    { rw [list.length_dropn, p, nat.mul_succ,nat.add_sub_cancel]
    },
  simp [join_list_of_bounded_chunk_list _ _ _ h, to_list_take_le],
  exact (list.append_taken_dropn _ _)
end
else
begin
  rw [nat.mul_succ],
  intro p,
  -- Assert contradiction
  assert t_ge : list.length l ≥ m, { rw p, apply nat.le_add_left },
  contradiction
end

theorem join_list_of_split_list
: ∀ (t : vector α (m * n)), join_list (split_vector n t) = t^.to_list
| ⟨l, p⟩ :=
  begin
    unfold split_vector,
    apply join_list_of_bounded_chunk_list,
    exact p
  end

end vector
