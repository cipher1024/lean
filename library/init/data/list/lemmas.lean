/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn
-/
prelude
import init.data.list.basic init.function init.meta init.data.nat.lemmas
import init.meta.interactive init.meta.smt.rsimp

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

namespace list
open nat

/- append -/

@[simp] lemma nil_append (s : list α) : [] ++ s = s :=
rfl

@[simp] lemma cons_append (x : α) (s t : list α) : (x::s) ++ t = x::(s ++ t) :=
rfl

@[simp] lemma append_nil (t : list α) : t ++ [] = t :=
by induction t; simph

@[simp] lemma append_assoc (s t u : list α) : s ++ t ++ u = s ++ (t ++ u) :=
by induction s; simph

lemma append_ne_nil_of_ne_nil_left (s t : list α) : s ≠ [] → s ++ t ≠ nil :=
by induction s; intros; contradiction

lemma append_ne_nil_of_ne_nil_right (s t : list α) : t ≠ [] → s ++ t ≠ nil :=
by induction s; intros; contradiction

/- concat -/

@[simp] lemma concat_eq_append (a : α) (l : list α) : concat l a = l ++ [a] :=
by induction l; simph [concat]

lemma concat_append
: ∀ (x : list α) (e : α) (y : list α), concat x e ++ y = x ++ e :: y
| nil e y := rfl
| (cons a x) e y :=
begin
unfold concat,
simp [cons_append, concat_append x e y]
end

/- null -/

def null (xs : list α) : Prop := xs = nil

instance null_decidable : ∀ xs : list α, decidable (null xs)
   | nil := is_true rfl
   | (x :: xs) := is_false $ by contradiction

lemma null_iff_eq_nil (xs : list α) : null xs ↔ xs = nil :=
by refl

@[simp]
lemma null_nil : null (@nil α) ↔ true :=
begin 
  apply iff_true_intro,
  simp [null_iff_eq_nil]
end

@[simp]
lemma null_cons (x : α) (xs : list α) : null (x :: xs) ↔ false :=
begin 
  apply iff_false_intro,
  contradiction
end

lemma null_of_null_append_left {xs ys : list α}
: null (xs ++ ys) → null xs :=
begin
  intro h,
  cases xs with x xs,
  { rw null_iff_eq_nil },
  { simp [null_iff_eq_nil] at h, contradiction }
end

lemma null_of_null_append_right {xs ys : list α}
: null (xs ++ ys) → null ys :=
begin
  intro h,
  cases ys with y ys,
  { rw null_iff_eq_nil },
  { simp [null_iff_eq_nil] at h,
    rw -concat_append at h,
    { cases xs ; unfold concat at h ; contradiction } }
end

lemma null_append {xs ys : list α}
: null xs → null ys → null (xs ++ ys) :=
begin
  unfold null,
  intros Hxs Hys,
  subst xs, subst ys,
  simp
end

/- head & tail -/

attribute [simp] head tail

@[simp] lemma head_append [h : inhabited α] (t : list α) {s : list α} (h : s ≠ []) : head (s ++ t) = head s :=
by {induction s, contradiction, simp}

lemma cons_head_tail [h : inhabited α] {l : list α} (h : l ≠ []) : (head l)::(tail l) = l :=
by {induction l, contradiction, simp}

/- repeat taken dropn -/

attribute [simp] repeat taken dropn

/- length -/

attribute [simp] length

lemma length_nil : length (@nil α) = 0 :=
rfl

lemma length_cons (a : α) (l : list α) : length (a :: l) = length l + 1 :=
rfl

@[simp] lemma length_append (s t : list α) : length (s ++ t) = length s + length t :=
by induction s; simph

lemma length_concat (a : α) (l : list α) : length (concat l a) = succ (length l) :=
by simp

@[simp] lemma length_repeat (a : α) (n : ℕ) : length (repeat a n) = n :=
by induction n; simph

lemma eq_nil_of_length_eq_zero {l : list α} : length l = 0 → l = [] :=
by {induction l; intros, refl, contradiction}

lemma ne_nil_of_length_eq_succ {l : list α} : ∀ {n : nat}, length l = succ n → l ≠ [] :=
by induction l; intros; contradiction

-- TODO(Leo): cleanup proof after arith dec proc
@[simp] lemma length_taken : ∀ (i : ℕ) (l : list α), length (taken i l) = min i (length l)
| 0        l      := by simp
| (succ n) []     := by simp
| (succ n) (a::l) := by simph [nat.min_succ_succ]; rw [-add_one_eq_succ]; simp

-- TODO(Leo): cleanup proof after arith dec proc
@[simp] lemma length_dropn : ∀ (i : ℕ) (l : list α), length (dropn i l) = length l - i
| 0 l         := rfl
| (succ i) [] := eq.symm (nat.zero_sub_eq_zero (succ i))
| (succ i) (x::l) := calc
  length (dropn (succ i) (x::l))
          = length l - i             : length_dropn i l
      ... = succ (length l) - succ i : nat.sub_eq_succ_sub_succ (length l) i

/- taken -/

@[simp]
theorem taken_zero (xs : list α) : taken 0 xs = [] := rfl

@[simp]
theorem taken_nil : ∀ (n : ℕ), taken n list.nil = @list.nil α
| 0 := by refl
| (nat.succ n) := by refl

@[simp]
theorem taken_succ_cons (n : ℕ) (x : α) (xs : list α) : taken (nat.succ n) (x :: xs) = x :: taken n xs := rfl

@[simp]
theorem taken_length_self : ∀ (xs : list α), taken (length xs) xs = xs
| nil := by refl
| (cons x xs) := by simp [taken_succ_cons, taken_length_self]

@[simp]
theorem taken_append : ∀(n : ℕ) (xs ys : list α), taken n (xs ++ ys) = taken n xs ++ taken (n - length xs) ys
| 0 xs ys := by simp [nat.zero_sub, taken_zero]
| (nat.succ n) nil ys :=
begin
  simp [nil_append, taken_nil]
end
| (nat.succ n) (x :: xs) ys :=
begin
  simp [cons_append, taken_succ_cons],
  simp [taken_append, cons_append, nat.succ_sub_succ]
end

theorem taken_length_append (xs ys : list α) 
: list.taken (list.length xs) (xs ++ ys) = xs :=
by simp [nat.sub_self, list.append_nil]

/- dropn -/

@[simp]
theorem dropn_zero (l : list α)
: dropn 0 l = l := rfl

@[simp]
theorem dropn_nil 
: ∀ (n : ℕ), dropn n nil = (nil : list α)
| 0 := rfl
| (nat.succ n) := rfl

@[simp]
theorem dropn_succ_cons (n : ℕ) (e : α) (l : list α)
: dropn (nat.succ n) (e :: l) = dropn n l := rfl

@[simp]
theorem dropn_length_self : ∀ (xs : list α), dropn (length xs) xs = []
| nil := by refl
| (cons x xs) := by simp [dropn_succ_cons, dropn_length_self]

@[simp]
theorem dropn_append : ∀(n : ℕ) (xs ys : list α), dropn n (xs ++ ys) = dropn n xs ++ dropn (n - length xs) ys
| 0 xs ys := by simp [nat.zero_sub, dropn_zero]
| (nat.succ n) nil ys :=
begin
  simp [nil_append, dropn_nil]
 end
| (nat.succ n) (x :: xs) ys :=
begin
  simp [cons_append, dropn_succ_cons],
  simp [dropn_append, nat.succ_sub_succ]
 end

theorem dropn_length_append (xs ys : list α) 
: list.dropn (list.length xs) (xs ++ ys) = ys :=
by simp [nat.sub_self]

/- taken / dropn -/

theorem append_taken_dropn : ∀ (n : ℕ) (l : list α), taken n l ++ dropn n l = l
| 0            l          := rfl
| (nat.succ n) nil        := rfl
| (nat.succ n) (cons a l) := congr_arg (cons a) (append_taken_dropn n l)

/- repeat -/

@[simp]
theorem repeat_zero (e : α)
: repeat e 0 = nil := rfl

section nat

open nat

theorem repeat_append_cons (x : α) (l : list α)
: ∀ n, repeat x n ++ (x :: l) = repeat x (succ n) ++ l
  | 0 := by refl
  | (succ n) := calc
    repeat x (succ n) ++ (x::l) = x :: (repeat x n ++ (x::l))   : rfl
                     ...        = x :: (repeat x (succ n) ++ l) : by rw repeat_append_cons n
                     ...        = repeat x (succ $ succ n) ++ l : rfl

theorem append_repeat (x : α) (n : ℕ) : repeat x n ++ [x] = repeat x (succ n) :=
by simp [ repeat_append_cons x nil n, append_nil ]


end nat

/- map -/

attribute [simp] map

@[simp]
lemma map_nil (f : α → β) : map f [] = [] :=
rfl

lemma map_cons (f : α → β) (a l) : map f (a::l) = f a :: map f l :=
rfl

@[simp] lemma map_append (f : α → β) : ∀ l₁ l₂, map f (l₁ ++ l₂) = (map f l₁) ++ (map f l₂) :=
by intro l₁; induction l₁; intros; simph

lemma map_singleton (f : α → β) (a : α) : map f [a] = [f a] :=
rfl

lemma map_concat (f : α → β) (a : α) (l : list α) : map f (concat l a) = concat (map f l) (f a) :=
by induction l; simph

@[simp] lemma map_id (l : list α) : map id l = l :=
by induction l; simph

lemma map_id' {f : α → α} (h : ∀ x, f x = x) (l : list α) : map f l = l :=
by induction l; simph

@[simp] lemma map_map (g : β → γ) (f : α → β) (l : list α) : map g (map f l) = map (g ∘ f) l :=
by induction l; simph

@[simp] lemma length_map (f : α → β) (l : list α) : length (map f l) = length l :=
by induction l; simph

/- map₂ -/

attribute [simp] map₂

@[simp] lemma length_map₂ (f : α → β → γ) (l₁) : ∀ l₂, length (map₂ f l₁ l₂) = min (length l₁) (length l₂) :=
by {induction l₁; intro l₂; cases l₂; simph [add_one_eq_succ, min_succ_succ]}

/- reverse -/

@[simp] lemma reverse_nil : reverse (@nil α) = [] :=
rfl

local attribute [simp] reverse_core

@[simp] lemma reverse_cons (a : α) (l : list α) : reverse (a::l) = concat (reverse l) a :=
have aux : ∀ l₁ l₂, reverse_core l₁ (concat l₂ a) = concat (reverse_core l₁ l₂) a,
  by intros l₁; induction l₁; intros; rsimp,
aux l nil

@[simp] lemma reverse_singleton (a : α) : reverse [a] = [a] :=
rfl

@[simp] lemma reverse_append (s t : list α) : reverse (s ++ t) = (reverse t) ++ (reverse s) :=
by induction s; simph

@[simp] lemma reverse_reverse (l : list α) : reverse (reverse l) = l :=
by induction l; simph

lemma concat_eq_reverse_cons (a : α) (l : list α) : concat l a = reverse (a :: reverse l) :=
by induction l; simph

@[simp] lemma length_reverse (l : list α) : length (reverse l) = length l :=
by induction l; simph

@[simp] lemma map_reverse (f : α → β) (l : list α) : map f (reverse l) = reverse (map f l) :=
by induction l; simph

theorem reverse_to_cons : ∀ (x : α) (xs : list α), reverse (xs ++ [x]) = x :: reverse xs
:= begin intros x xs, rw reverse_append, refl end

/- last -/

attribute [simp] last

@[simp] lemma last_cons {a : α} {l : list α} : ∀ (h₁ : a :: l ≠ nil) (h₂ : l ≠ nil), last (a :: l) h₁ = last l h₂ :=
by {induction l; intros, contradiction, simph}

@[simp] lemma last_append {a : α} (l : list α) (h : l ++ [a] ≠ []) : last (l ++ [a]) h = a :=
begin
  induction l with hd tl ih; rsimp,
  assert haux : tl ++ [a] ≠ [],
    {apply append_ne_nil_of_ne_nil_right, contradiction},
  simph
end

lemma last_concat {a : α} (l : list α) (h : concat l a ≠ []) : last (concat l a) h = a :=
by simph

/- nth -/

attribute [simp] nth

lemma nth_succ (a : α) (l : list α) (n : nat) : nth (a::l) (nat.succ n) = nth l n :=
rfl

/- mem -/

@[simp] lemma mem_nil_iff (a : α) : a ∈ ([] : list α) ↔ false :=
iff.rfl

@[simp] lemma not_mem_nil (a : α) : a ∉ ([] : list α) :=
iff.mp $ mem_nil_iff a

@[simp] lemma mem_cons_self (a : α) (l : list α) : a ∈ a :: l :=
or.inl rfl

@[simp] lemma mem_cons_iff (a y : α) (l : list α) : a ∈ y :: l ↔ (a = y ∨ a ∈ l) :=
iff.rfl

@[rsimp] lemma mem_cons_eq (a y : α) (l : list α) : (a ∈ y :: l) = (a = y ∨ a ∈ l) :=
rfl

lemma eq_nil_of_forall_not_mem : ∀ {l : list α}, (∀ a, a ∉ l) → l = nil
| []        := assume h, rfl
| (b :: l') := assume h, absurd (mem_cons_self b l') (h b)

lemma mem_cons_of_mem (y : α) {a : α} {l : list α} : a ∈ l → a ∈ y :: l :=
assume H, or.inr H

lemma eq_or_mem_of_mem_cons {a y : α} {l : list α} : a ∈ y::l → a = y ∨ a ∈ l :=
assume h, h

lemma mem_singleton {a b : α} : a ∈ [b] → a = b :=
suppose a ∈ [b], or.elim (eq_or_mem_of_mem_cons this)
  (suppose a = b, this)
  (suppose a ∈ [], absurd this (not_mem_nil a))

@[simp] lemma mem_singleton_iff (a b : α) : a ∈ [b] ↔ a = b :=
iff.intro mem_singleton (begin intro h, simp [h] end)

lemma mem_of_mem_cons_of_mem {a b : α} {l : list α} : a ∈ b::l → b ∈ l → a ∈ l :=
assume ainbl binl, or.elim (eq_or_mem_of_mem_cons ainbl)
  (suppose a = b, begin subst a, exact binl end)
  (suppose a ∈ l, this)

lemma mem_or_mem_of_mem_append {a : α} : ∀ {s t : list α}, a ∈ s ++ t → a ∈ s ∨ a ∈ t
| []     t h := or.inr h
| (b::s) t h :=
  have a = b ∨ a ∈ s ++ t, from h,
  match this with
  | or.inl h₁ := or.inl (h₁ ▸ mem_cons_self _ _)
  | or.inr h₁ :=
    have a ∈ s ∨ a ∈ t, from mem_or_mem_of_mem_append h₁,
    match this with
    | or.inl h₂ := or.inl (mem_cons_of_mem _ h₂)
    | or.inr h₂ := or.inr h₂
    end
  end

lemma mem_append_of_mem_or_mem {a : α} {s t : list α} : a ∈ s ∨ a ∈ t → a ∈ s ++ t :=
list.induction_on s
  (take h, or.elim h false.elim id)
  (take b s,
    assume ih : a ∈ s ∨ a ∈ t → a ∈ s ++ t,
    suppose a ∈ b::s ∨ a ∈ t,
      or.elim this
        (suppose a ∈ b::s,
          or.elim (eq_or_mem_of_mem_cons this)
            (suppose a = b, or.inl this)
            (suppose a ∈ s, or.inr (ih (or.inl this))))
        (suppose a ∈ t, or.inr (ih (or.inr this))))

@[simp] lemma mem_append_iff (a : α) (s t : list α) : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t :=
iff.intro mem_or_mem_of_mem_append mem_append_of_mem_or_mem

@[rsimp] lemma mem_append_eq (a : α) (s t : list α) : (a ∈ s ++ t) = (a ∈ s ∨ a ∈ t) :=
propext $ mem_append_iff a s t

lemma not_mem_of_not_mem_append_left {a : α} {s t : list α} : a ∉ s++t → a ∉ s :=
λ nainst ains, absurd (mem_append_of_mem_or_mem (or.inl ains)) nainst

lemma not_mem_of_not_mem_append_right {a : α} {s t : list α} : a ∉ s++t → a ∉ t :=
λ nainst aint, absurd (mem_append_of_mem_or_mem (or.inr aint)) nainst

lemma not_mem_append {a : α} {s t : list α} : a ∉ s → a ∉ t → a ∉ s++t :=
λ nains naint ainst, or.elim (mem_or_mem_of_mem_append ainst)
  (λ ains, by contradiction)
  (λ aint, by contradiction)

lemma length_pos_of_mem {a : α} : ∀ {l : list α}, a ∈ l → 0 < length l
| []     := suppose a ∈ [], begin simp at this, contradiction end
| (b::l) := suppose a ∈ b::l, nat.zero_lt_succ _

lemma mem_split {a : α} {l : list α} : a ∈ l → ∃ s t : list α, l = s ++ (a::t) :=
list.induction_on l
  (suppose a ∈ [], begin simp at this, contradiction end)
  (take b l,
    assume ih : a ∈ l → ∃ s t : list α, l = s ++ (a::t),
    suppose a ∈ b::l,
    or.elim (eq_or_mem_of_mem_cons this)
      (suppose a = b, ⟨[], l, begin rw this, reflexivity end⟩)
      (suppose a ∈ l,
        match (ih this) with
        | ⟨s, t, (h : l = s ++ (a::t))⟩ := ⟨b::s, t, begin rw h, reflexivity end⟩
        end))

lemma mem_append_left {a : α} {l₁ : list α} (l₂ : list α) : a ∈ l₁ → a ∈ l₁ ++ l₂ :=
assume ainl₁, mem_append_of_mem_or_mem (or.inl ainl₁)

lemma mem_append_right {a : α} (l₁ : list α) {l₂ : list α} : a ∈ l₂ → a ∈ l₁ ++ l₂ :=
assume ainl₂, mem_append_of_mem_or_mem (or.inr ainl₂)

lemma mem_of_ne_of_mem {a y : α} {l : list α} (h₁ : a ≠ y) (h₂ : a ∈ y :: l) : a ∈ l :=
or.elim (eq_or_mem_of_mem_cons h₂) (λe, absurd e h₁) (λr, r)

lemma ne_of_not_mem_cons {a b : α} {l : list α} : a ∉ b::l → a ≠ b :=
assume nin aeqb, absurd (or.inl aeqb) nin

lemma not_mem_of_not_mem_cons {a b : α} {l : list α} : a ∉ b::l → a ∉ l :=
assume nin nainl, absurd (or.inr nainl) nin

lemma not_mem_cons_of_ne_of_not_mem {a y : α} {l : list α} : a ≠ y → a ∉ l → a ∉ y::l :=
assume p1 p2, not.intro (assume Pain, absurd (eq_or_mem_of_mem_cons Pain) (not_or p1 p2))

lemma ne_and_not_mem_of_not_mem_cons {a y : α} {l : list α} : a ∉ y::l → a ≠ y ∧ a ∉ l :=
assume p, and.intro (ne_of_not_mem_cons p) (not_mem_of_not_mem_cons p)

-- TODO(Jeremy): move this to data/list/set.lean

definition sublist (l₁ l₂ : list α) := ∀ ⦃a : α⦄, a ∈ l₁ → a ∈ l₂

instance : has_subset (list α) := ⟨sublist⟩

@[simp] lemma nil_subset (l : list α) : [] ⊆ l :=
λ b i, false.elim (iff.mp (mem_nil_iff b) i)

@[simp] lemma subset.refl (l : list α) : l ⊆ l :=
λ b i, i

lemma subset.trans {l₁ l₂ l₃ : list α} (h₁ : l₁ ⊆ l₂) (h₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ :=
λ b i, h₂ (h₁ i)

@[simp] lemma subset_cons (a : α) (l : list α) : l ⊆ a::l :=
λ b i, or.inr i

lemma subset_of_cons_subset {a : α} {l₁ l₂ : list α} : a::l₁ ⊆ l₂ → l₁ ⊆ l₂ :=
λ s b i, s (mem_cons_of_mem _ i)

lemma cons_subset_cons  {l₁ l₂ : list α} (a : α) (s : l₁ ⊆ l₂) : (a::l₁) ⊆ (a::l₂) :=
λ b hin, or.elim (eq_or_mem_of_mem_cons hin)
  (λ e : b = a,  or.inl e)
  (λ i : b ∈ l₁, or.inr (s i))

@[simp] lemma subset_append_left (l₁ l₂ : list α) : l₁ ⊆ l₁++l₂ :=
λ b i, iff.mpr (mem_append_iff b l₁ l₂) (or.inl i)

@[simp] lemma subset_append_right (l₁ l₂ : list α) : l₂ ⊆ l₁++l₂ :=
λ b i, iff.mpr (mem_append_iff b l₁ l₂) (or.inr i)

lemma subset_cons_of_subset (a : α) {l₁ l₂ : list α} : l₁ ⊆ l₂ → l₁ ⊆ (a::l₂) :=
λ (s : l₁ ⊆ l₂) (a : α) (i : a ∈ l₁), or.inr (s i)

lemma subset_app_of_subset_left (l l₁ l₂ : list α) : l ⊆ l₁ → l ⊆ l₁++l₂ :=
λ (s : l ⊆ l₁) (a : α) (ainl : a ∈ l),
  have a ∈ l₁, from s ainl,
  mem_append_of_mem_or_mem (or.inl this)

lemma subset_app_of_subset_right (l l₁ l₂ : list α) : l ⊆ l₂ → l ⊆ l₁++l₂ :=
λ (s : l ⊆ l₂) (a : α) (ainl : a ∈ l),
  have a ∈ l₂, from s ainl,
  mem_append_of_mem_or_mem (or.inr this)

lemma cons_subset_of_subset_of_mem {a : α} {l m : list α} (ainm : a ∈ m) (lsubm : l ⊆ m) :
  a::l ⊆ m :=
take b, suppose b ∈ a::l,
or.elim (eq_or_mem_of_mem_cons this)
  (suppose b = a, begin subst b, exact ainm end)
  (suppose b ∈ l, lsubm this)

lemma app_subset_of_subset_of_subset {l₁ l₂ l : list α} (l₁subl : l₁ ⊆ l) (l₂subl : l₂ ⊆ l) :
  l₁ ++ l₂ ⊆ l :=
take a, suppose a ∈ l₁ ++ l₂,
or.elim (mem_or_mem_of_mem_append this)
  (suppose a ∈ l₁, l₁subl this)
  (suppose a ∈ l₂, l₂subl this)

/- foldr -/

section foldr

variable f : α → β → β

@[simp]
theorem foldr_nil (i : β) :
  foldr f i nil = i
:= rfl

@[simp]
theorem foldr_cons (i : β) (x : α) (xs : list α) :
  foldr f i (x :: xs) = f x (foldr f i xs)
:= rfl

theorem foldr_append (f : α → β → β) :
  ∀ (b : β) (l₁ l₂ : list α), foldr f b (l₁++l₂) = foldr f (foldr f b l₂) l₁
| b nil         l₂ := rfl
| b (cons a l₁) l₂ := congr_arg (f a) (foldr_append b l₁ l₂)

end foldr

section foldr_ac

variable f : α → α → α
variable [is_associative α f]
variable [is_commutative α f]

theorem foldr_trade_ac (x x' : α) (xs : list α) :
  foldr f (f x x') xs = f x' (foldr f x xs) :=
begin
  induction xs with x'' xs,
  { unfold foldr, apply is_commutative.comm },
  { simp [ih_1],
    ac_refl  }
end

theorem foldr_reverse_ac (x : α) (xs : list α) :
  foldr f x (reverse xs) = foldr f x xs :=
begin
  induction xs with y ys,
  { refl },
  { simp [foldr_append],
    rw [is_commutative.comm f,foldr_trade_ac f,ih_1] }
end

theorem foldr_append_ac (x x₀ x₁ : α) (xs ys : list α)
  (h : f x₀ x₁ = x)
: foldr f x (xs ++ ys) = f (foldr f x₀ ys) (foldr f x₁ xs) :=
begin
  rw [-foldr_trade_ac f,-foldr_trade_ac f,foldr_append,h],
end

end foldr_ac

/- foldl -/

section foldl

variable f : β → α → β

@[simp]
theorem foldl_nil (i : β) :
  foldl f i nil = i
:= rfl

@[simp]
theorem foldl_cons (i : β) (x : α) (xs : list α) :
  foldl f i (x :: xs) = foldl f (f i x) xs
:= rfl

theorem foldl_append :
  ∀ (a : β) (l₁ l₂ : list α), foldl f a (l₁++l₂) = foldl f (foldl f a l₁) l₂
| a nil         l₂ := rfl
| a (cons b l₁) l₂ := foldl_append (f a b) l₁ l₂

end foldl

section foldl_ac

variable f : α → α → α
variable [is_associative α f]
variable [is_commutative α f]

theorem foldl_trade_ac (x x' : α) (xs : list α) :
  foldl f (f x x') xs = f x' (foldl f x xs) :=
begin
  revert x x',
  induction xs with x'' xs,
  { intros x x', unfold foldl, apply is_commutative.comm },
  { intros x x',
    assert h : f (f x x') x'' = f (f x x'') x',
    { ac_refl },
    simp [h,ih_1]  }
end

theorem foldl_reverse_ac (x : α) (xs : list α) :
  foldl f x (reverse xs) = foldl f x xs :=
begin
  induction xs with y ys,
  { refl },
  { simp [foldl_append,ih_1],
    rw [foldl_trade_ac f,is_commutative.comm f] }
end

lemma foldl_cons_ac (x x₀ : α) (xs : list α) :
  foldl f x₀ (x :: xs) = f x (foldl f x₀ xs)
:= by simp [foldl_trade_ac f]

theorem foldl_append_ac (x x₀ x₁ : α) (xs ys : list α)
  (h : f x₀ x₁ = x)
: foldl f x (xs ++ ys) = f (foldl f x₀ xs) (foldl f x₁ ys) :=
begin
  rw [-foldl_trade_ac f,-foldl_trade_ac f,foldl_append,h],
end

end foldl_ac

/- foldr / folrl -/

section foldl_to_foldr

variable f : α → β → α

theorem foldl_to_foldr (x : α) (xs : list β) :
  foldl f x xs = foldr (flip f) x (reverse xs) :=
begin
  revert x, induction xs with y ys H,
  { intro x, refl },
  { intro x,
    simp [H,foldr_append],
    refl, }
end

theorem foldl_to_cons (i : α) (x : β) (xs : list β) :
  foldl f i (xs ++ [x]) = f (foldl f i xs) x :=
begin
  simp [foldl_to_foldr], refl
end

end foldl_to_foldr

section foldl_to_foldr_ac

variable f : α → α → α
variable [is_associative α f]
variable [is_commutative α f]

theorem foldl_to_foldr_ac (x : α) (xs : list α) :
  foldl f x xs = foldr f x xs :=
begin
  revert x,
  induction xs with x' xs IH,
  { intro, refl },
  { intro x,
    unfold foldr foldl,
    rw -foldr_trade_ac f,
    apply IH }
end

end foldl_to_foldr_ac

/- map -/

lemma eq_nil_of_map_eq_nil {f : α → β} {l :list α} (h : map f l = nil) : l = nil :=
eq_nil_of_length_eq_zero (begin rw -(length_map f l), simp [h] end)

lemma mem_map (f : α → β) {a : α} {l : list α} (h : a ∈ l) : f a ∈ map f l :=
begin
  induction l with b l' ih,
  {simp at h, contradiction },
  {simp, simp at h, cases h with h h,
    {simph},
    {exact or.inr (ih h)}}
end

lemma exists_of_mem_map {f : α → β} {b : β} {l : list α} (h : b ∈ map f l) : ∃ a, a ∈ l ∧ f a = b :=
begin
  induction l with c l' ih,
  {simp at h, contradiction},
  {cases (eq_or_mem_of_mem_cons h) with h h,
    {existsi c, simp [h]},
    {cases ih h with a ha, cases ha with ha₁ ha₂,
      existsi a, simph }}
end

lemma eq_of_map_const {b₁ b₂ : β} : ∀ {l : list α}, b₁ ∈ map (function.const α b₂) l → b₁ = b₂
| []     h := absurd h (not_mem_nil b₁)
| (a::l) h :=
  or.elim (eq_or_mem_of_mem_cons h)
    (suppose b₁ = b₂, this)
    (suppose b₁ ∈ map (function.const α b₂) l, eq_of_map_const this)

/- sum -/

  @[simp]
  lemma sum_nil [add_comm_monoid α] : sum (@nil α) = 0 := rfl

  @[simp]
  lemma sum_cons [add_comm_monoid α] (x : α) (xs : list α)
  : sum (x :: xs) = x + sum xs :=
  foldl_cons_ac add x 0 xs

  lemma sum_singleton [add_comm_monoid α] (x : α)
  : sum [x] = x :=
  by simp

  lemma sum_append [add_comm_monoid α] (xs ys : list α)
  : sum (xs ++ ys) = sum xs + sum ys :=
  foldl_append_ac add 0 0 0 xs ys $ zero_add _

  lemma sum_reverse [add_comm_monoid α] (xs : list α)
  : sum (reverse xs) = sum xs
  := foldl_reverse_ac add 0 xs

  lemma sum_eq_foldl [add_comm_monoid α] (xs : list α)
  : sum xs = foldl add 0 xs := rfl

  lemma sum_eq_foldr [add_comm_monoid α] (xs : list α)
  : sum xs = foldr add 0 xs :=
  by simp [sum_eq_foldl,foldl_to_foldr_ac]

  -- The following theorem looks like it should be applicable to xs : list α with
  --   [has_lift_t ℕ α]               -- to allow k * coe (length xs)
  --   [ordered_cancel_comm_monoid α]
  --   [distrib α]
  -- except that there is no rule saying:
  --   coe nat.zero = ordered_cancel_comm_monoid.zero
  lemma sum_le {k : ℕ} : ∀ {xs : list ℕ},
     (∀ i, i ∈ xs → i ≤ k) →
     sum xs ≤ k * length xs
   | nil _ := by simp
   | (x :: xs) h :=
   begin
     simp [left_distrib],
     -- x + sum xs ≤ k + k * length xs
     apply add_le_add,
     { -- x ≤ k
       apply h,
       apply or.inl rfl },
     { -- sum xs ≤ k * length xs
       apply sum_le,
       intros i h',
       apply h,
       apply or.inr h' },
   end

end list
