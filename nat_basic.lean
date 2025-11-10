/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
-/
module

prelude
public import Init.SimpLemmas
public import Init.Data.NeZero
public import Init.Grind.Tactics

public section

set_option linter.missingDocs true -- keep it documented
universe u

namespace Nat

/-- Compiled version of `Nat.rec` so that we can define `Nat.recAux` to be defeq to `Nat.rec`.
This is working around the fact that the compiler does not currently support recursors. -/
def recCompiled {motive : Nat → Sort u} (zero : motive zero) (succ : (n : Nat) → motive n → motive (Nat.succ n)) : (t : Nat) → motive t
  | .zero => zero
  | .succ n => succ n (recCompiled zero succ n)

@[csimp]
theorem rec_eq_recCompiled : @Nat.rec = @Nat.recCompiled :=
  funext fun _ => funext fun _ => funext fun succ => funext fun t =>
    Nat.recOn t rfl (fun n ih => congrArg (succ n) ih)

/--
A recursor for `Nat` that uses the notations `0` for `Nat.zero` and `n + 1` for `Nat.succ`.

It is otherwise identical to the default recursor `Nat.rec`. It is used by the `induction` tactic
by default for `Nat`.
-/
@[elab_as_elim, induction_eliminator]
protected abbrev recAux {motive : Nat → Sort u} (zero : motive 0) (succ : (n : Nat) → motive n → motive (n + 1)) (t : Nat) : motive t :=
  Nat.rec zero succ t

/--
A case analysis principle for `Nat` that uses the notations `0` for `Nat.zero` and `n + 1` for
`Nat.succ`.

It is otherwise identical to the default recursor `Nat.casesOn`. It is used as the default `Nat`
case analysis principle for `Nat` by the `cases` tactic.
-/
@[elab_as_elim, cases_eliminator]
protected abbrev casesAuxOn {motive : Nat → Sort u} (t : Nat) (zero : motive 0) (succ : (n : Nat) → motive (n + 1)) : motive t :=
  Nat.casesOn t zero succ


/--
Applies a function to a starting value the specified number of times.

In other words, `f` is iterated `n` times on `a`.

Examples:
* `Nat.repeat f 3 a = f <| f <| f <| a`
* `Nat.repeat (· ++ "!") 4 "Hello" = "Hello!!!!"`
-/
@[specialize, expose] def repeat {α : Type u} (f : α → α) : (n : Nat) → (a : α) → α
  | 0,      a => a
  | succ n, a => f (repeat f n a)

/--
Applies a function to a starting value the specified number of times.

In other words, `f` is iterated `n` times on `a`.

This is a tail-recursive version of `Nat.repeat` that's used at runtime.

Examples:
* `Nat.repeatTR f 3 a = f <| f <| f <| a`
* `Nat.repeatTR (· ++ "!") 4 "Hello" = "Hello!!!!"`
-/
@[inline] def repeatTR {α : Type u} (f : α → α) (n : Nat) (a : α) : α :=
  let rec @[specialize] loop
    | 0,      a => a
    | succ n, a => loop n (f a)
  loop n a

/--
The Boolean less-than comparison on natural numbers.

This function is overridden in both the kernel and the compiler to efficiently evaluate using the
arbitrary-precision arithmetic library. The definition provided here is the logical model.

Examples:
 * `Nat.blt 2 5 = true`
 * `Nat.blt 5 2 = false`
 * `Nat.blt 5 5 = false`
-/
@[expose] def blt (a b : Nat) : Bool :=
  ble a.succ b

attribute [simp] Nat.zero_le
attribute [simp] Nat.not_lt_zero

theorem and_forall_add_one {p : Nat → Prop} : p 0 ∧ (∀ n, p (n + 1)) ↔ ∀ n, p n :=
  ⟨fun h n => Nat.casesOn n h.1 h.2, fun h => ⟨h _, fun _ => h _⟩⟩

theorem or_exists_add_one : p 0 ∨ (Exists fun n => p (n + 1)) ↔ Exists p :=
  ⟨fun h => h.elim (fun h0 => ⟨0, h0⟩) fun ⟨n, hn⟩ => ⟨n + 1, hn⟩,
    fun ⟨n, h⟩ => match n with | 0 => Or.inl h | n+1 => Or.inr ⟨n, h⟩⟩

/-! # Helper "packing" theorems -/

@[simp] theorem zero_eq : Nat.zero = 0 := rfl
@[simp] theorem add_eq : Nat.add x y = x + y := rfl
@[simp] theorem mul_eq : Nat.mul x y = x * y := rfl
@[simp] theorem sub_eq : Nat.sub x y = x - y := rfl
@[simp] theorem lt_eq : Nat.lt x y = (x < y) := rfl
@[simp] theorem le_eq : Nat.le x y = (x ≤ y) := rfl

/-! # Helper Bool relation theorems -/

@[simp] theorem beq_refl (a : Nat) : Nat.beq a a = true := by
  induction a with simp [Nat.beq]
  | succ a ih => simp [ih]

@[simp] theorem beq_eq : (Nat.beq x y = true) = (x = y) := propext <| Iff.intro Nat.eq_of_beq_eq_true (fun h => h ▸ (Nat.beq_refl x))
@[simp] theorem ble_eq : (Nat.ble x y = true) = (x ≤ y) := propext <| Iff.intro Nat.le_of_ble_eq_true Nat.ble_eq_true_of_le
@[simp] theorem blt_eq : (Nat.blt x y = true) = (x < y) := propext <| Iff.intro Nat.le_of_ble_eq_true Nat.ble_eq_true_of_le

instance : LawfulBEq Nat where
  eq_of_beq h := by simpa using h
  rfl := by simp [BEq.beq]

theorem beq_eq_true_eq (a b : Nat) : ((a == b) = true) = (a = b) := by simp
theorem not_beq_eq_true_eq (a b : Nat) : ((!(a == b)) = true) = ¬(a = b) := by simp

/-! # Nat.add theorems -/

@[simp] protected theorem zero_add : ∀ (n : Nat), 0 + n = n
  | 0   => rfl
  | n+1 => congrArg succ (Nat.zero_add n)
instance : Std.LawfulIdentity (α := Nat) (· + ·) 0 where
  left_id := Nat.zero_add
  right_id := Nat.add_zero

theorem succ_add : ∀ (n m : Nat), (succ n) + m = succ (n + m)
  | _, 0   => rfl
  | n, m+1 => congrArg succ (succ_add n m)

theorem add_succ (n m : Nat) : n + succ m = succ (n + m) :=
  rfl

theorem add_one (n : Nat) : n + 1 = succ n :=
  rfl

@[simp] theorem succ_eq_add_one (n : Nat) : succ n = n + 1 :=
  rfl

theorem add_one_ne_zero (n : Nat) : n + 1 ≠ 0 := nofun
theorem zero_ne_add_one (n : Nat) : 0 ≠ n + 1 := by simp

protected theorem add_comm : ∀ (n m : Nat), n + m = m + n
  | n, 0   => Eq.symm (Nat.zero_add n)
  | n, m+1 => by
    have : succ (n + m) = succ (m + n) := by apply congrArg; apply Nat.add_comm
    rw [succ_add m n]
    apply this
instance : Std.Commutative (α := Nat) (· + ·) := ⟨Nat.add_comm⟩

protected theorem add_assoc : ∀ (n m k : Nat), (n + m) + k = n + (m + k)
  | _, _, 0      => rfl
  | n, m, succ k => congrArg succ (Nat.add_assoc n m k)
instance : Std.Associative (α := Nat) (· + ·) := ⟨Nat.add_assoc⟩

protected theorem add_left_comm (n m k : Nat) : n + (m + k) = m + (n + k) := by
  rw [← Nat.add_assoc, Nat.add_comm n m, Nat.add_assoc]

protected theorem add_right_comm (n m k : Nat) : (n + m) + k = (n + k) + m := by
  rw [Nat.add_assoc, Nat.add_comm m k, ← Nat.add_assoc]

protected theorem add_left_cancel {n m k : Nat} : n + m = n + k → m = k := by
  induction n with
  | zero => simp
  | succ n ih => simp [succ_add, succ.injEq]; intro h; apply ih h

protected theorem add_right_cancel {n m k : Nat} (h : n + m = k + m) : n = k := by
  rw [Nat.add_comm n m, Nat.add_comm k m] at h
  apply Nat.add_left_cancel h

theorem eq_zero_of_add_eq_zero : ∀ {n m}, n + m = 0 → n = 0 ∧ m = 0
  | 0, 0, _ => ⟨rfl, rfl⟩
  | _+1, 0, h => Nat.noConfusion h

protected theorem eq_zero_of_add_eq_zero_left (h : n + m = 0) : m = 0 :=
  (Nat.eq_zero_of_add_eq_zero h).2

/-! # Nat.mul theorems -/

@[simp] protected theorem mul_zero (n : Nat) : n * 0 = 0 :=
  rfl

theorem mul_succ (n m : Nat) : n * succ m = n * m + n :=
  rfl

theorem mul_add_one (n m : Nat) : n * (m + 1) = n * m + n :=
  rfl

@[simp] protected theorem zero_mul : ∀ (n : Nat), 0 * n = 0
  | 0      => rfl
  | succ n => mul_succ 0 n ▸ (Nat.zero_mul n).symm ▸ rfl

theorem succ_mul (n m : Nat) : (succ n) * m = (n * m) + m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [mul_succ, add_succ, ih, mul_succ, add_succ, Nat.add_right_comm]

theorem add_one_mul (n m : Nat) : (n + 1) * m = (n * m) + m := succ_mul n m

protected theorem mul_comm : ∀ (n m : Nat), n * m = m * n
  | n, 0      => (Nat.zero_mul n).symm ▸ (Nat.mul_zero n).symm ▸ rfl
  | n, succ m => (mul_succ n m).symm ▸ (succ_mul m n).symm ▸ (Nat.mul_comm n m).symm ▸ rfl
instance : Std.Commutative (α := Nat) (· * ·) := ⟨Nat.mul_comm⟩

@[simp] protected theorem mul_one : ∀ (n : Nat), n * 1 = n :=
  Nat.zero_add

@[simp] protected theorem one_mul (n : Nat) : 1 * n = n :=
  Nat.mul_comm n 1 ▸ Nat.mul_one n
instance : Std.LawfulIdentity (α := Nat) (· * ·) 1 where
  left_id := Nat.one_mul
  right_id := Nat.mul_one

protected theorem left_distrib (n m k : Nat) : n * (m + k) = n * m + n * k := by
  induction n with
  | zero      => repeat rw [Nat.zero_mul]
  | succ n ih => simp [succ_mul, ih]; rw [Nat.add_assoc, Nat.add_assoc (n*m)]; apply congrArg; apply Nat.add_left_comm

protected theorem right_distrib (n m k : Nat) : (n + m) * k = n * k + m * k := by
  rw [Nat.mul_comm, Nat.left_distrib]; simp [Nat.mul_comm]

protected theorem mul_add (n m k : Nat) : n * (m + k) = n * m + n * k :=
  Nat.left_distrib n m k

protected theorem add_mul (n m k : Nat) : (n + m) * k = n * k + m * k :=
  Nat.right_distrib n m k

protected theorem mul_assoc : ∀ (n m k : Nat), (n * m) * k = n * (m * k)
  | _, _, 0      => rfl
  | n, m, succ k => by simp [mul_succ, Nat.mul_assoc n m k, Nat.left_distrib]
instance : Std.Associative (α := Nat) (· * ·) := ⟨Nat.mul_assoc⟩

protected theorem mul_left_comm (n m k : Nat) : n * (m * k) = m * (n * k) := by
  rw [← Nat.mul_assoc, Nat.mul_comm n m, Nat.mul_assoc]

protected theorem mul_two (n) : n * 2 = n + n := by rw [Nat.mul_succ, Nat.mul_one]
protected theorem two_mul (n) : 2 * n = n + n := by rw [Nat.succ_mul, Nat.one_mul]

/-! # Inequalities -/

attribute [simp] Nat.le_refl

theorem succ_lt_succ {n m : Nat} : n < m → succ n < succ m := succ_le_succ

theorem le_of_lt_add_one {n m : Nat} : n < m + 1 → n ≤ m := le_of_succ_le_succ

theorem lt_add_one_of_le {n m : Nat} : n ≤ m → n < m + 1 := succ_le_succ

@[simp] protected theorem sub_zero (n : Nat) : n - 0 = n := rfl

theorem not_add_one_le_zero (n : Nat) : ¬ n + 1 ≤ 0 := nofun

theorem not_add_one_le_self : (n : Nat) → ¬ n + 1 ≤ n := Nat.not_succ_le_self

theorem add_one_pos (n : Nat) : 0 < n + 1 := Nat.zero_lt_succ n

theorem pred_lt : ∀ {n : Nat}, n ≠ 0 → pred n < n
  | zero,   h => absurd rfl h
  | succ _, _ => lt_succ_of_le (Nat.le_refl _)

theorem sub_one_lt : ∀ {n : Nat}, n ≠ 0 → n - 1 < n := pred_lt

theorem sub_lt_of_lt {a b c : Nat} (h : a < c) : a - b < c :=
  Nat.lt_of_le_of_lt (Nat.sub_le _ _) h

theorem sub_succ (n m : Nat) : n - succ m = pred (n - m) := rfl

theorem succ_sub_succ (n m : Nat) : succ n - succ m = n - m :=
  succ_sub_succ_eq_sub n m

@[simp] protected theorem sub_self : ∀ (n : Nat), n - n = 0
  | 0        => by rw [Nat.sub_zero]
  | (succ n) => by rw [succ_sub_succ, Nat.sub_self n]

theorem sub_add_eq (a b c : Nat) : a - (b + c) = a - b - c := by
  induction c with
  | zero => simp
  | succ c ih => simp only [Nat.add_succ, Nat.sub_succ, ih]

protected theorem lt_of_lt_of_eq {n m k : Nat} : n < m → m = k → n < k :=
  fun h₁ h₂ => h₂ ▸ h₁

instance : Trans (. < . : Nat → Nat → Prop) (. < . : Nat → Nat → Prop) (. < . : Nat → Nat → Prop) where
  trans := Nat.lt_trans

instance : Trans (. ≤ . : Nat → Nat → Prop) (. ≤ . : Nat → Nat → Prop) (. ≤ . : Nat → Nat → Prop) where
  trans := Nat.le_trans

instance : Trans (. < . : Nat → Nat → Prop) (. ≤ . : Nat → Nat → Prop) (. < . : Nat → Nat → Prop) where
  trans := Nat.lt_of_lt_of_le

instance : Trans (. ≤ . : Nat → Nat → Prop) (. < . : Nat → Nat → Prop) (. < . : Nat → Nat → Prop) where
  trans := Nat.lt_of_le_of_lt

protected theorem le_of_eq {n m : Nat} (p : n = m) : n ≤ m :=
  p ▸ Nat.le_refl n

theorem lt.step {n m : Nat} : n < m → n < succ m := le_step

theorem le_of_succ_le {n m : Nat} (h : succ n ≤ m) : n ≤ m := Nat.le_trans (le_succ n) h
theorem lt_of_succ_lt      {n m : Nat} : succ n < m → n < m := le_of_succ_le
protected theorem le_of_lt {n m : Nat} : n < m → n ≤ m := le_of_succ_le

theorem lt_of_succ_lt_succ {n m : Nat} : succ n < succ m → n < m := le_of_succ_le_succ

theorem lt_of_succ_le {n m : Nat} (h : succ n ≤ m) : n < m := h
theorem succ_le_of_lt {n m : Nat} (h : n < m) : succ n ≤ m := h

theorem eq_zero_or_pos : ∀ (n : Nat), n = 0 ∨ n > 0
  | 0   => Or.inl rfl
  | _+1 => Or.inr (succ_pos _)

protected theorem pos_of_ne_zero {n : Nat} : n ≠ 0 → 0 < n := (eq_zero_or_pos n).resolve_left

theorem pos_of_neZero (n : Nat) [NeZero n] : 0 < n := Nat.pos_of_ne_zero (NeZero.ne _)

attribute [simp] Nat.lt_add_one

theorem lt.base (n : Nat) : n < succ n := Nat.le_refl (succ n)

protected theorem le_total (m n : Nat) : m ≤ n ∨ n ≤ m :=
  match Nat.lt_or_ge m n with
  | Or.inl h => Or.inl (Nat.le_of_lt h)
  | Or.inr h => Or.inr h

theorem eq_zero_of_le_zero {n : Nat} (h : n ≤ 0) : n = 0 := Nat.le_antisymm h (zero_le _)

theorem zero_lt_of_lt : {a b : Nat} → a < b → 0 < b
  | 0,   _, h => h
  | a+1, b, h =>
    have : a < b := Nat.lt_trans (Nat.lt_succ_self _) h
    zero_lt_of_lt this

theorem zero_lt_of_ne_zero {a : Nat} (h : a ≠ 0) : 0 < a := by
  match a with
  | 0 => contradiction
  | a+1 => apply Nat.zero_lt_succ

attribute [simp] Nat.lt_irrefl

theorem ne_of_lt {a b : Nat} (h : a < b) : a ≠ b := fun he => absurd (he ▸ h) (Nat.lt_irrefl a)

theorem le_or_eq_of_le_succ {m n : Nat} (h : m ≤ succ n) : m ≤ n ∨ m = succ n :=
  Decidable.byCases
    (fun (h' : m = succ n) => Or.inr h')
    (fun (h' : m ≠ succ n) =>
       have : m < succ n := Nat.lt_of_le_of_ne h h'
       have : succ m ≤ succ n := succ_le_of_lt this
       Or.inl (le_of_succ_le_succ this))

theorem le_or_eq_of_le_add_one {m n : Nat} (h : m ≤ n + 1) : m ≤ n ∨ m = n + 1 :=
  le_or_eq_of_le_succ h

@[simp] theorem le_add_right : ∀ (n k : Nat), n ≤ n + k
  | n, 0   => Nat.le_refl n
  | n, k+1 => le_succ_of_le (le_add_right n k)

@[simp] theorem le_add_left (n m : Nat): n ≤ m + n :=
  Nat.add_comm n m ▸ le_add_right n m

theorem le_of_add_right_le {n m k : Nat} (h : n + k ≤ m) : n ≤ m :=
  Nat.le_trans (le_add_right n k) h

theorem le_add_right_of_le {n m k : Nat} (h : n ≤ m) : n ≤ m + k :=
  Nat.le_trans h (le_add_right m k)

theorem le_of_add_left_le {n m k : Nat} (h : k + n ≤ m) : n ≤ m :=
  Nat.le_trans (le_add_left n k) h

theorem le_add_left_of_le {n m k : Nat} (h : n ≤ m) : n ≤ k + m :=
  Nat.le_trans h (le_add_left m k)

theorem lt_of_add_one_le {n m : Nat} (h : n + 1 ≤ m) : n < m := h

theorem add_one_le_of_lt {n m : Nat} (h : n < m) : n + 1 ≤ m := h

protected theorem lt_add_left (c : Nat) (h : a < b) : a < c + b :=
  Nat.lt_of_lt_of_le h (Nat.le_add_left ..)

protected theorem lt_add_right (c : Nat) (h : a < b) : a < b + c :=
  Nat.lt_of_lt_of_le h (Nat.le_add_right ..)

theorem lt_of_add_right_lt {n m k : Nat} (h : n + k < m) : n < m :=
  Nat.lt_of_le_of_lt (Nat.le_add_right ..) h

theorem lt_of_add_left_lt {n m k : Nat} (h : k + n < m) : n < m :=
  lt_of_add_right_lt (Nat.add_comm _ _ ▸ h)

theorem le.dest : ∀ {n m : Nat}, n ≤ m → Exists (fun k => n + k = m)
  | zero,   zero,   _ => ⟨0, rfl⟩
  | zero,   succ n, _ => ⟨succ n, Nat.add_comm 0 (succ n) ▸ rfl⟩
  | succ _, zero,   h => absurd h (not_succ_le_zero _)
  | succ n, succ m, h =>
    have : n ≤ m := Nat.le_of_succ_le_succ h
    have : Exists (fun k => n + k = m) := dest this
    match this with
    | ⟨k, h⟩ => ⟨k, show succ n + k = succ m from ((succ_add n k).symm ▸ h ▸ rfl)⟩

theorem le.intro {n m k : Nat} (h : n + k = m) : n ≤ m :=
  h ▸ le_add_right n k

protected theorem not_le_of_gt {n m : Nat} (h : n > m) : ¬ n ≤ m := fun h₁ =>
  match Nat.lt_or_ge n m with
  | Or.inl h₂ => absurd (Nat.lt_trans h h₂) (Nat.lt_irrefl _)
  | Or.inr h₂ =>
    have Heq : n = m := Nat.le_antisymm h₁ h₂
    absurd (@Eq.subst _ _ _ _ Heq h) (Nat.lt_irrefl m)
protected theorem not_le_of_lt : ∀{a b : Nat}, a < b → ¬(b ≤ a) := Nat.not_le_of_gt
protected theorem not_lt_of_ge : ∀{a b : Nat}, b ≥ a → ¬(b < a) := flip Nat.not_le_of_gt
protected theorem not_lt_of_le : ∀{a b : Nat}, a ≤ b → ¬(b < a) := flip Nat.not_le_of_gt
protected theorem lt_le_asymm : ∀{a b : Nat}, a < b → ¬(b ≤ a) := Nat.not_le_of_gt
protected theorem le_lt_asymm : ∀{a b : Nat}, a ≤ b → ¬(b < a) := flip Nat.not_le_of_gt

theorem gt_of_not_le {n m : Nat} (h : ¬ n ≤ m) : n > m := (Nat.lt_or_ge m n).resolve_right h
protected theorem lt_of_not_ge : ∀{a b : Nat}, ¬(b ≥ a) → b < a := Nat.gt_of_not_le

theorem ge_of_not_lt {n m : Nat} (h : ¬ n < m) : n ≥ m := (Nat.lt_or_ge n m).resolve_left h
protected theorem le_of_not_gt : ∀{a b : Nat}, ¬(b > a) → b ≤ a := Nat.ge_of_not_lt
protected theorem le_of_not_lt : ∀{a b : Nat}, ¬(a < b) → b ≤ a := Nat.ge_of_not_lt

theorem ne_of_gt {a b : Nat} (h : b < a) : a ≠ b := (ne_of_lt h).symm
protected theorem ne_of_lt' : ∀{a b : Nat}, a < b → b ≠ a := ne_of_gt

@[simp] protected theorem not_le {a b : Nat} : ¬ a ≤ b ↔ b < a :=
  Iff.intro Nat.gt_of_not_le Nat.not_le_of_gt
@[simp] protected theorem not_lt {a b : Nat} : ¬ a < b ↔ b ≤ a :=
  Iff.intro Nat.ge_of_not_lt (flip Nat.not_le_of_gt)

protected theorem le_of_not_le {a b : Nat} (h : ¬ b ≤ a) : a ≤ b := Nat.le_of_lt (Nat.not_le.1 h)
protected theorem le_of_not_ge : ∀{a b : Nat}, ¬(a ≥ b) → a ≤ b:= @Nat.le_of_not_le

protected theorem lt_trichotomy (a b : Nat) : a < b ∨ a = b ∨ b < a :=
  match Nat.lt_or_ge a b with
  | .inl h => .inl h
  | .inr h =>
    match Nat.eq_or_lt_of_le h with
    | .inl h => .inr (.inl h.symm)
    | .inr h => .inr (.inr h)

protected theorem lt_or_gt_of_ne {a b : Nat} (ne : a ≠ b) : a < b ∨ a > b :=
  match Nat.lt_trichotomy a b with
  | .inl h => .inl h
  | .inr (.inl e) => False.elim (ne e)
  | .inr (.inr h) => .inr h

protected theorem lt_or_lt_of_ne : ∀{a b : Nat}, a ≠ b → a < b ∨ b < a := Nat.lt_or_gt_of_ne

protected theorem le_antisymm_iff {a b : Nat} : a = b ↔ a ≤ b ∧ b ≤ a :=
  Iff.intro (fun p => And.intro (Nat.le_of_eq p) (Nat.le_of_eq p.symm))
            (fun ⟨hle, hge⟩ => Nat.le_antisymm hle hge)
protected theorem eq_iff_le_and_ge : ∀{a b : Nat}, a = b ↔ a ≤ b ∧ b ≤ a := @Nat.le_antisymm_iff

instance : Std.Antisymm ( . ≤ . : Nat → Nat → Prop) where
  antisymm _ _ h₁ h₂ := Nat.le_antisymm h₁ h₂

instance : Std.Antisymm (¬ . < . : Nat → Nat → Prop) where
  antisymm _ _ h₁ h₂ := Nat.le_antisymm (Nat.ge_of_not_lt h₂) (Nat.ge_of_not_lt h₁)

protected theorem add_le_add_left {n m : Nat} (h : n ≤ m) (k : Nat) : k + n ≤ k + m :=
  match le.dest h with
  | ⟨w, hw⟩ =>
    have h₁ : k + n + w = k + (n + w) := Nat.add_assoc ..
    have h₂ : k + (n + w) = k + m     := congrArg _ hw
    le.intro <| h₁.trans h₂

protected theorem add_le_add_right {n m : Nat} (h : n ≤ m) (k : Nat) : n + k ≤ m + k := by
  rw [Nat.add_comm n k, Nat.add_comm m k]
  apply Nat.add_le_add_left
  assumption

protected theorem add_lt_add_left {n m : Nat} (h : n < m) (k : Nat) : k + n < k + m :=
  lt_of_succ_le (add_succ k n ▸ Nat.add_le_add_left (succ_le_of_lt h) k)

protected theorem add_lt_add_right {n m : Nat} (h : n < m) (k : Nat) : n + k < m + k :=
  Nat.add_comm k m ▸ Nat.add_comm k n ▸ Nat.add_lt_add_left h k

protected theorem lt_add_of_pos_left (h : 0 < k) : n < k + n := by
  rw [Nat.add_comm]
  exact Nat.add_lt_add_left h n

protected theorem lt_add_of_pos_right (h : 0 < k) : n < n + k :=
  Nat.add_lt_add_left h n

protected theorem zero_lt_one : 0 < (1:Nat) :=
  zero_lt_succ 0

protected theorem pos_iff_ne_zero : 0 < n ↔ n ≠ 0 := ⟨ne_of_gt, Nat.pos_of_ne_zero⟩

theorem add_le_add {a b c d : Nat} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
  Nat.le_trans (Nat.add_le_add_right h₁ c) (Nat.add_le_add_left h₂ b)

theorem add_lt_add {a b c d : Nat} (h₁ : a < b) (h₂ : c < d) : a + c < b + d :=
  Nat.lt_trans (Nat.add_lt_add_right h₁ c) (Nat.add_lt_add_left h₂ b)

protected theorem le_of_add_le_add_left {a b c : Nat} (h : a + b ≤ a + c) : b ≤ c := by
  match le.dest h with
  | ⟨d, hd⟩ =>
    apply @le.intro _ _ d
    rw [Nat.add_assoc] at hd
    apply Nat.add_left_cancel hd

protected theorem le_of_add_le_add_right {a b c : Nat} : a + b ≤ c + b → a ≤ c := by
  rw [Nat.add_comm _ b, Nat.add_comm _ b]
  apply Nat.le_of_add_le_add_left

@[simp] protected theorem add_le_add_iff_right {n : Nat} : m + n ≤ k + n ↔ m ≤ k :=
  ⟨Nat.le_of_add_le_add_right, fun h => Nat.add_le_add_right h _⟩

@[simp] protected theorem add_le_add_iff_left {n : Nat} : n + m ≤ n + k ↔ m ≤ k :=
  ⟨Nat.le_of_add_le_add_left, fun h => Nat.add_le_add_left h _⟩

/-! ### le/lt -/

attribute [simp] not_lt_zero

example : (default : Nat) = 0 := rfl

protected theorem lt_asymm {a b : Nat} (h : a < b) : ¬ b < a := Nat.not_lt.2 (Nat.le_of_lt h)
/-- Alias for `Nat.lt_asymm`. -/
protected abbrev not_lt_of_gt := @Nat.lt_asymm
/-- Alias for `Nat.lt_asymm`. -/
protected abbrev not_lt_of_lt := @Nat.lt_asymm

protected theorem lt_iff_le_not_le {m n : Nat} : m < n ↔ m ≤ n ∧ ¬ n ≤ m :=
  ⟨fun h => ⟨Nat.le_of_lt h, Nat.not_le_of_gt h⟩, fun ⟨_, h⟩ => Nat.lt_of_not_ge h⟩
/-- Alias for `Nat.lt_iff_le_not_le`. -/
protected abbrev lt_iff_le_and_not_ge := @Nat.lt_iff_le_not_le

protected theorem lt_iff_le_and_ne {m n : Nat} : m < n ↔ m ≤ n ∧ m ≠ n :=
  ⟨fun h => ⟨Nat.le_of_lt h, Nat.ne_of_lt h⟩, fun h => Nat.lt_of_le_of_ne h.1 h.2⟩

protected theorem ne_iff_lt_or_gt {a b : Nat} : a ≠ b ↔ a < b ∨ b < a :=
  ⟨Nat.lt_or_gt_of_ne, fun | .inl h => Nat.ne_of_lt h | .inr h => Nat.ne_of_gt h⟩
/-- Alias for `Nat.ne_iff_lt_or_gt`. -/
protected abbrev lt_or_gt := @Nat.ne_iff_lt_or_gt

/-- Alias for `Nat.le_total`. -/
protected abbrev le_or_ge := @Nat.le_total
/-- Alias for `Nat.le_total`. -/
protected abbrev le_or_le := @Nat.le_total

protected theorem eq_or_lt_of_not_lt {a b : Nat} (hnlt : ¬ a < b) : a = b ∨ b < a :=
  (Nat.lt_trichotomy ..).resolve_left hnlt

protected theorem lt_or_eq_of_le {n m : Nat} (h : n ≤ m) : n < m ∨ n = m :=
  (Nat.lt_or_ge ..).imp_right (Nat.le_antisymm h)

protected theorem le_iff_lt_or_eq {n m : Nat} : n ≤ m ↔ n < m ∨ n = m :=
  ⟨Nat.lt_or_eq_of_le, fun | .inl h => Nat.le_of_lt h | .inr rfl => Nat.le_refl _⟩

protected theorem lt_succ_iff : m < succ n ↔ m ≤ n := ⟨le_of_lt_succ, lt_succ_of_le⟩

protected theorem lt_add_one_iff : m < n + 1 ↔ m ≤ n := ⟨le_of_lt_succ, lt_succ_of_le⟩

protected theorem lt_succ_iff_lt_or_eq : m < succ n ↔ m < n ∨ m = n :=
  Nat.lt_succ_iff.trans Nat.le_iff_lt_or_eq

protected theorem lt_add_one_iff_lt_or_eq : m < n + 1 ↔ m < n ∨ m = n :=
  Nat.lt_add_one_iff.trans Nat.le_iff_lt_or_eq

protected theorem eq_of_lt_succ_of_not_lt (hmn : m < n + 1) (h : ¬ m < n) : m = n :=
  (Nat.lt_succ_iff_lt_or_eq.1 hmn).resolve_left h

protected theorem eq_of_le_of_lt_succ (h₁ : n ≤ m) (h₂ : m < n + 1) : m = n :=
  Nat.le_antisymm (le_of_succ_le_succ h₂) h₁


/-! ## zero/one/two -/

theorem le_zero : i ≤ 0 ↔ i = 0 := ⟨Nat.eq_zero_of_le_zero, fun | rfl => Nat.le_refl _⟩

/-- Alias for `Nat.zero_lt_one`. -/
protected abbrev one_pos := @Nat.zero_lt_one

protected theorem two_pos : 0 < 2 := Nat.zero_lt_succ _

protected theorem ne_zero_iff_zero_lt : n ≠ 0 ↔ 0 < n := Nat.pos_iff_ne_zero.symm

protected theorem zero_lt_two : 0 < 2 := Nat.zero_lt_succ _

protected theorem one_lt_two : 1 < 2 := Nat.succ_lt_succ Nat.zero_lt_one

protected theorem eq_zero_of_not_pos (h : ¬0 < n) : n = 0 :=
  Nat.eq_zero_of_le_zero (Nat.not_lt.1 h)

/-! ## succ/pred -/

attribute [simp] zero_lt_succ

@[simp] theorem succ_ne_self (n) : succ n ≠ n := Nat.ne_of_gt (lt_succ_self n)

theorem add_one_ne_self (n) : n + 1 ≠ n := Nat.ne_of_gt (lt_succ_self n)

theorem succ_le : succ n ≤ m ↔ n < m := .rfl

theorem add_one_le_iff : n + 1 ≤ m ↔ n < m := .rfl

theorem lt_succ : m < succ n ↔ m ≤ n := ⟨le_of_lt_succ, lt_succ_of_le⟩

theorem lt_succ_of_lt (h : a < b) : a < succ b := le_succ_of_le h

theorem lt_add_one_of_lt (h : a < b) : a < b + 1 := le_succ_of_le h

@[simp] theorem lt_one_iff : n < 1 ↔ n = 0 := Nat.lt_succ_iff.trans <| by rw [le_zero_eq]

theorem succ_pred_eq_of_ne_zero : ∀ {n}, n ≠ 0 → succ (pred n) = n
  | _+1, _ => rfl

theorem eq_zero_or_eq_succ_pred : ∀ n, n = 0 ∨ n = succ (pred n)
  | 0 => .inl rfl
  | _+1 => .inr rfl

theorem succ_inj : succ a = succ b ↔ a = b := (Nat.succ.injEq a b).to_iff

@[deprecated succ_inj (since := "2025-04-14")]
theorem succ_inj' : succ a = succ b ↔ a = b := succ_inj

theorem succ_le_succ_iff : succ a ≤ succ b ↔ a ≤ b := ⟨le_of_succ_le_succ, succ_le_succ⟩

theorem succ_lt_succ_iff : succ a < succ b ↔ a < b := ⟨lt_of_succ_lt_succ, succ_lt_succ⟩

theorem succ_ne_succ_iff : succ a ≠ succ b ↔ a ≠ b := by simp [Nat.succ.injEq]

theorem succ_succ_ne_one (a : Nat) : succ (succ a) ≠ 1 := nofun

theorem add_one_inj : a + 1 = b + 1 ↔ a = b := succ_inj

theorem ne_add_one (n : Nat) : n ≠ n + 1 := fun h => by cases h

theorem add_one_ne (n : Nat) : n + 1 ≠ n := fun h => by cases h

theorem add_one_le_add_one_iff : a + 1 ≤ b + 1 ↔ a ≤ b := succ_le_succ_iff

theorem add_one_lt_add_one_iff : a + 1 < b + 1 ↔ a < b := succ_lt_succ_iff

theorem add_one_ne_add_one_iff : a + 1 ≠ b + 1 ↔ a ≠ b := succ_ne_succ_iff

theorem add_one_add_one_ne_one : a + 1 + 1 ≠ 1 := nofun

theorem pred_inj : ∀ {a b}, 0 < a → 0 < b → pred a = pred b → a = b
  | _+1, _+1, _, _ => congrArg _

theorem pred_ne_self : ∀ {a}, a ≠ 0 → pred a ≠ a
  | _+1, _ => (succ_ne_self _).symm

theorem sub_one_ne_self : ∀ {a}, a ≠ 0 → a - 1 ≠ a
  | _+1, _ => (succ_ne_self _).symm

theorem pred_lt_self : ∀ {a}, 0 < a → pred a < a
  | _+1, _ => lt_succ_self _

theorem pred_lt_pred : ∀ {n m}, n ≠ 0 → n < m → pred n < pred m
  | _+1, _+1, _, h => lt_of_succ_lt_succ h

theorem pred_le_iff_le_succ : ∀ {n m}, pred n ≤ m ↔ n ≤ succ m
  | 0, _ => ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩
  | _+1, _ => Nat.succ_le_succ_iff.symm

theorem le_succ_of_pred_le : pred n ≤ m → n ≤ succ m := pred_le_iff_le_succ.1

theorem pred_le_of_le_succ : n ≤ succ m → pred n ≤ m := pred_le_iff_le_succ.2

theorem lt_pred_iff_succ_lt : ∀ {n m}, n < pred m ↔ succ n < m
  | _, 0 => ⟨nofun, nofun⟩
  | _, _+1 => Nat.succ_lt_succ_iff.symm

theorem succ_lt_of_lt_pred : n < pred m → succ n < m := lt_pred_iff_succ_lt.1

theorem lt_pred_of_succ_lt : succ n < m → n < pred m := lt_pred_iff_succ_lt.2

theorem le_pred_iff_lt : ∀ {n m}, 0 < m → (n ≤ pred m ↔ n < m)
  | 0, _+1, _ => ⟨fun _ => Nat.zero_lt_succ _, fun _ => Nat.zero_le _⟩
  | _+1, _+1, _ => Nat.lt_pred_iff_succ_lt

theorem le_pred_of_lt (h : n < m) : n ≤ pred m := (le_pred_iff_lt (Nat.zero_lt_of_lt h)).2 h

theorem le_sub_one_of_lt : a < b → a ≤ b - 1 := Nat.le_pred_of_lt

theorem lt_of_le_pred (h : 0 < m) : n ≤ pred m → n < m := (le_pred_iff_lt h).1

theorem lt_of_le_sub_one (h : 0 < m) : n ≤ m - 1 → n < m := (le_pred_iff_lt h).1

protected theorem le_sub_one_iff_lt (h : 0 < m) : n ≤ m - 1 ↔ n < m :=
  ⟨Nat.lt_of_le_sub_one h, Nat.le_sub_one_of_lt⟩

theorem exists_eq_succ_of_ne_zero : ∀ {n}, n ≠ 0 → Exists fun k => n = succ k
  | _+1, _ => ⟨_, rfl⟩

theorem exists_eq_add_one_of_ne_zero : ∀ {n}, n ≠ 0 → Exists fun k => n = k + 1
  | _+1, _ => ⟨_, rfl⟩

/-! # Basic theorems for comparing numerals -/

theorem ctor_eq_zero : Nat.zero = 0 :=
  rfl

protected theorem one_ne_zero : 1 ≠ (0 : Nat) := by simp

@[simp] protected theorem zero_ne_one : 0 ≠ (1 : Nat) :=
  fun h => Nat.noConfusion h

theorem succ_ne_zero (n : Nat) : succ n ≠ 0 := by simp

instance instNeZeroSucc {n : Nat} : NeZero (n + 1) := ⟨succ_ne_zero n⟩

@[simp] theorem default_eq_zero : default = 0 := rfl

/-! # mul + order -/

theorem mul_le_mul_left {n m : Nat} (k : Nat) (h : n ≤ m) : k * n ≤ k * m :=
  match le.dest h with
  | ⟨l, hl⟩ =>
    have : k * n + k * l = k * m := Nat.left_distrib k n l ▸ hl.symm ▸ rfl
    le.intro this

theorem mul_le_mul_right {n m : Nat} (k : Nat) (h : n ≤ m) : n * k ≤ m * k :=
  Nat.mul_comm k m ▸ Nat.mul_comm k n ▸ mul_le_mul_left k h

protected theorem mul_le_mul {n₁ m₁ n₂ m₂ : Nat} (h₁ : n₁ ≤ n₂) (h₂ : m₁ ≤ m₂) : n₁ * m₁ ≤ n₂ * m₂ :=
  Nat.le_trans (mul_le_mul_right _ h₁) (mul_le_mul_left _ h₂)

protected theorem mul_lt_mul_of_pos_left {n m k : Nat} (h : n < m) (hk : k > 0) : k * n < k * m :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk _) (Nat.mul_succ k n ▸ Nat.mul_le_mul_left k (succ_le_of_lt h))

protected theorem mul_lt_mul_of_pos_right {n m k : Nat} (h : n < m) (hk : k > 0) : n * k < m * k :=
  Nat.mul_comm k m ▸ Nat.mul_comm k n ▸ Nat.mul_lt_mul_of_pos_left h hk

protected theorem le_of_mul_le_mul_left {a b c : Nat} (h : c * a ≤ c * b) (hc : 0 < c) : a ≤ b :=
  Nat.ge_of_not_lt fun hlt : b < a =>
    have h' : c * b < c * a := Nat.mul_lt_mul_of_pos_left hlt hc
    absurd h (Nat.not_le_of_gt h')

protected theorem le_of_mul_le_mul_right {a b c : Nat} (h : a * c ≤ b * c) (hc : 0 < c) : a ≤ b := by
  rw [Nat.mul_comm a c, Nat.mul_comm b c] at h
  exact Nat.le_of_mul_le_mul_left h hc

protected theorem mul_le_mul_left_iff {n m k : Nat} (w : 0 < k) : k * n ≤ k * m ↔ n ≤ m :=
  ⟨fun h => Nat.le_of_mul_le_mul_left h w, fun h => mul_le_mul_left _ h⟩

protected theorem mul_le_mul_right_iff {n m k : Nat} (w : 0 < k) : n * k ≤ m * k ↔ n ≤ m :=
  ⟨fun h => Nat.le_of_mul_le_mul_right h w, fun h => mul_le_mul_right _ h⟩

protected theorem eq_of_mul_eq_mul_left {m k n : Nat} (hn : 0 < n) (h : n * m = n * k) : m = k :=
  Nat.le_antisymm (Nat.le_of_mul_le_mul_left (Nat.le_of_eq h) hn)
                  (Nat.le_of_mul_le_mul_left (Nat.le_of_eq h.symm) hn)

theorem eq_of_mul_eq_mul_right {n m k : Nat} (hm : 0 < m) (h : n * m = k * m) : n = k := by
  rw [Nat.mul_comm n m, Nat.mul_comm k m] at h; exact Nat.eq_of_mul_eq_mul_left hm h

/-! # power -/

protected theorem pow_succ (n m : Nat) : n^(succ m) = n^m * n :=
  rfl

protected theorem pow_add_one (n m : Nat) : n^(m + 1) = n^m * n :=
  rfl

@[simp] protected theorem pow_zero (n : Nat) : n^0 = 1 := rfl

@[simp] protected theorem pow_one (a : Nat) : a ^ 1 = a := by
  simp [Nat.pow_succ]

protected theorem pow_le_pow_left {n m : Nat} (h : n ≤ m) : ∀ (i : Nat), n^i ≤ m^i
  | 0      => Nat.le_refl _
  | succ i => Nat.mul_le_mul (Nat.pow_le_pow_left h i) h

protected theorem pow_le_pow_right {n : Nat} (hx : n > 0) {i : Nat} : ∀ {j}, i ≤ j → n^i ≤ n^j
  | 0,      h =>
    have : i = 0 := eq_zero_of_le_zero h
    this.symm ▸ Nat.le_refl _
  | succ j, h =>
    match le_or_eq_of_le_succ h with
    | Or.inl h => show n^i ≤ n^j * n from
      have : n^i * 1 ≤ n^j * n := Nat.mul_le_mul (Nat.pow_le_pow_right hx h) hx
      Nat.mul_one (n^i) ▸ this
    | Or.inr h =>
      h.symm ▸ Nat.le_refl _

@[simp] theorem zero_pow_of_pos (n : Nat) (h : 0 < n) : 0 ^ n = 0 := by
  cases n with
  | zero => cases h
  | succ n => simp [Nat.pow_succ]

protected theorem two_pow_pos (w : Nat) : 0 < 2^w := Nat.pow_pos (by decide)

instance {n m : Nat} [NeZero n] : NeZero (n^m) :=
  ⟨Nat.ne_zero_iff_zero_lt.mpr (Nat.pow_pos (pos_of_neZero _))⟩

protected theorem mul_pow (a b n : Nat) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => simp [Nat.pow_zero]
  | succ n ih =>
    rw [Nat.pow_succ, ih, Nat.pow_succ, Nat.pow_succ, ← Nat.mul_assoc, ← Nat.mul_assoc]
    congr 1
    rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm _ a]

protected theorem pow_lt_pow_left {a b n : Nat} (hab : a < b) (h : n ≠ 0) : a ^ n < b ^ n := by
  cases n with
  | zero => simp at h
  | succ n =>
    clear h
    induction n with
    | zero => simpa
    | succ n ih =>
      rw [Nat.pow_succ a, Nat.pow_succ b]
      exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_of_lt hab))
        (Nat.mul_lt_mul_of_pos_right ih (Nat.lt_of_le_of_lt (Nat.zero_le _) hab))

protected theorem pow_left_inj {a b n : Nat} (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b := by
  refine ⟨fun h => ?_, (· ▸ rfl)⟩
  match Nat.lt_trichotomy a b with
  | Or.inl hab => exact False.elim (absurd h (ne_of_lt (Nat.pow_lt_pow_left hab hn)))
  | Or.inr (Or.inl hab) => exact hab
  | Or.inr (Or.inr hab) => exact False.elim (absurd h (Nat.ne_of_lt' (Nat.pow_lt_pow_left hab hn)))

/-! # min/max -/

/--
Returns the lesser of two natural numbers. Usually accessed via `Min.min`.

Returns `n` if `n ≤ m`, or `m` if `m ≤ n`.

Examples:
* `min 0 5 = 0`
* `min 4 5 = 4`
* `min 4 3 = 3`
* `min 8 8 = 8`
-/
protected abbrev min (n m : Nat) := min n m

@[grind =] protected theorem min_def {n m : Nat} : min n m = if n ≤ m then n else m := rfl

instance : Max Nat := maxOfLe

/--
Returns the greater of two natural numbers. Usually accessed via `Max.max`.

Returns `m` if `n ≤ m`, or `n` if `m ≤ n`.

Examples:
* `max 0 5 = 5`
* `max 4 5 = 5`
* `max 4 3 = 4`
* `max 8 8 = 8`
-/
protected abbrev max (n m : Nat) := max n m

@[grind =] protected theorem max_def {n m : Nat} : max n m = if n ≤ m then m else n := rfl


/-! # Auxiliary theorems for well-founded recursion -/

protected theorem ne_zero_of_lt (h : b < a) : a ≠ 0 := by
  cases a
  exact absurd h (Nat.not_lt_zero _)
  apply Nat.noConfusion

theorem pred_lt_of_lt {n m : Nat} (h : m < n) : pred n < n :=
  pred_lt (Nat.ne_zero_of_lt h)

theorem sub_one_lt_of_lt {n m : Nat} (h : m < n) : n - 1 < n :=
  sub_one_lt (Nat.ne_zero_of_lt h)

/-! # pred theorems -/

protected theorem pred_zero : pred 0 = 0 := rfl
protected theorem pred_succ (n : Nat) : pred n.succ = n := rfl

@[simp] protected theorem zero_sub_one : 0 - 1 = 0 := rfl
@[simp] protected theorem add_one_sub_one (n : Nat) : n + 1 - 1 = n := rfl

theorem sub_one_eq_self {n : Nat} : n - 1 = n ↔ n = 0 := by cases n <;> simp [ne_add_one]
theorem eq_self_sub_one {n : Nat} : n = n - 1 ↔ n = 0 := by cases n <;> simp

theorem succ_pred {a : Nat} (h : a ≠ 0) : a.pred.succ = a := by
  induction a with
  | zero => contradiction
  | succ => rfl

theorem sub_one_add_one {a : Nat} (h : a ≠ 0) : a - 1 + 1 = a := by
  induction a with
  | zero => contradiction
  | succ => rfl

theorem succ_pred_eq_of_pos : ∀ {n}, 0 < n → succ (pred n) = n
  | _+1, _ => rfl

theorem sub_one_add_one_eq_of_pos : ∀ {n}, 0 < n → (n - 1) + 1 = n
  | _+1, _ => rfl

theorem eq_zero_or_eq_sub_one_add_one : ∀ {n}, n = 0 ∨ n = n - 1 + 1
  | 0 => Or.inl rfl
  | _+1 => Or.inr rfl

@[simp] theorem pred_eq_sub_one : pred n = n - 1 := rfl

/-! # sub theorems -/

theorem add_sub_self_left (a b : Nat) : (a + b) - a = b := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_add, Nat.succ_sub_succ]
    apply ih

theorem add_sub_self_right (a b : Nat) : (a + b) - b = a := by
  rw [Nat.add_comm]; apply add_sub_self_left

theorem sub_le_succ_sub (a i : Nat) : a - i ≤ a.succ - i := by
  cases i with
  | zero => apply Nat.le_of_lt; apply Nat.lt_succ_self
  | succ i => rw [Nat.sub_succ, Nat.succ_sub_succ]; apply Nat.pred_le

theorem zero_lt_sub_of_lt (h : i < a) : 0 < a - i := by
  induction a with
  | zero => contradiction
  | succ a ih =>
    match Nat.eq_or_lt_of_le h with
    | Or.inl h => injection h with h; subst h; rw [Nat.add_sub_self_left]; decide
    | Or.inr h =>
      have : 0 < a - i := ih (Nat.lt_of_succ_lt_succ h)
      exact Nat.lt_of_lt_of_le this (Nat.sub_le_succ_sub _ _)

theorem sub_succ_lt_self (a i : Nat) (h : i < a) : a - (i + 1) < a - i := by
  rw [Nat.add_succ, Nat.sub_succ]
  apply Nat.pred_lt
  apply Nat.ne_zero_of_lt
  apply Nat.zero_lt_sub_of_lt
  assumption

theorem sub_ne_zero_of_lt : {a b : Nat} → a < b → b - a ≠ 0
  | 0, 0, h      => absurd h (Nat.lt_irrefl 0)
  | 0, succ b, _ => by simp only [Nat.sub_zero, ne_eq, not_false_eq_true, Nat.succ_ne_zero]
  | succ a, 0, h => absurd h (Nat.not_lt_zero a.succ)
  | succ a, succ b, h => by rw [Nat.succ_sub_succ]; exact sub_ne_zero_of_lt (Nat.lt_of_succ_lt_succ h)

theorem add_sub_of_le {a b : Nat} (h : a ≤ b) : a + (b - a) = b := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hne : b - a ≠ 0 := Nat.sub_ne_zero_of_lt h
    have : a ≤ b := Nat.le_of_succ_le h
    rw [sub_succ, Nat.succ_add, ← Nat.add_succ, Nat.succ_pred hne, ih this]

theorem sub_one_cancel : ∀ {a b : Nat}, 0 < a → 0 < b → a - 1 = b - 1 → a = b
  | _+1, _+1, _, _ => congrArg _

@[simp] protected theorem sub_add_cancel {n m : Nat} (h : m ≤ n) : n - m + m = n := by
  rw [Nat.add_comm, Nat.add_sub_of_le h]

protected theorem add_sub_add_right (n k m : Nat) : (n + k) - (m + k) = n - m := by
  induction k with
  | zero => simp
  | succ k ih => simp [← Nat.add_assoc, succ_sub_succ_eq_sub, ih]

protected theorem add_sub_add_left (k n m : Nat) : (k + n) - (k + m) = n - m := by
  rw [Nat.add_comm k n, Nat.add_comm k m, Nat.add_sub_add_right]

@[simp] protected theorem add_sub_cancel (n m : Nat) : n + m - m = n :=
  suffices n + m - (0 + m) = n by rw [Nat.zero_add] at this; assumption
  by rw [Nat.add_sub_add_right, Nat.sub_zero]

@[simp] protected theorem add_sub_cancel_left (n m : Nat) : n + m - n = m :=
  show n + m - (n + 0) = m from
  by rw [Nat.add_sub_add_left, Nat.sub_zero]

protected theorem add_sub_assoc {m k : Nat} (h : k ≤ m) (n : Nat) : n + m - k = n + (m - k) := by
 cases Nat.le.dest h
 rename_i l hl
 rw [← hl, Nat.add_sub_cancel_left, Nat.add_comm k, ← Nat.add_assoc, Nat.add_sub_cancel]

protected theorem eq_add_of_sub_eq {a b c : Nat} (hle : b ≤ a) (h : a - b = c) : a = c + b := by
  rw [h.symm, Nat.sub_add_cancel hle]

protected theorem sub_eq_of_eq_add {a b c : Nat} (h : a = c + b) : a - b = c := by
  rw [h, Nat.add_sub_cancel]

theorem le_add_of_sub_le {a b c : Nat} (h : a - b ≤ c) : a ≤ c + b := by
  match le.dest h, Nat.le_total a b with
  | _, Or.inl hle =>
    exact Nat.le_trans hle (Nat.le_add_left ..)
  | ⟨d, hd⟩, Or.inr hge =>
    apply @le.intro _ _ d
    rw [Nat.add_comm, ← Nat.add_sub_assoc hge] at hd
    have hd := Nat.eq_add_of_sub_eq (Nat.le_trans hge (Nat.le_add_left ..)) hd
    rw [Nat.add_comm, hd]

protected theorem sub_lt_sub_left : ∀ {k m n : Nat}, k < m → k < n → m - n < m - k
  | 0, m+1, n+1, _, _ => by rw [Nat.add_sub_add_right]; exact lt_succ_of_le (Nat.sub_le _ _)
  | k+1, m+1, n+1, h1, h2 => by
    rw [Nat.add_sub_add_right, Nat.add_sub_add_right]
    exact Nat.sub_lt_sub_left (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2)

@[simp] protected theorem zero_sub (n : Nat) : 0 - n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ih, Nat.sub_succ]; decide

protected theorem sub_lt_sub_right : ∀ {a b c : Nat}, c ≤ a → a < b → a - c < b - c
  | 0, _, _, hle, h => by
    rw [Nat.eq_zero_of_le_zero hle, Nat.sub_zero, Nat.sub_zero]
    exact h
  | _, _, 0, _, h => by
    rw [Nat.sub_zero, Nat.sub_zero]
    exact h
  | _+1, _+1, _+1, hle, h => by
    rw [Nat.add_sub_add_right, Nat.add_sub_add_right]
    exact Nat.sub_lt_sub_right (le_of_succ_le_succ hle) (lt_of_succ_lt_succ h)

protected theorem sub_self_add (n m : Nat) : n - (n + m) = 0 := by
  change (n + 0) - (n + m) = 0
  rw [Nat.add_sub_add_left, Nat.zero_sub]

@[simp] protected theorem sub_eq_zero_of_le {n m : Nat} (h : n ≤ m) : n - m = 0 := by
  match le.dest h with
  | ⟨k, hk⟩ => rw [← hk, Nat.sub_self_add]

theorem sub_le_of_le_add {a b c : Nat} (h : a ≤ c + b) : a - b ≤ c := by
  match le.dest h, Nat.le_total a b with
  | _, Or.inl hle =>
    rw [Nat.sub_eq_zero_of_le hle]
    apply Nat.zero_le
  | ⟨d, hd⟩, Or.inr hge =>
    apply @le.intro _ _ d
    have hd := Nat.sub_eq_of_eq_add hd
    rw [Nat.add_comm, ← Nat.add_sub_assoc hge, Nat.add_comm]
    exact hd

theorem add_le_of_le_sub {a b c : Nat} (hle : b ≤ c) (h : a ≤ c - b) : a + b ≤ c := by
  match le.dest h with
  | ⟨d, hd⟩ =>
    apply @le.intro _ _ d
    rw [Nat.eq_add_of_sub_eq hle hd.symm]
    simp [Nat.add_comm, Nat.add_left_comm]

theorem le_sub_of_add_le {a b c : Nat} (h : a + b ≤ c) : a ≤ c - b := by
  match le.dest h with
  | ⟨d, hd⟩ =>
    apply @le.intro _ _ d
    have hd : a + d + b = c := by simp [← hd, Nat.add_comm, Nat.add_left_comm]
    have hd := Nat.sub_eq_of_eq_add hd.symm
    exact hd.symm

theorem add_lt_of_lt_sub {a b c : Nat} (h : a < c - b) : a + b < c := by
  have hle : b ≤ c := by
    apply Nat.ge_of_not_lt
    intro hgt
    apply Nat.not_lt_zero a
    rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hgt)] at h
    exact h
  have : a.succ + b ≤ c := add_le_of_le_sub hle h
  simp [Nat.succ_add] at this
  exact this

theorem lt_sub_of_add_lt {a b c : Nat} (h : a + b < c) : a < c - b :=
  have : a.succ + b ≤ c := by simp [Nat.succ_add]; exact h
  le_sub_of_add_le this

theorem sub.elim {motive : Nat → Prop}
    (x y : Nat)
    (h₁ : y ≤ x → (k : Nat) → x = y + k → motive k)
    (h₂ : x < y → motive 0)
    : motive (x - y) := by
  cases Nat.lt_or_ge x y with
  | inl hlt => rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)]; exact h₂ hlt
  | inr hle => exact h₁ hle (x - y) (Nat.add_sub_of_le hle).symm

theorem succ_sub {m n : Nat} (h : n ≤ m) : succ m - n = succ (m - n) := by
  let ⟨k, hk⟩ := Nat.le.dest h
  rw [← hk, Nat.add_sub_cancel_left, ← add_succ, Nat.add_sub_cancel_left]

protected theorem sub_pos_of_lt (h : m < n) : 0 < n - m :=
  Nat.pos_iff_ne_zero.2 (Nat.sub_ne_zero_of_lt h)

protected theorem sub_sub (n m k : Nat) : n - m - k = n - (m + k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.add_succ, Nat.sub_succ, Nat.add_succ, Nat.sub_succ, ih]

protected theorem sub_le_sub_left (h : n ≤ m) (k : Nat) : k - m ≤ k - n :=
  match m, le.dest h with
  | _, ⟨a, rfl⟩ => by rw [← Nat.sub_sub]; apply sub_le

protected theorem sub_le_sub_right {n m : Nat} (h : n ≤ m) : ∀ k, n - k ≤ m - k
  | 0   => h
  | z+1 => pred_le_pred (Nat.sub_le_sub_right h z)

protected theorem sub_le_add_right_sub (a i j : Nat) : a - i ≤ a + j - i :=
  Nat.sub_le_sub_right (Nat.le_add_right ..) ..

protected theorem lt_of_sub_ne_zero (h : n - m ≠ 0) : m < n :=
  Nat.not_le.1 (mt Nat.sub_eq_zero_of_le h)

protected theorem sub_ne_zero_iff_lt : n - m ≠ 0 ↔ m < n :=
  ⟨Nat.lt_of_sub_ne_zero, Nat.sub_ne_zero_of_lt⟩

protected theorem lt_of_sub_pos (h : 0 < n - m) : m < n :=
  Nat.lt_of_sub_ne_zero (Nat.pos_iff_ne_zero.1 h)

protected theorem lt_of_sub_eq_succ (h : m - n = succ l) : n < m :=
  Nat.lt_of_sub_pos (h ▸ Nat.zero_lt_succ _)

protected theorem lt_of_sub_eq_sub_one (h : m - n = l + 1) : n < m :=
  Nat.lt_of_sub_pos (h ▸ Nat.zero_lt_succ _)

protected theorem sub_lt_left_of_lt_add {n k m : Nat} (H : n ≤ k) (h : k < n + m) : k - n < m := by
  have := Nat.sub_le_sub_right (succ_le_of_lt h) n
  rwa [Nat.add_sub_cancel_left, Nat.succ_sub H] at this

protected theorem sub_lt_right_of_lt_add {n k m : Nat} (H : n ≤ k) (h : k < m + n) : k - n < m :=
  Nat.sub_lt_left_of_lt_add H (Nat.add_comm .. ▸ h)

protected theorem le_of_sub_eq_zero : ∀ {n m}, n - m = 0 → n ≤ m
  | 0, _, _ => Nat.zero_le ..
  | _+1, _+1, h => Nat.succ_le_succ <| Nat.le_of_sub_eq_zero (Nat.succ_sub_succ .. ▸ h)

protected theorem le_of_sub_le_sub_right : ∀ {n m k : Nat}, k ≤ m → n - k ≤ m - k → n ≤ m
  | 0, _, _, _, _ => Nat.zero_le ..
  | _+1, _, 0, _, h₁ => h₁
  | _+1, _+1, _+1, h₀, h₁ => by
    simp only [Nat.succ_sub_succ] at h₁
    exact succ_le_succ <| Nat.le_of_sub_le_sub_right (le_of_succ_le_succ h₀) h₁

protected theorem sub_le_sub_iff_right {n : Nat} (h : k ≤ m) : n - k ≤ m - k ↔ n ≤ m :=
  ⟨Nat.le_of_sub_le_sub_right h, fun h => Nat.sub_le_sub_right h _⟩

protected theorem sub_eq_iff_eq_add {c : Nat} (h : b ≤ a) : a - b = c ↔ a = c + b :=
  ⟨fun | rfl => by rw [Nat.sub_add_cancel h], fun heq => by rw [heq, Nat.add_sub_cancel]⟩

protected theorem sub_eq_iff_eq_add' {c : Nat} (h : b ≤ a) : a - b = c ↔ a = b + c := by
  rw [Nat.add_comm, Nat.sub_eq_iff_eq_add h]

attribute [simp] sub_le

protected theorem sub_one_sub_lt_of_lt (h : a < b) : b - 1 - a < b := by
  rw [← Nat.sub_add_eq]
  exact sub_lt (zero_lt_of_lt h) (Nat.lt_add_right a Nat.one_pos)

/-! ## Mul sub distrib -/

theorem pred_mul (n m : Nat) : pred n * m = n * m - m := by
  cases n with
  | zero   => simp
  | succ n => rw [Nat.pred_succ, succ_mul, Nat.add_sub_cancel]

protected theorem sub_one_mul  (n m : Nat) : (n - 1) * m = n * m - m := by
  cases n with
  | zero   => simp
  | succ n =>
    rw [Nat.add_sub_cancel, add_one_mul, Nat.add_sub_cancel]

theorem mul_pred (n m : Nat) : n * pred m = n * m - n := by
  rw [Nat.mul_comm, pred_mul, Nat.mul_comm]

theorem mul_sub_one (n m : Nat) : n * (m - 1) = n * m - n := by
  rw [Nat.mul_comm, Nat.sub_one_mul , Nat.mul_comm]

protected theorem mul_sub_right_distrib (n m k : Nat) : (n - m) * k = n * k - m * k := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.sub_succ, Nat.pred_mul, ih, succ_mul, Nat.sub_sub]; done

protected theorem sub_mul (n m k : Nat) : (n - m) * k = n * k - m * k :=
  Nat.mul_sub_right_distrib n m k

protected theorem mul_sub_left_distrib (n m k : Nat) : n * (m - k) = n * m - n * k := by
  rw [Nat.mul_comm, Nat.mul_sub_right_distrib, Nat.mul_comm m n, Nat.mul_comm n k]

protected theorem mul_sub (n m k : Nat) : n * (m - k) = n * m - n * k :=
  Nat.mul_sub_left_distrib n m k

/-! # Helper normalization theorems -/

theorem not_le_eq (a b : Nat) : (¬ (a ≤ b)) = (b + 1 ≤ a) :=
  Eq.propIntro Nat.gt_of_not_le Nat.not_le_of_gt
theorem not_ge_eq (a b : Nat) : (¬ (a ≥ b)) = (a + 1 ≤ b) :=
  not_le_eq b a

theorem not_lt_eq (a b : Nat) : (¬ (a < b)) = (b ≤ a) :=
  Eq.propIntro Nat.le_of_not_lt Nat.not_lt_of_le
theorem not_gt_eq (a b : Nat) : (¬ (a > b)) = (a ≤ b) :=
  not_lt_eq b a

@[csimp] theorem repeat_eq_repeatTR : @repeat = @repeatTR :=
  funext fun α => funext fun f => funext fun n => funext fun init =>
  let rec go : ∀ m n, repeatTR.loop f m (repeat f n init) = repeat f (m + n) init
    | 0,      n => by simp [repeatTR.loop]
    | succ m, n => by rw [repeatTR.loop, succ_add]; exact go m (succ n)
  (go n 0).symm

end Nat



/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro, Floris van Doorn
-/
module

prelude
import all Init.Data.Nat.Bitwise.Basic
public import Init.Data.Nat.MinMax
public import Init.Data.Nat.Log2
import all Init.Data.Nat.Log2
public import Init.Data.Nat.Power2
public import Init.Data.Nat.Mod
import Init.TacticsExtra
import Init.BinderPredicates

public section

/-! # Basic theorems about natural numbers

The primary purpose of the theorems in this file is to assist with reasoning
about sizes of objects, array indices and such.

The content of this file was upstreamed from Batteries and mathlib,
and later these theorems should be organised into other files more systematically.
-/

namespace Nat

@[simp] theorem exists_ne_zero {P : Nat → Prop} : (∃ n, ¬ n = 0 ∧ P n) ↔ ∃ n, P (n + 1) :=
  ⟨fun ⟨n, h, w⟩ => by cases n with | zero => simp at h | succ n => exact ⟨n, w⟩,
    fun ⟨n, w⟩ => ⟨n + 1, by simp, w⟩⟩

@[simp] theorem exists_eq_add_one : (∃ n, a = n + 1) ↔ 0 < a :=
  ⟨fun ⟨n, h⟩ => by omega, fun h => ⟨a - 1, by omega⟩⟩
@[simp] theorem exists_add_one_eq : (∃ n, n + 1 = a) ↔ 0 < a :=
  ⟨fun ⟨n, h⟩ => by omega, fun h => ⟨a - 1, by omega⟩⟩

/-- Dependent variant of `forall_lt_succ_right`. -/
theorem forall_lt_succ_right' {p : (m : Nat) → (m < n + 1) → Prop} :
    (∀ m (h : m < n + 1), p m h) ↔ (∀ m (h : m < n), p m (by omega)) ∧ p n (by omega) := by
  simp only [Nat.lt_succ_iff, Nat.le_iff_lt_or_eq]
  constructor
  · intro w
    constructor
    · intro m h
      exact w _ (.inl h)
    · exact w _ (.inr rfl)
  · rintro w m (h|rfl)
    · exact w.1 _ h
    · exact w.2

/-- See `forall_lt_succ_right'` for a variant where `p` takes the bound as an argument. -/
theorem forall_lt_succ_right {p : Nat → Prop} :
    (∀ m, m < n + 1 → p m) ↔ (∀ m, m < n → p m) ∧ p n := by
  simpa using forall_lt_succ_right' (p := fun m _ => p m)

/-- Dependent variant of `forall_lt_succ_left`. -/
theorem forall_lt_succ_left' {p : (m : Nat) → (m < n + 1) → Prop} :
    (∀ m (h : m < n + 1), p m h) ↔ p 0 (by omega) ∧ (∀ m (h : m < n), p (m + 1) (by omega)) := by
  constructor
  · intro w
    constructor
    · exact w 0 (by omega)
    · intro m h
      exact w (m + 1) (by omega)
  · rintro ⟨h₀, h₁⟩ m h
    cases m with
    | zero => exact h₀
    | succ m => exact h₁ m (by omega)

/-- See `forall_lt_succ_left'` for a variant where `p` takes the bound as an argument. -/
theorem forall_lt_succ_left {p : Nat → Prop} :
    (∀ m, m < n + 1 → p m) ↔ p 0 ∧ (∀ m, m < n → p (m + 1)) := by
  simpa using forall_lt_succ_left' (p := fun m _ => p m)

/-- Dependent variant of `exists_lt_succ_right`. -/
theorem exists_lt_succ_right' {p : (m : Nat) → (m < n + 1) → Prop} :
    (∃ m, ∃ (h : m < n + 1), p m h) ↔ (∃ m, ∃ (h : m < n), p m (by omega)) ∨ p n (by omega) := by
  simp only [Nat.lt_succ_iff, Nat.le_iff_lt_or_eq]
  constructor
  · rintro ⟨m, (h|rfl), w⟩
    · exact .inl ⟨m, h, w⟩
    · exact .inr w
  · rintro (⟨m, h, w⟩ | w)
    · exact ⟨m, by omega, w⟩
    · exact ⟨n, by omega, w⟩

/-- See `exists_lt_succ_right'` for a variant where `p` takes the bound as an argument. -/
theorem exists_lt_succ_right {p : Nat → Prop} :
    (∃ m, m < n + 1 ∧ p m) ↔ (∃ m, m < n ∧ p m) ∨ p n := by
  simpa using exists_lt_succ_right' (p := fun m _ => p m)

/-- Dependent variant of `exists_lt_succ_left`. -/
theorem exists_lt_succ_left' {p : (m : Nat) → (m < n + 1) → Prop} :
    (∃ m, ∃ (h : m < n + 1), p m h) ↔ p 0 (by omega) ∨ (∃ m, ∃ (h : m < n), p (m + 1) (by omega)) := by
  constructor
  · rintro ⟨_|m, h, w⟩
    · exact .inl w
    · exact .inr ⟨m, by omega, w⟩
  · rintro (w|⟨m, h, w⟩)
    · exact ⟨0, by omega, w⟩
    · exact ⟨m + 1, by omega, w⟩

/-- See `exists_lt_succ_left'` for a variant where `p` takes the bound as an argument. -/
theorem exists_lt_succ_left {p : Nat → Prop} :
    (∃ m, m < n + 1 ∧ p m) ↔ p 0 ∨ (∃ m, m < n ∧ p (m + 1)) := by
  simpa using exists_lt_succ_left' (p := fun m _ => p m)

/-! ## succ/pred -/

protected theorem sub_one (n) : n - 1 = pred n := rfl

theorem one_add (n) : 1 + n = succ n := Nat.add_comm ..

theorem succ_ne_succ : succ m ≠ succ n ↔ m ≠ n :=
  ⟨mt (congrArg Nat.succ ·), mt succ.inj⟩

theorem one_lt_succ_succ (n : Nat) : 1 < n.succ.succ := succ_lt_succ <| succ_pos _

theorem not_succ_lt_self : ¬ succ n < n := Nat.not_lt_of_ge n.le_succ

theorem succ_le_iff : succ m ≤ n ↔ m < n := ⟨lt_of_succ_le, succ_le_of_lt⟩

theorem le_succ_iff {m n : Nat} : m ≤ n.succ ↔ m ≤ n ∨ m = n.succ := by
  refine ⟨fun hmn ↦ (Nat.lt_or_eq_of_le hmn).imp_left le_of_lt_succ, ?_⟩
  rintro (hmn | rfl)
  · exact le_succ_of_le hmn
  · exact Nat.le_refl _

theorem lt_iff_le_pred : ∀ {n}, 0 < n → (m < n ↔ m ≤ n - 1) | _ + 1, _ => Nat.lt_succ_iff

-- TODO: state LHS using `- 1` instead?
theorem le_of_pred_lt : ∀ {m}, pred m < n → m ≤ n
  | 0 => Nat.le_of_lt
  | _ + 1 => id

theorem lt_iff_add_one_le : m < n ↔ m + 1 ≤ n := by rw [succ_le_iff]

theorem lt_one_add_iff : m < 1 + n ↔ m ≤ n := by simp only [Nat.add_comm, Nat.lt_succ_iff]

theorem one_add_le_iff : 1 + m ≤ n ↔ m < n := by simp only [Nat.add_comm, add_one_le_iff]

theorem one_le_iff_ne_zero : 1 ≤ n ↔ n ≠ 0 := Nat.pos_iff_ne_zero

theorem one_lt_iff_ne_zero_and_ne_one : ∀ {n : Nat}, 1 < n ↔ n ≠ 0 ∧ n ≠ 1
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by omega

theorem le_one_iff_eq_zero_or_eq_one : ∀ {n : Nat}, n ≤ 1 ↔ n = 0 ∨ n = 1 := by simp [le_succ_iff]

theorem one_le_of_lt (h : a < b) : 1 ≤ b := Nat.lt_of_le_of_lt (Nat.zero_le _) h

theorem pred_one_add (n : Nat) : pred (1 + n) = n := by rw [Nat.add_comm, add_one, Nat.pred_succ]

theorem pred_eq_self_iff : n.pred = n ↔ n = 0 := by cases n <;> simp [(Nat.succ_ne_self _).symm]

theorem pred_eq_of_eq_succ {m n : Nat} (H : m = n.succ) : m.pred = n := by simp [H]

@[simp] theorem pred_eq_succ_iff : n - 1 = m + 1 ↔ n = m + 2 := by
  cases n <;> constructor <;> rintro ⟨⟩ <;> rfl

@[simp] theorem add_succ_sub_one (m n : Nat) : m + succ n - 1 = m + n := rfl

@[simp]
theorem succ_add_sub_one (n m : Nat) : succ m + n - 1 = m + n := by rw [succ_add, Nat.add_one_sub_one]

theorem pred_sub (n m : Nat) : pred n - m = pred (n - m) := by
  rw [← Nat.sub_one, Nat.sub_sub, one_add, sub_succ]

theorem self_add_sub_one : ∀ n, n + (n - 1) = 2 * n - 1
  | 0 => rfl
  | n + 1 => by rw [Nat.two_mul]; exact (add_succ_sub_one (Nat.succ _) _).symm

theorem sub_one_add_self (n : Nat) : (n - 1) + n = 2 * n - 1 := Nat.add_comm _ n ▸ self_add_sub_one n

theorem self_add_pred (n : Nat) : n + pred n = (2 * n).pred := self_add_sub_one n
theorem pred_add_self (n : Nat) : pred n + n = (2 * n).pred := sub_one_add_self n

theorem pred_le_iff : pred m ≤ n ↔ m ≤ succ n :=
  ⟨le_succ_of_pred_le, by
    cases m
    · exact fun _ ↦ zero_le n
    · exact le_of_succ_le_succ⟩

theorem lt_of_lt_pred (h : m < n - 1) : m < n := by omega

theorem le_add_pred_of_pos (a : Nat) (hb : b ≠ 0) : a ≤ b + (a - 1) := by omega

theorem lt_pred_iff : a < pred b ↔ succ a < b := by simp; omega

/-! ## add -/

protected theorem add_add_add_comm (a b c d : Nat) : (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_left_comm b]

theorem succ_eq_one_add (n) : succ n = 1 + n := (one_add _).symm

theorem succ_add_eq_add_succ (a b) : succ a + b = a + succ b := Nat.succ_add ..

protected theorem eq_zero_of_add_eq_zero_right (h : n + m = 0) : n = 0 :=
  (Nat.eq_zero_of_add_eq_zero h).1

protected theorem add_eq_zero_iff : n + m = 0 ↔ n = 0 ∧ m = 0 :=
  ⟨Nat.eq_zero_of_add_eq_zero, fun ⟨h₁, h₂⟩ => h₂.symm ▸ h₁⟩

@[simp high] protected theorem add_left_cancel_iff {n : Nat} : n + m = n + k ↔ m = k :=
  ⟨Nat.add_left_cancel, fun | rfl => rfl⟩

@[simp high] protected theorem add_right_cancel_iff {n : Nat} : m + n = k + n ↔ m = k :=
  ⟨Nat.add_right_cancel, fun | rfl => rfl⟩

protected theorem add_left_inj {n : Nat} : m + n = k + n ↔ m = k := Nat.add_right_cancel_iff
protected theorem add_right_inj {n : Nat} : n + m = n + k ↔ m = k := Nat.add_left_cancel_iff

@[simp high] protected theorem add_eq_left {a b : Nat} : a + b = a ↔ b = 0 := by omega
@[simp high] protected theorem add_eq_right {a b : Nat} : a + b = b ↔ a = 0 := by omega
@[simp high] protected theorem left_eq_add {a b : Nat} : a = a + b ↔ b = 0 := by omega
@[simp high] protected theorem right_eq_add {a b : Nat} : b = a + b ↔ a = 0 := by omega

@[deprecated Nat.add_eq_right (since := "2025-04-15")]
protected theorem add_left_eq_self  {a b : Nat} : a + b = b ↔ a = 0 := Nat.add_eq_right
@[deprecated Nat.add_eq_left (since := "2025-04-15")]
protected theorem add_right_eq_self {a b : Nat} : a + b = a ↔ b = 0 := Nat.add_eq_left
@[deprecated Nat.left_eq_add (since := "2025-04-15")]
protected theorem self_eq_add_right {a b : Nat} : a = a + b ↔ b = 0 := Nat.left_eq_add
@[deprecated Nat.right_eq_add (since := "2025-04-15")]
protected theorem self_eq_add_left  {a b : Nat} : a = b + a ↔ b = 0 := Nat.right_eq_add

protected theorem lt_of_add_lt_add_right : ∀ {n : Nat}, k + n < m + n → k < m
  | 0, h => h
  | _+1, h => Nat.lt_of_add_lt_add_right (Nat.lt_of_succ_lt_succ h)

protected theorem lt_of_add_lt_add_left {n : Nat} : n + k < n + m → k < m := by
  rw [Nat.add_comm n, Nat.add_comm n]; exact Nat.lt_of_add_lt_add_right

@[simp] protected theorem add_lt_add_iff_left {k n m : Nat} : k + n < k + m ↔ n < m :=
  ⟨Nat.lt_of_add_lt_add_left, fun h => Nat.add_lt_add_left h _⟩

@[simp] protected theorem add_lt_add_iff_right {k n m : Nat} : n + k < m + k ↔ n < m :=
  ⟨Nat.lt_of_add_lt_add_right, fun h => Nat.add_lt_add_right h _⟩

protected theorem add_lt_add_of_le_of_lt {a b c d : Nat} (hle : a ≤ b) (hlt : c < d) :
    a + c < b + d :=
  Nat.lt_of_le_of_lt (Nat.add_le_add_right hle _) (Nat.add_lt_add_left hlt _)

protected theorem add_lt_add_of_lt_of_le {a b c d : Nat} (hlt : a < b) (hle : c ≤ d) :
    a + c < b + d :=
  Nat.lt_of_le_of_lt (Nat.add_le_add_left hle _) (Nat.add_lt_add_right hlt _)

protected theorem pos_of_lt_add_right (h : n < n + k) : 0 < k :=
  Nat.lt_of_add_lt_add_left h

protected theorem pos_of_lt_add_left : n < k + n → 0 < k := by
  rw [Nat.add_comm]; exact Nat.pos_of_lt_add_right

@[simp] protected theorem lt_add_right_iff_pos : n < n + k ↔ 0 < k :=
  ⟨Nat.pos_of_lt_add_right, Nat.lt_add_of_pos_right⟩

@[simp] protected theorem lt_add_left_iff_pos : n < k + n ↔ 0 < k :=
  ⟨Nat.pos_of_lt_add_left, Nat.lt_add_of_pos_left⟩

protected theorem add_pos_left (h : 0 < m) (n) : 0 < m + n :=
  Nat.lt_of_lt_of_le h (Nat.le_add_right ..)

protected theorem add_self_ne_one : ∀ n, n + n ≠ 1
  | n+1, h => by rw [Nat.succ_add, Nat.succ.injEq] at h; contradiction

theorem le_iff_lt_add_one : x ≤ y ↔ x < y + 1 := by
  omega

@[simp high] protected theorem add_eq_zero : m + n = 0 ↔ m = 0 ∧ n = 0 := by omega

theorem add_pos_iff_pos_or_pos : 0 < m + n ↔ 0 < m ∨ 0 < n := by omega

theorem add_eq_one_iff : m + n = 1 ↔ m = 0 ∧ n = 1 ∨ m = 1 ∧ n = 0 := by omega

theorem add_eq_two_iff : m + n = 2 ↔ m = 0 ∧ n = 2 ∨ m = 1 ∧ n = 1 ∨ m = 2 ∧ n = 0 := by
  omega

theorem add_eq_three_iff :
    m + n = 3 ↔ m = 0 ∧ n = 3 ∨ m = 1 ∧ n = 2 ∨ m = 2 ∧ n = 1 ∨ m = 3 ∧ n = 0 := by
  omega

theorem le_add_one_iff : m ≤ n + 1 ↔ m ≤ n ∨ m = n + 1 := by omega

theorem le_and_le_add_one_iff : n ≤ m ∧ m ≤ n + 1 ↔ m = n ∨ m = n + 1 := by omega

theorem add_succ_lt_add (hab : a < b) (hcd : c < d) : a + c + 1 < b + d := by omega

theorem le_or_le_of_add_eq_add_pred (h : a + c = b + d - 1) : b ≤ a ∨ d ≤ c := by omega

/-! ## sub -/

protected theorem one_sub : ∀ n, 1 - n = if n = 0 then 1 else 0
  | 0 => rfl
  | _+1 => by rw [if_neg (Nat.succ_ne_zero _), Nat.succ_sub_succ, Nat.zero_sub]

theorem succ_sub_sub_succ (n m k) : succ n - m - succ k = n - m - k := by
  rw [Nat.sub_sub, Nat.sub_sub, add_succ, succ_sub_succ]

theorem add_sub_sub_add_right (n m k l : Nat) :
    (n + l) - m - (k + l) = n - m - k := by
  rw [Nat.sub_sub, Nat.sub_sub, ←Nat.add_assoc, Nat.add_sub_add_right]

protected theorem sub_right_comm (m n k : Nat) : m - n - k = m - k - n := by
  rw [Nat.sub_sub, Nat.sub_sub, Nat.add_comm]

protected theorem add_sub_cancel_right (n m : Nat) : (n + m) - m = n := Nat.add_sub_cancel ..

@[simp] protected theorem add_sub_cancel' {n m : Nat} (h : m ≤ n) : m + (n - m) = n := by
  rw [Nat.add_comm, Nat.sub_add_cancel h]

theorem succ_sub_one (n) : succ n - 1 = n := rfl

protected theorem one_add_sub_one (n : Nat) : (1 + n) - 1 = n := Nat.add_sub_cancel_left 1 _

protected theorem sub_sub_self {n m : Nat} (h : m ≤ n) : n - (n - m) = m :=
  (Nat.sub_eq_iff_eq_add (Nat.sub_le ..)).2 (Nat.add_sub_of_le h).symm

protected theorem sub_add_comm {n m k : Nat} (h : k ≤ n) : n + m - k = n - k + m := by
  rw [Nat.sub_eq_iff_eq_add (Nat.le_trans h (Nat.le_add_right ..))]
  rwa [Nat.add_right_comm, Nat.sub_add_cancel]

protected theorem sub_eq_zero_iff_le : n - m = 0 ↔ n ≤ m :=
  ⟨Nat.le_of_sub_eq_zero, Nat.sub_eq_zero_of_le⟩

protected theorem sub_pos_iff_lt : 0 < n - m ↔ m < n :=
  ⟨Nat.lt_of_sub_pos, Nat.sub_pos_of_lt⟩

@[simp] protected theorem sub_le_iff_le_add {a b c : Nat} : a - b ≤ c ↔ a ≤ c + b :=
  ⟨Nat.le_add_of_sub_le, sub_le_of_le_add⟩

protected theorem sub_le_iff_le_add' {a b c : Nat} : a - b ≤ c ↔ a ≤ b + c := by
  rw [Nat.add_comm, Nat.sub_le_iff_le_add]

protected theorem le_sub_iff_add_le {n : Nat} (h : k ≤ m) : n ≤ m - k ↔ n + k ≤ m :=
  ⟨Nat.add_le_of_le_sub h, Nat.le_sub_of_add_le⟩

theorem add_lt_iff_lt_sub_right {a b c : Nat} : a + b < c ↔ a < c - b := by
  omega

protected theorem add_le_of_le_sub' {n k m : Nat} (h : m ≤ k) : n ≤ k - m → m + n ≤ k :=
  Nat.add_comm .. ▸ Nat.add_le_of_le_sub h

protected theorem le_sub_of_add_le' {n k m : Nat} : m + n ≤ k → n ≤ k - m :=
  Nat.add_comm .. ▸ Nat.le_sub_of_add_le

protected theorem le_sub_iff_add_le' {n : Nat} (h : k ≤ m) : n ≤ m - k ↔ k + n ≤ m :=
  ⟨Nat.add_le_of_le_sub' h, Nat.le_sub_of_add_le'⟩

protected theorem le_of_sub_le_sub_left : ∀ {n k m : Nat}, n ≤ k → k - m ≤ k - n → n ≤ m
  | 0, _, _, _, _ => Nat.zero_le ..
  | _+1, _, 0, h₀, h₁ =>
    absurd (Nat.sub_lt (Nat.zero_lt_of_lt h₀) (Nat.zero_lt_succ _)) (Nat.not_lt.2 h₁)
  | _+1, _+1, _+1, h₀, h₁ => by
    simp only [Nat.succ_sub_succ] at h₁
    exact succ_le_succ <| Nat.le_of_sub_le_sub_left (Nat.le_of_succ_le_succ h₀) h₁

protected theorem sub_le_sub_iff_left {n m k : Nat} (h : n ≤ k) : k - m ≤ k - n ↔ n ≤ m :=
  ⟨Nat.le_of_sub_le_sub_left h, fun h => Nat.sub_le_sub_left h _⟩

protected theorem sub_lt_of_pos_le (h₀ : 0 < a) (h₁ : a ≤ b) : b - a < b :=
  Nat.sub_lt (Nat.lt_of_lt_of_le h₀ h₁) h₀
protected abbrev sub_lt_self := @Nat.sub_lt_of_pos_le

theorem add_lt_of_lt_sub' {a b c : Nat} : b < c - a → a + b < c := by
  rw [Nat.add_comm]; exact Nat.add_lt_of_lt_sub

protected theorem sub_add_lt_sub (h₁ : m + k ≤ n) (h₂ : 0 < k) : n - (m + k) < n - m := by
  rw [← Nat.sub_sub]; exact Nat.sub_lt_of_pos_le h₂ (Nat.le_sub_of_add_le' h₁)

theorem sub_one_lt_of_le (h₀ : 0 < a) (h₁ : a ≤ b) : a - 1 < b :=
  Nat.lt_of_lt_of_le (Nat.pred_lt_of_lt h₀) h₁

theorem sub_lt_succ (a b) : a - b < succ a := lt_succ_of_le (sub_le a b)

theorem sub_lt_add_one (a b) : a - b < a + 1 := lt_add_one_of_le (sub_le a b)

theorem sub_one_sub_lt (h : i < n) : n - 1 - i < n := by
  rw [Nat.sub_right_comm]; exact Nat.sub_one_lt_of_le (Nat.sub_pos_of_lt h) (Nat.sub_le ..)

protected theorem exists_eq_add_of_le (h : m ≤ n) : ∃ k : Nat, n = m + k :=
  ⟨n - m, (add_sub_of_le h).symm⟩

protected theorem exists_eq_add_of_le' (h : m ≤ n) : ∃ k : Nat, n = k + m :=
  ⟨n - m, (Nat.sub_add_cancel h).symm⟩

protected theorem exists_eq_add_of_lt (h : m < n) : ∃ k : Nat, n = m + k + 1 :=
  ⟨n - (m + 1), by rw [Nat.add_right_comm, add_sub_of_le h]⟩

/-- A version of `Nat.sub_succ` in the form `_ - 1` instead of `Nat.pred _`. -/
theorem sub_succ' (m n : Nat) : m - n.succ = m - n - 1 := rfl

protected theorem sub_eq_of_eq_add' {a b c : Nat} (h : a = b + c) : a - b = c := by omega
protected theorem eq_sub_of_add_eq {a b c : Nat} (h : c + b = a) : c = a - b := by omega
protected theorem eq_sub_of_add_eq' {a b c : Nat} (h : b + c = a) : c = a - b := by omega

protected theorem lt_sub_iff_add_lt {a b c : Nat} : a < c - b ↔ a + b < c := ⟨add_lt_of_lt_sub, lt_sub_of_add_lt⟩
protected theorem lt_sub_iff_add_lt' {a b c : Nat} : a < c - b ↔ b + a < c := by omega
protected theorem sub_lt_iff_lt_add {a b c : Nat} (hba : b ≤ a) : a - b < c ↔ a < c + b := by omega
protected theorem sub_lt_iff_lt_add' {a b c : Nat} (hba : b ≤ a) : a - b < c ↔ a < b + c := by omega

-- TODO: variants
protected theorem sub_sub_sub_cancel_right {a b c : Nat} (h : c ≤ b) : a - c - (b - c) = a - b := by omega
protected theorem add_sub_sub_cancel {a b c : Nat} (h : c ≤ a) : a + b - (a - c) = b + c := by omega
protected theorem sub_add_sub_cancel {a b c : Nat} (hab : b ≤ a) (hcb : c ≤ b) : a - b + (b - c) = a - c := by omega

protected theorem sub_lt_sub_iff_right {a b c : Nat} (h : c ≤ a) : a - c < b - c ↔ a < b := by omega

/-! ### min/max -/

theorem succ_min_succ (x y) : min (succ x) (succ y) = succ (min x y) := by
  cases Nat.le_total x y with
  | inl h => rw [Nat.min_eq_left h, Nat.min_eq_left (Nat.succ_le_succ h)]
  | inr h => rw [Nat.min_eq_right h, Nat.min_eq_right (Nat.succ_le_succ h)]

protected theorem min_self (a : Nat) : min a a = a := by simp
instance : Std.IdempotentOp (α := Nat) min := ⟨Nat.min_self⟩

@[simp] protected theorem min_assoc : ∀ (a b c : Nat), min (min a b) c = min a (min b c)
  | 0, _, _ => by rw [Nat.zero_min, Nat.zero_min, Nat.zero_min]
  | _, 0, _ => by rw [Nat.zero_min, Nat.min_zero, Nat.zero_min]
  | _, _, 0 => by rw [Nat.min_zero, Nat.min_zero, Nat.min_zero]
  | _+1, _+1, _+1 => by simp only [Nat.succ_min_succ]; exact congrArg succ <| Nat.min_assoc ..
instance : Std.Associative (α := Nat) min := ⟨Nat.min_assoc⟩

@[simp] protected theorem min_self_assoc {m n : Nat} : min m (min m n) = min m n := by
  rw [← Nat.min_assoc, Nat.min_self]

@[simp] protected theorem min_self_assoc' {m n : Nat} : min n (min m n) = min n m := by
  rw [Nat.min_comm m n, ← Nat.min_assoc, Nat.min_self]

theorem min_add_left_self {a b : Nat} : min a (b + a) = a := by
  simp
theorem min_add_right_self {a b : Nat} : min a (a + b) = a := by
  simp
theorem add_left_min_self {a b : Nat} : min (b + a) a = a := by
  simp
theorem add_right_min_self {a b : Nat} : min (a + b) a = a := by
  simp

protected theorem sub_sub_eq_min : ∀ (a b : Nat), a - (a - b) = min a b
  | 0, _ => by rw [Nat.zero_sub, Nat.zero_min]
  | _, 0 => by rw [Nat.sub_zero, Nat.sub_self, Nat.min_zero]
  | _+1, _+1 => by
    rw [Nat.succ_sub_succ, Nat.succ_min_succ, Nat.succ_sub (Nat.sub_le ..)]
    exact congrArg succ <| Nat.sub_sub_eq_min ..

protected theorem sub_eq_sub_min (n m : Nat) : n - m = n - min n m := by
  cases Nat.le_total n m with
  | inl h => rw [Nat.min_eq_left h, Nat.sub_eq_zero_of_le h, Nat.sub_self]
  | inr h => rw [Nat.min_eq_right h]

@[simp] protected theorem sub_add_min_cancel (n m : Nat) : n - m + min n m = n := by
  rw [Nat.sub_eq_sub_min, Nat.sub_add_cancel (Nat.min_le_left ..)]

protected theorem succ_max_succ (x y) : max (succ x) (succ y) = succ (max x y) := by
  cases Nat.le_total x y with
  | inl h => rw [Nat.max_eq_right h, Nat.max_eq_right (Nat.succ_le_succ h)]
  | inr h => rw [Nat.max_eq_left h, Nat.max_eq_left (Nat.succ_le_succ h)]

protected theorem max_self (a : Nat) : max a a = a := by simp
instance : Std.IdempotentOp (α := Nat) max := ⟨Nat.max_self⟩

instance : Std.LawfulIdentity (α := Nat) max 0 where
  left_id := Nat.zero_max
  right_id := Nat.max_zero

@[simp] protected theorem max_assoc : ∀ (a b c : Nat), max (max a b) c = max a (max b c)
  | 0, _, _ => by rw [Nat.zero_max, Nat.zero_max]
  | _, 0, _ => by rw [Nat.zero_max, Nat.max_zero]
  | _, _, 0 => by rw [Nat.max_zero, Nat.max_zero]
  | _+1, _+1, _+1 => by simp only [Nat.succ_max_succ]; exact congrArg succ <| Nat.max_assoc ..
instance : Std.Associative (α := Nat) max := ⟨Nat.max_assoc⟩

theorem max_add_left_self {a b : Nat} : max a (b + a) = b + a := by
  simp
theorem max_add_right_self {a b : Nat} : max a (a + b) = a + b := by
  simp
theorem add_left_max_self {a b : Nat} : max (b + a) a = b + a := by
  simp
theorem add_right_max_self {a b : Nat} : max (a + b) a = a + b := by
  simp

protected theorem sub_add_eq_max (a b : Nat) : a - b + b = max a b := by
  match Nat.le_total a b with
  | .inl hl => rw [Nat.max_eq_right hl, Nat.sub_eq_zero_iff_le.mpr hl, Nat.zero_add]
  | .inr hr => rw [Nat.max_eq_left hr, Nat.sub_add_cancel hr]

protected theorem sub_eq_max_sub (n m : Nat) : n - m = max n m - m := by
  cases Nat.le_total m n with
  | inl h => rw [Nat.max_eq_left h]
  | inr h => rw [Nat.max_eq_right h, Nat.sub_eq_zero_of_le h, Nat.sub_self]

protected theorem max_min_distrib_left : ∀ (a b c : Nat), max a (min b c) = min (max a b) (max a c)
  | 0, _, _ => by simp only [Nat.zero_max]
  | _, 0, _ => by
    rw [Nat.zero_min, Nat.max_zero]
    exact Nat.min_eq_left (Nat.le_max_left ..) |>.symm
  | _, _, 0 => by
    rw [Nat.min_zero, Nat.max_zero]
    exact Nat.min_eq_right (Nat.le_max_left ..) |>.symm
  | _+1, _+1, _+1 => by
    simp only [Nat.succ_max_succ, Nat.succ_min_succ]
    exact congrArg succ <| Nat.max_min_distrib_left ..

protected theorem min_max_distrib_left : ∀ (a b c : Nat), min a (max b c) = max (min a b) (min a c)
  | 0, _, _ => by simp only [Nat.zero_min, Nat.max_self]
  | _, 0, _ => by simp only [Nat.min_zero, Nat.zero_max]
  | _, _, 0 => by simp only [Nat.min_zero, Nat.max_zero]
  | _+1, _+1, _+1 => by
    simp only [Nat.succ_max_succ, Nat.succ_min_succ]
    exact congrArg succ <| Nat.min_max_distrib_left ..

protected theorem max_min_distrib_right (a b c : Nat) :
    max (min a b) c = min (max a c) (max b c) := by
  repeat rw [Nat.max_comm _ c]
  exact Nat.max_min_distrib_left ..

protected theorem min_max_distrib_right (a b c : Nat) :
    min (max a b) c = max (min a c) (min b c) := by
  repeat rw [Nat.min_comm _ c]
  exact Nat.min_max_distrib_left ..

protected theorem pred_min_pred : ∀ (x y), min (pred x) (pred y) = pred (min x y)
  | 0, _ => by simp only [Nat.pred_zero, Nat.zero_min]
  | _, 0 => by simp only [Nat.pred_zero, Nat.min_zero]
  | _+1, _+1 => by simp only [Nat.pred_succ, Nat.succ_min_succ]

protected theorem pred_max_pred : ∀ (x y), max (pred x) (pred y) = pred (max x y)
  | 0, _ => by simp only [Nat.pred_zero, Nat.zero_max]
  | _, 0 => by simp only [Nat.pred_zero, Nat.max_zero]
  | _+1, _+1 => by simp only [Nat.pred_succ, Nat.succ_max_succ]

protected theorem sub_min_sub_right : ∀ (a b c : Nat), min (a - c) (b - c) = min a b - c
  | _, _, 0 => rfl
  | _, _, _+1 => Eq.trans (Nat.pred_min_pred ..) <| congrArg _ (Nat.sub_min_sub_right ..)

protected theorem sub_max_sub_right : ∀ (a b c : Nat), max (a - c) (b - c) = max a b - c
  | _, _, 0 => rfl
  | _, _, _+1 => Eq.trans (Nat.pred_max_pred ..) <| congrArg _ (Nat.sub_max_sub_right ..)

protected theorem sub_min_sub_left (a b c : Nat) : min (a - b) (a - c) = a - max b c := by
  omega

protected theorem sub_max_sub_left (a b c : Nat) : max (a - b) (a - c) = a - min b c := by
  omega

protected theorem min_left_comm (a b c : Nat) : min a (min b c) = min b (min a c) := by
  rw [← Nat.min_assoc, ← Nat.min_assoc, b.min_comm]

protected theorem max_left_comm (a b c : Nat) : max a (max b c) = max b (max a c) := by
  rw [← Nat.max_assoc, ← Nat.max_assoc, b.max_comm]

protected theorem min_right_comm (a b c : Nat) : min (min a b) c = min (min a c) b := by
  rw [Nat.min_assoc, Nat.min_assoc, b.min_comm]

protected theorem max_right_comm (a b c : Nat) : max (max a b) c = max (max a c) b := by
  rw [Nat.max_assoc, Nat.max_assoc, b.max_comm]

@[simp] theorem min_eq_zero_iff : min m n = 0 ↔ m = 0 ∨ n = 0 := by omega
@[simp] theorem max_eq_zero_iff : max m n = 0 ↔ m = 0 ∧ n = 0 := by omega

theorem add_eq_max_iff : m + n = max m n ↔ m = 0 ∨ n = 0 := by omega
theorem add_eq_min_iff : m + n = min m n ↔ m = 0 ∧ n = 0 := by omega

/-! ### mul -/

protected theorem mul_right_comm (n m k : Nat) : n * m * k = n * k * m := by
  rw [Nat.mul_assoc, Nat.mul_comm m, ← Nat.mul_assoc]

protected theorem mul_mul_mul_comm (a b c d : Nat) : (a * b) * (c * d) = (a * c) * (b * d) := by
  rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_left_comm b]

theorem mul_eq_zero : ∀ {m n}, n * m = 0 ↔ n = 0 ∨ m = 0
  | 0, _ => ⟨fun _ => .inr rfl, fun _ => rfl⟩
  | _, 0 => ⟨fun _ => .inl rfl, fun _ => Nat.zero_mul ..⟩
  | _+1, _+1 => ⟨nofun, nofun⟩

protected theorem mul_ne_zero_iff : n * m ≠ 0 ↔ n ≠ 0 ∧ m ≠ 0 := by rw [ne_eq, mul_eq_zero, not_or]

protected theorem mul_ne_zero : n ≠ 0 → m ≠ 0 → n * m ≠ 0 := (Nat.mul_ne_zero_iff.2 ⟨·,·⟩)

protected theorem ne_zero_of_mul_ne_zero_left (h : n * m ≠ 0) : n ≠ 0 :=
  (Nat.mul_ne_zero_iff.1 h).1

protected theorem mul_left_cancel {n m k : Nat} (np : 0 < n) (h : n * m = n * k) : m = k := by
  match Nat.lt_trichotomy m k with
  | Or.inl p =>
    have r : n * m < n * k := Nat.mul_lt_mul_of_pos_left p np
    simp [h] at r
  | Or.inr (Or.inl p) => exact p
  | Or.inr (Or.inr p) =>
    have r : n * k < n * m := Nat.mul_lt_mul_of_pos_left p np
    simp [h] at r

protected theorem mul_right_cancel {n m k : Nat} (mp : 0 < m) (h : n * m = k * m) : n = k := by
  simp [Nat.mul_comm _ m] at h
  apply Nat.mul_left_cancel mp h

protected theorem mul_left_cancel_iff {n : Nat} (p : 0 < n) {m k : Nat} : n * m = n * k ↔ m = k :=
  ⟨Nat.mul_left_cancel p, fun | rfl => rfl⟩

protected theorem mul_right_cancel_iff {m : Nat} (p : 0 < m) {n k : Nat} : n * m = k * m ↔ n = k :=
  ⟨Nat.mul_right_cancel p, fun | rfl => rfl⟩

protected theorem ne_zero_of_mul_ne_zero_right (h : n * m ≠ 0) : m ≠ 0 :=
  (Nat.mul_ne_zero_iff.1 h).2

protected theorem le_mul_of_pos_left (m) (h : 0 < n) : m ≤ n * m :=
  Nat.le_trans (Nat.le_of_eq (Nat.one_mul _).symm) (Nat.mul_le_mul_right _ h)

protected theorem le_mul_of_pos_right (n) (h : 0 < m) : n ≤ n * m :=
  Nat.le_trans (Nat.le_of_eq (Nat.mul_one _).symm) (Nat.mul_le_mul_left _ h)

protected theorem mul_lt_mul_of_lt_of_le (hac : a < c) (hbd : b ≤ d) (hd : 0 < d) :
    a * b < c * d :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ hbd) (Nat.mul_lt_mul_of_pos_right hac hd)

protected theorem mul_lt_mul_of_lt_of_le' (hac : a < c) (hbd : b ≤ d) (hb : 0 < b) :
    a * b < c * d :=
  Nat.mul_lt_mul_of_lt_of_le hac hbd (Nat.lt_of_lt_of_le hb hbd)

protected theorem mul_lt_mul_of_le_of_lt (hac : a ≤ c) (hbd : b < d) (hc : 0 < c) :
    a * b < c * d :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ hac) (Nat.mul_lt_mul_of_pos_left hbd hc)

protected theorem mul_lt_mul_of_le_of_lt' (hac : a ≤ c) (hbd : b < d) (ha : 0 < a) :
    a * b < c * d :=
  Nat.mul_lt_mul_of_le_of_lt hac hbd (Nat.lt_of_lt_of_le ha hac)

protected theorem mul_lt_mul_of_lt_of_lt {a b c d : Nat} (hac : a < c) (hbd : b < d) :
    a * b < c * d :=
  Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hac) hbd (Nat.zero_lt_of_lt hac)

theorem succ_mul_succ (a b) : succ a * succ b = a * b + a + b + 1 := by
  rw [succ_mul, mul_succ]; rfl

theorem add_one_mul_add_one (a b : Nat) : (a + 1) * (b + 1) = a * b + a + b + 1 := by
  rw [add_one_mul, mul_add_one]; rfl

theorem mul_le_add_right {m k n : Nat} : k * m ≤ m + n ↔ (k-1) * m ≤ n := by
  match k with
  | 0 =>
    simp
  | succ k =>
    simp [succ_mul, Nat.add_comm _ m, Nat.add_le_add_iff_left]

theorem succ_mul_succ_eq (a b : Nat) : succ a * succ b = a * b + a + b + 1 := by
  rw [mul_succ, succ_mul, Nat.add_right_comm _ a]; rfl

protected theorem mul_self_sub_mul_self_eq (a b : Nat) : a * a - b * b = (a + b) * (a - b) := by
  rw [Nat.mul_sub_left_distrib, Nat.right_distrib, Nat.right_distrib, Nat.mul_comm b a,
    Nat.sub_add_eq, Nat.add_sub_cancel]

protected theorem pos_of_mul_pos_left {a b : Nat} (h : 0 < a * b) : 0 < b := by
  apply Decidable.by_contra
  intros
  simp_all

protected theorem pos_of_mul_pos_right {a b : Nat} (h : 0 < a * b) : 0 < a := by
  apply Decidable.by_contra
  intros
  simp_all

@[simp] protected theorem mul_pos_iff_of_pos_left {a b : Nat} (h : 0 < a) :
    0 < a * b ↔ 0 < b :=
  ⟨Nat.pos_of_mul_pos_left, Nat.mul_pos h⟩

@[simp] protected theorem mul_pos_iff_of_pos_right {a b : Nat} (h : 0 < b) :
    0 < a * b ↔ 0 < a :=
  ⟨Nat.pos_of_mul_pos_right, fun w => Nat.mul_pos w h⟩

protected theorem pos_of_lt_mul_left {a b c : Nat} (h : a < b * c) : 0 < c := by
  replace h : 0 < b * c := by omega
  exact Nat.pos_of_mul_pos_left h

protected theorem pos_of_lt_mul_right {a b c : Nat} (h : a < b * c) : 0 < b := by
  replace h : 0 < b * c := by omega
  exact Nat.pos_of_mul_pos_right h

protected theorem mul_dvd_mul_iff_left {a b c : Nat} (h : 0 < a) : a * b ∣ a * c ↔ b ∣ c :=
  ⟨fun ⟨k, hk⟩ => ⟨k, Nat.mul_left_cancel h (Nat.mul_assoc _ _ _ ▸ hk)⟩, Nat.mul_dvd_mul_left _⟩

protected theorem mul_dvd_mul_iff_right {a b c : Nat} (h : 0 < c) : a * c ∣ b * c ↔ a ∣ b := by
  rw [Nat.mul_comm _ c, Nat.mul_comm _ c, Nat.mul_dvd_mul_iff_left h]

protected theorem zero_eq_mul : 0 = m * n ↔ m = 0 ∨ n = 0 := by rw [eq_comm, Nat.mul_eq_zero]

-- TODO: Replace `Nat.mul_right_cancel_iff` with `Nat.mul_left_inj`
protected theorem mul_left_inj (ha : a ≠ 0) : b * a = c * a ↔ b = c :=
  Nat.mul_right_cancel_iff (Nat.pos_iff_ne_zero.2 ha)

-- TODO: Replace `Nat.mul_left_cancel_iff` with `Nat.mul_right_inj`
protected theorem mul_right_inj (ha : a ≠ 0) : a * b = a * c ↔ b = c :=
  Nat.mul_left_cancel_iff (Nat.pos_iff_ne_zero.2 ha)

protected theorem mul_ne_mul_left (ha : a ≠ 0) : b * a ≠ c * a ↔ b ≠ c :=
  not_congr (Nat.mul_left_inj ha)

protected theorem mul_ne_mul_right (ha : a ≠ 0) : a * b ≠ a * c ↔ b ≠ c :=
  not_congr (Nat.mul_right_inj ha)

theorem mul_eq_left (ha : a ≠ 0) : a * b = a ↔ b = 1 := by simpa using Nat.mul_right_inj ha (c := 1)
theorem mul_eq_right (hb : b ≠ 0) : a * b = b ↔ a = 1 := by simpa using Nat.mul_left_inj hb (c := 1)

/-- The product of two natural numbers is greater than 1 if and only if
  at least one of them is greater than 1 and both are positive. -/
theorem one_lt_mul_iff : 1 < m * n ↔ 0 < m ∧ 0 < n ∧ (1 < m ∨ 1 < n) := by
  constructor <;> intro h
  · refine Decidable.by_contra (fun h' => ?_)
    simp only [Nat.le_zero, Decidable.not_and_iff_not_or_not, not_or, Nat.not_lt] at h'
    obtain rfl | rfl | h' := h'
    · simp at h
    · simp at h
    · exact Nat.not_lt_of_le (Nat.mul_le_mul h'.1 h'.2) h
  · obtain hm | hn := h.2.2
    · exact Nat.mul_lt_mul_of_lt_of_le' hm h.2.1 Nat.zero_lt_one
    · exact Nat.mul_lt_mul_of_le_of_lt h.1 hn h.1

theorem eq_one_of_mul_eq_one_right (H : m * n = 1) : m = 1 := eq_one_of_dvd_one ⟨n, H.symm⟩

theorem eq_one_of_mul_eq_one_left (H : m * n = 1) : n = 1 :=
  eq_one_of_mul_eq_one_right (n := m) (by rwa [Nat.mul_comm])

@[simp] protected theorem lt_mul_iff_one_lt_left (hb : 0 < b) : b < a * b ↔ 1 < a := by
  simpa using Nat.mul_lt_mul_right (b := 1) hb

@[simp] protected theorem lt_mul_iff_one_lt_right (ha : 0 < a) : a < a * b ↔ 1 < b := by
  simpa using Nat.mul_lt_mul_left (b := 1) ha

theorem eq_zero_of_two_mul_le (h : 2 * n ≤ n) : n = 0 := by omega

theorem eq_zero_of_mul_le (hb : 2 ≤ n) (h : n * m ≤ m) : m = 0 :=
  eq_zero_of_two_mul_le <| Nat.le_trans (Nat.mul_le_mul_right _ hb) h

theorem succ_mul_pos (m : Nat) (hn : 0 < n) : 0 < succ m * n := Nat.mul_pos m.succ_pos hn

theorem mul_self_le_mul_self {m n : Nat} (h : m ≤ n) : m * m ≤ n * n := Nat.mul_le_mul h h

-- This name is consistent with mathlib's top level definitions for groups with zero, where there
-- are `mul_lt_mul`, `mul_lt_mul'` and `mul_lt_mul''`, all with different sets of hypotheses.
theorem mul_lt_mul'' {a b c d : Nat} (hac : a < c) (hbd : b < d) : a * b < c * d :=
  Nat.mul_lt_mul_of_lt_of_le hac (Nat.le_of_lt hbd) <| by omega

protected theorem lt_iff_lt_of_mul_eq_mul (ha : a ≠ 0) (hbd : a = b * d) (hce : a = c * e) :
    c < b ↔ d < e where
  mp hcb := Nat.lt_of_not_le fun hed ↦ Nat.not_lt_of_le (Nat.le_of_eq <| hbd.symm.trans hce) <|
    Nat.mul_lt_mul_of_lt_of_le hcb hed <| by simp [hbd, Nat.mul_eq_zero] at ha; omega
  mpr hde := Nat.lt_of_not_le fun hbc ↦ Nat.not_lt_of_le (Nat.le_of_eq <| hce.symm.trans hbd) <|
    Nat.mul_lt_mul_of_le_of_lt hbc hde <| by simp [hce, Nat.mul_eq_zero] at ha; omega

theorem mul_self_lt_mul_self {m n : Nat} (h : m < n) : m * m < n * n := mul_lt_mul'' h h

theorem mul_self_le_mul_self_iff {m n : Nat} : m * m ≤ n * n ↔ m ≤ n :=
  ⟨fun h => Nat.le_of_not_lt fun h' => Nat.not_le_of_gt (mul_self_lt_mul_self h') h,
   mul_self_le_mul_self⟩

theorem mul_self_lt_mul_self_iff {m n : Nat} : m * m < n * n ↔ m < n := by
  simp only [← Nat.not_le, mul_self_le_mul_self_iff]

theorem le_mul_self : ∀ n : Nat, n ≤ n * n
  | 0 => Nat.le_refl _
  | n + 1 => by simp [Nat.mul_add]

theorem mul_self_inj {m n : Nat} : m * m = n * n ↔ m = n := by
  simp [Nat.le_antisymm_iff, mul_self_le_mul_self_iff]

@[simp] theorem lt_mul_self_iff : ∀ {n : Nat}, n < n * n ↔ 1 < n
  | 0 => by simp
  | n + 1 => Nat.lt_mul_iff_one_lt_left n.succ_pos

theorem add_sub_one_le_mul (ha : a ≠ 0) (hb : b ≠ 0) : a + b - 1 ≤ a * b := by
  cases a
  · cases ha rfl
  · rw [succ_add, Nat.add_one_sub_one, succ_mul]
    exact Nat.add_le_add_right (Nat.le_mul_of_pos_right _ <| Nat.pos_iff_ne_zero.2 hb) _

protected theorem add_le_mul {a : Nat} (ha : 2 ≤ a) : ∀ {b : Nat} (_ : 2 ≤ b), a + b ≤ a * b
  | 2, _ => by omega
  | b + 3, _ => by have := Nat.add_le_mul ha (Nat.le_add_left _ b); rw [mul_succ]; omega

/-! ### div/mod -/

theorem mod_two_eq_zero_or_one (n : Nat) : n % 2 = 0 ∨ n % 2 = 1 :=
  match n % 2, @Nat.mod_lt n 2 (by decide) with
  | 0, _ => .inl rfl
  | 1, _ => .inr rfl

@[simp] theorem mod_two_bne_zero : ((a % 2) != 0) = (a % 2 == 1) := by
  cases mod_two_eq_zero_or_one a <;> simp_all
@[simp] theorem mod_two_bne_one : ((a % 2) != 1) = (a % 2 == 0) := by
  cases mod_two_eq_zero_or_one a <;> simp_all

theorem le_of_mod_lt {a b : Nat} (h : a % b < a) : b ≤ a :=
  Nat.not_lt.1 fun hf => (ne_of_lt h).elim (Nat.mod_eq_of_lt hf)

theorem mul_mod_mul_right (z x y : Nat) : (x * z) % (y * z) = (x % y) * z := by
  rw [Nat.mul_comm x z, Nat.mul_comm y z, Nat.mul_comm (x % y) z]; apply mul_mod_mul_left

theorem sub_mul_mod {x k n : Nat} (h₁ : n*k ≤ x) : (x - n*k) % n = x % n := by
  match k with
  | 0 => rw [Nat.mul_zero, Nat.sub_zero]
  | succ k =>
    have h₂ : n * k ≤ x := Nat.le_trans (le_add_right _ n) h₁
    have h₄ : x - n * k ≥ n := by
      apply Nat.le_of_add_le_add_right (b := n * k)
      rw [Nat.sub_add_cancel h₂]
      simp [mul_succ, Nat.add_comm] at h₁; simp [h₁]
    rw [mul_succ, ← Nat.sub_sub, ← mod_eq_sub_mod h₄, sub_mul_mod h₂]

theorem mod_mod (a n : Nat) : (a % n) % n = a % n := by
  simp

theorem mul_mod (a b n : Nat) : a * b % n = (a % n) * (b % n) % n := by
  rw (occs := [1]) [← mod_add_div a n]
  rw (occs := [1]) [← mod_add_div b n]
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add,
    Nat.mul_assoc, Nat.mul_assoc, ← Nat.mul_add n, add_mul_mod_self_left,
    Nat.mul_comm _ (n * (b / n)), Nat.mul_assoc, add_mul_mod_self_left]

@[simp] theorem mod_add_mod (m n k : Nat) : (m % n + k) % n = (m + k) % n := by
  have := (add_mul_mod_self_left (m % n + k) n (m / n)).symm
  rwa [Nat.add_right_comm, mod_add_div] at this

@[simp] theorem mul_mod_mod (m n l : Nat) : (m * (n % l)) % l = (m * n) % l := by
  rw [mul_mod, mod_mod, ← mul_mod]

@[simp] theorem add_mod_mod (m n k : Nat) : (m + n % k) % k = (m + n) % k := by
  rw [Nat.add_comm, mod_add_mod, Nat.add_comm]

@[simp] theorem mod_mul_mod (m n l : Nat) : ((m % l) * n) % l = (m * n) % l := by
  rw [Nat.mul_comm, mul_mod_mod, Nat.mul_comm]

theorem add_mod (a b n : Nat) : (a + b) % n = ((a % n) + (b % n)) % n := by
  rw [add_mod_mod, mod_add_mod]

@[simp] theorem self_sub_mod (n k : Nat) [NeZero k] : (n - k) % n = n - k := by
  cases n with
  | zero => simp
  | succ n =>
    rw [mod_eq_of_lt]
    cases k with
    | zero => simp_all
    | succ k => omega

theorem mod_eq_sub (x w : Nat) : x % w = x - w * (x / w) := by
  conv => rhs; congr; rw [← mod_add_div x w]
  simp

theorem div_dvd_div {m n k : Nat} : k ∣ m → m ∣ n → m / k ∣ n / k := by
  refine (Nat.eq_zero_or_pos k).elim (by rintro rfl; simp) (fun hk => ?_)
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  rw [Nat.mul_comm, Nat.mul_div_cancel _ hk, Nat.mul_comm, ← Nat.mul_assoc, Nat.mul_div_cancel _ hk]
  exact Nat.dvd_mul_left a b

@[simp] theorem div_dvd_iff_dvd_mul {a b c : Nat} (h : b ∣ a) (hb : 0 < b) :
    a / b ∣ c ↔ a ∣ b * c := by
  rcases h with ⟨k, rfl⟩
  rw [Nat.mul_comm, Nat.mul_div_cancel _ hb, Nat.mul_comm, Nat.mul_dvd_mul_iff_left hb]

theorem div_eq_self {m n : Nat} : m / n = m ↔ m = 0 ∨ n = 1 := by
  refine ⟨fun h => (Nat.eq_zero_or_pos m).elim Or.inl ?_, fun h => by cases h <;> simp_all⟩
  refine fun hm => Or.inr ?_
  rcases Nat.lt_trichotomy n 1 with (hn|hn|hn)
  · obtain rfl : n = 0 := by rwa [lt_one_iff] at hn
    obtain rfl : 0 = m := by simpa [Nat.div_zero] using h
    simp at hm
  · exact hn
  · exact False.elim (absurd h (Nat.ne_of_lt (Nat.div_lt_self hm hn)))

@[simp] protected theorem div_eq_zero_iff : a / b = 0 ↔ b = 0 ∨ a < b where
  mp h := by
    rw [← mod_add_div a b, h, Nat.mul_zero, Nat.add_zero, Decidable.or_iff_not_imp_left]
    exact mod_lt _ ∘ Nat.pos_iff_ne_zero.2
  mpr := by
    obtain rfl | hb := Decidable.em (b = 0)
    · simp
    simp only [hb, false_or]
    rw [← Nat.mul_right_inj hb, ← Nat.add_left_cancel_iff, mod_add_div]
    simp +contextual [mod_eq_of_lt]

protected theorem div_ne_zero_iff : a / b ≠ 0 ↔ b ≠ 0 ∧ b ≤ a := by simp

@[simp] protected theorem div_pos_iff : 0 < a / b ↔ 0 < b ∧ b ≤ a := by
  simp [Nat.pos_iff_ne_zero]

theorem lt_mul_of_div_lt (h : a / c < b) (hc : 0 < c) : a < b * c :=
  Nat.lt_of_not_ge <| Nat.not_le_of_gt h ∘ (Nat.le_div_iff_mul_le hc).2

theorem mul_div_le_mul_div_assoc (a b c : Nat) : a * (b / c) ≤ a * b / c :=
  if hc0 : c = 0 then by simp [hc0] else
    (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hc0)).2
      (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _))

protected theorem eq_mul_of_div_eq_right {a b c : Nat} (H1 : b ∣ a) (H2 : a / b = c) :
    a = b * c := by
  rw [← H2, Nat.mul_div_cancel' H1]

protected theorem eq_mul_of_div_eq_left {a b c : Nat} (H1 : b ∣ a) (H2 : a / b = c) : a = c * b := by
  rw [Nat.mul_comm, Nat.eq_mul_of_div_eq_right H1 H2]

protected theorem mul_div_cancel_left' {a b : Nat} (Hd : a ∣ b) : a * (b / a) = b := by
  rw [Nat.mul_comm, Nat.div_mul_cancel Hd]

theorem lt_div_mul_add {a b : Nat} (hb : 0 < b) : a < a / b * b + b := by
  rw [← Nat.succ_mul, ← Nat.div_lt_iff_lt_mul hb]; exact Nat.lt_succ_self _

@[simp]
protected theorem div_left_inj {a b d : Nat} (hda : d ∣ a) (hdb : d ∣ b) :
    a / d = b / d ↔ a = b := by
  refine ⟨fun h ↦ ?_, congrArg fun b ↦ b / d⟩
  rw [← Nat.mul_div_cancel' hda, ← Nat.mul_div_cancel' hdb, h]

theorem div_le_iff_le_mul_add_pred (hb : 0 < b) : a / b ≤ c ↔ a ≤ b * c + (b - 1) := by
  rw [← Nat.lt_succ_iff, div_lt_iff_lt_mul hb, succ_mul, Nat.mul_comm]
  cases hb <;> exact Nat.lt_succ_iff

theorem one_le_div_iff {a b : Nat} (hb : 0 < b) : 1 ≤ a / b ↔ b ≤ a := by
  rw [le_div_iff_mul_le hb, Nat.one_mul]

theorem div_lt_one_iff (hb : 0 < b) : a / b < 1 ↔ a < b := by
  simp only [← Nat.not_le, one_le_div_iff hb]

protected theorem div_le_div_right {a b c : Nat} (h : a ≤ b) : a / c ≤ b / c :=
  (c.eq_zero_or_pos.elim fun hc ↦ by simp [hc]) fun hc ↦
    (le_div_iff_mul_le hc).2 <| Nat.le_trans (Nat.div_mul_le_self _ _) h

theorem lt_of_div_lt_div {a b c : Nat} (h : a / c < b / c) : a < b :=
  Nat.lt_of_not_le fun hab ↦ Nat.not_le_of_lt h <| Nat.div_le_div_right hab

theorem sub_mul_div (a b c : Nat) : (a - b * c) / b = a / b - c := by
  obtain h | h := Nat.le_total (b * c) a
  · rw [Nat.sub_mul_div_of_le _ _ _ h]
  · rw [Nat.sub_eq_zero_of_le h, Nat.zero_div]
    by_cases hn : b = 0
    · simp only [hn, Nat.div_zero, zero_le, Nat.sub_eq_zero_of_le]
    · have h2 : a / b ≤ (b * c) / b := Nat.div_le_div_right h
      rw [Nat.mul_div_cancel_left _ (zero_lt_of_ne_zero hn)] at h2
      rw [Nat.sub_eq_zero_of_le h2]

theorem mul_sub_div_of_dvd {b c : Nat} (hc : c ≠ 0) (hcb : c ∣ b) (a : Nat) : (c * a - b) / c = a - b / c := by
  obtain ⟨_, hx⟩ := hcb
  simp only [hx, ← Nat.mul_sub_left_distrib, Nat.mul_div_right, zero_lt_of_ne_zero hc]

theorem mul_add_mul_div_of_dvd (hb : b ≠ 0) (hd : d ≠ 0) (hba : b ∣ a) (hdc : d ∣ c) :
    (a * d + b * c) / (b * d) = a / b + c / d := by
  obtain ⟨n, hn⟩ := hba
  obtain ⟨_, hm⟩ := hdc
  rw [hn, hm, Nat.mul_assoc b n d, Nat.mul_comm n d, ← Nat.mul_assoc, ← Nat.mul_assoc,
    ← Nat.mul_add,
    Nat.mul_div_right _ (zero_lt_of_ne_zero hb),
    Nat.mul_div_right _ (zero_lt_of_ne_zero hd),
    Nat.mul_div_right _ (zero_lt_of_ne_zero <| Nat.mul_ne_zero hb hd)]

theorem mul_sub_mul_div_of_dvd (hb : b ≠ 0) (hd : d ≠ 0) (hba : b ∣ a) (hdc : d ∣ c) :
    (a * d - b * c) / (b * d)  = a / b - c / d := by
  obtain ⟨n, hn⟩ := hba
  obtain ⟨m, hm⟩ := hdc
  rw [hn, hm]
  rw [Nat.mul_assoc,Nat.mul_comm n d, ← Nat.mul_assoc,← Nat.mul_assoc, ← Nat.mul_sub_left_distrib,
    Nat.mul_div_right _ (zero_lt_of_ne_zero hb), Nat.mul_div_right _ (zero_lt_of_ne_zero hd),
    Nat.mul_div_right _ (zero_lt_of_ne_zero <| Nat.mul_ne_zero hb hd)]

protected theorem div_mul_right_comm {a b : Nat} (hba : b ∣ a) (c : Nat) : a / b * c = a * c / b := by
  rw [Nat.mul_comm, ← Nat.mul_div_assoc _ hba, Nat.mul_comm]

protected theorem mul_div_right_comm {a b : Nat} (hba : b ∣ a) (c : Nat) : a * c / b = a / b * c :=
  (Nat.div_mul_right_comm hba _).symm

protected theorem div_eq_iff_eq_mul_right {a b c : Nat} (H : 0 < b) (H' : b ∣ a) :
    a / b = c ↔ a = b * c :=
  ⟨Nat.eq_mul_of_div_eq_right H', Nat.div_eq_of_eq_mul_right H⟩

protected theorem div_eq_iff_eq_mul_left {a b c : Nat} (H : 0 < b) (H' : b ∣ a) :
    a / b = c ↔ a = c * b := by
  rw [Nat.mul_comm]; exact Nat.div_eq_iff_eq_mul_right H H'

theorem eq_div_iff_mul_eq_left (hc : c ≠ 0) (hcb : c ∣ b) : a = b / c ↔ b = a * c := by
  rw [eq_comm, Nat.div_eq_iff_eq_mul_left (zero_lt_of_ne_zero hc) hcb]

theorem div_mul_div_comm {a b c d : Nat} : b ∣ a → d ∣ c → (a / b) * (c / d) = (a * c) / (b * d) := by
  rintro ⟨x, rfl⟩ ⟨y, rfl⟩
  obtain rfl | hb := b.eq_zero_or_pos
  · simp
  obtain rfl | hd := d.eq_zero_or_pos
  · simp
  rw [Nat.mul_div_cancel_left _ hb, Nat.mul_div_cancel_left _ hd, Nat.mul_assoc b,
    Nat.mul_left_comm x, ← Nat.mul_assoc b, Nat.mul_div_cancel_left _ (Nat.mul_pos hb hd)]

protected theorem mul_div_mul_comm {a b c d : Nat} (hba : b ∣ a) (hdc : d ∣ c) : a * c / (b * d) = a / b * (c / d) :=
  (div_mul_div_comm hba hdc).symm

theorem eq_zero_of_le_div (hn : 2 ≤ n) (h : m ≤ m / n) : m = 0 :=
  eq_zero_of_mul_le hn <| by
    rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le (Nat.lt_of_lt_of_le (by decide) hn)).1 h

theorem div_mul_div_le_div (a b c : Nat) : a / c * b / a ≤ b / c := by
  obtain rfl | ha := Nat.eq_zero_or_pos a
  · simp
  · calc
      a / c * b / a ≤ b * a / c / a :=
        Nat.div_le_div_right (by rw [Nat.mul_comm]; exact mul_div_le_mul_div_assoc _ _ _)
      _ = b / c := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm b, Nat.mul_comm c,
          Nat.mul_div_mul_left _ _ ha]

theorem eq_zero_of_le_div_two (h : n ≤ n / 2) : n = 0 := eq_zero_of_le_div (Nat.le_refl _) h

theorem le_div_two_of_div_two_lt_sub (h : a / 2 < a - b) : b ≤ a / 2 := by
  omega

theorem div_two_le_of_sub_le_div_two (h : a - b ≤ a / 2) : a / 2 ≤ b := by
  omega

protected theorem div_le_div_of_mul_le_mul (hd : d ≠ 0) (hdc : d ∣ c) (h : a * d ≤ c * b) :
    a / b ≤ c / d :=
  Nat.div_le_of_le_mul <| by
    rwa [← Nat.mul_div_assoc _ hdc, Nat.le_div_iff_mul_le (Nat.pos_iff_ne_zero.2 hd), b.mul_comm]

theorem div_eq_sub_mod_div {m n : Nat} : m / n = (m - m % n) / n := by
  obtain rfl | hn := n.eq_zero_or_pos
  · rw [Nat.div_zero, Nat.div_zero]
  · have : m - m % n = n * (m / n) := by
      rw [Nat.sub_eq_iff_eq_add (Nat.mod_le _ _), Nat.add_comm, mod_add_div]
    rw [this, mul_div_right _ hn]

protected theorem eq_div_of_mul_eq_left (hc : c ≠ 0) (h : a * c = b) : a = b / c := by
  rw [← h, Nat.mul_div_cancel _ (Nat.pos_iff_ne_zero.2 hc)]

protected theorem eq_div_of_mul_eq_right (hc : c ≠ 0) (h : c * a = b) : a = b / c := by
  rw [← h, Nat.mul_div_cancel_left _ (Nat.pos_iff_ne_zero.2 hc)]

protected theorem mul_le_of_le_div (k x y : Nat) (h : x ≤ y / k) : x * k ≤ y := by
  if hk : k = 0 then
    rw [hk, Nat.mul_zero]; exact zero_le _
  else
    rwa [← le_div_iff_mul_le (Nat.pos_iff_ne_zero.2 hk)]

theorem div_le_iff_le_mul_of_dvd (hb : b ≠ 0) (hba : b ∣ a) : a / b ≤ c ↔ a ≤ c * b := by
  obtain ⟨_, hx⟩ := hba
  simp only [hx]
  rw [Nat.mul_div_right _ (zero_lt_of_ne_zero hb), Nat.mul_comm]
  exact ⟨mul_le_mul_right b, fun h ↦ Nat.le_of_mul_le_mul_right h (zero_lt_of_ne_zero hb)⟩

protected theorem div_lt_div_right (ha : a ≠ 0) : a ∣ b → a ∣ c → (b / a < c / a ↔ b < c) := by
  rintro ⟨d, rfl⟩ ⟨e, rfl⟩; simp [Nat.pos_iff_ne_zero.2 ha]

protected theorem div_lt_div_left (ha : a ≠ 0) (hba : b ∣ a) (hca : c ∣ a) :
    a / b < a / c ↔ c < b := by
  obtain ⟨d, hd⟩ := hba
  obtain ⟨e, he⟩ := hca
  rw [Nat.div_eq_of_eq_mul_right _ hd, Nat.div_eq_of_eq_mul_right _ he,
    Nat.lt_iff_lt_of_mul_eq_mul ha hd he] <;>
    rw [Nat.pos_iff_ne_zero] <;> rintro rfl <;> simp at * <;> contradiction

theorem lt_div_iff_mul_lt_of_dvd (hc : c ≠ 0) (hcb : c ∣ b) : a < b / c ↔ a * c < b := by
  simp [← Nat.div_lt_div_right _ _ hcb, hc, Nat.pos_iff_ne_zero, Nat.dvd_mul_left]

protected theorem div_mul_div_le (a b c d : Nat) :
    (a / b) * (c / d) ≤ (a * c) / (b * d) := by
  if hb : b = 0 then simp [hb] else
  if hd : d = 0 then simp [hd] else
  have hbd : b * d ≠ 0 := Nat.mul_ne_zero hb hd
  rw [le_div_iff_mul_le (Nat.pos_of_ne_zero hbd)]
  refine Nat.le_trans (m := ((a / b) * b) * ((c / d) * d)) ?_ ?_
  · apply Nat.le_of_eq; simp only [Nat.mul_assoc, Nat.mul_left_comm]
  · apply Nat.mul_le_mul <;> apply div_mul_le_self

/-! ### pow -/

theorem pow_succ' {m n : Nat} : m ^ n.succ = m * m ^ n := by
  rw [Nat.pow_succ, Nat.mul_comm]

theorem pow_add_one' {m n : Nat} : m ^ (n + 1) = m * m ^ n := by
  rw [Nat.pow_add_one, Nat.mul_comm]

@[simp] theorem pow_eq {m n : Nat} : m.pow n = m ^ n := rfl

theorem one_shiftLeft (n : Nat) : 1 <<< n = 2 ^ n := by rw [shiftLeft_eq, Nat.one_mul]

attribute [simp] Nat.pow_zero

protected theorem zero_pow {n : Nat} (H : 0 < n) : 0 ^ n = 0 := by
  match n with
  | 0 => contradiction
  | n+1 => rw [Nat.pow_succ, Nat.mul_zero]

@[simp] protected theorem one_pow (n : Nat) : 1 ^ n = 1 := by
  induction n with
  | zero => rfl
  | succ _ ih => rw [Nat.pow_succ, Nat.mul_one, ih]

protected theorem pow_two (a : Nat) : a ^ 2 = a * a := by rw [Nat.pow_succ, Nat.pow_one]

protected theorem pow_add (a m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | succ _ ih => rw [Nat.add_succ, Nat.pow_succ, Nat.pow_succ, ih, Nat.mul_assoc]

protected theorem pow_add' (a m n : Nat) : a ^ (m + n) = a ^ n * a ^ m := by
  rw [← Nat.pow_add, Nat.add_comm]

protected theorem pow_mul (a m n : Nat) : a ^ (m * n) = (a ^ m) ^ n := by
  induction n with
  | zero => rw [Nat.mul_zero, Nat.pow_zero, Nat.pow_zero]
  | succ _ ih => rw [Nat.mul_succ, Nat.pow_add, Nat.pow_succ, ih]

protected theorem pow_mul' (a m n : Nat) : a ^ (m * n) = (a ^ n) ^ m := by
  rw [← Nat.pow_mul, Nat.mul_comm]

protected theorem pow_right_comm (a m n : Nat) : (a ^ m) ^ n = (a ^ n) ^ m := by
  rw [← Nat.pow_mul, Nat.pow_mul']

protected theorem one_lt_two_pow (h : n ≠ 0) : 1 < 2 ^ n :=
  match n, h with
  | n+1, _ => by
    rw [Nat.pow_succ', ← Nat.one_mul 1]
    exact Nat.mul_lt_mul_of_lt_of_le' (by decide) (Nat.two_pow_pos n) (by decide)

@[simp] protected theorem one_lt_two_pow_iff : 1 < 2 ^ n ↔ n ≠ 0 :=
  ⟨(by intro h p; subst p; simp at h), Nat.one_lt_two_pow⟩

protected theorem one_le_two_pow : 1 ≤ 2 ^ n :=
  if h : n = 0 then
    by subst h; simp
  else
    Nat.le_of_lt (Nat.one_lt_two_pow h)

@[simp] theorem one_mod_two_pow_eq_one : 1 % 2 ^ n = 1 ↔ 0 < n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [mod_eq_of_lt (a := 1) (Nat.one_lt_two_pow (by omega))]
    simp

@[simp] theorem one_mod_two_pow (h : 0 < n) : 1 % 2 ^ n = 1 :=
  one_mod_two_pow_eq_one.mpr h

protected theorem pow_lt_pow_succ (h : 1 < a) : a ^ n < a ^ (n + 1) := by
  rw [← Nat.mul_one (a^n), Nat.pow_succ]
  exact Nat.mul_lt_mul_of_le_of_lt (Nat.le_refl _) h (Nat.pow_pos (Nat.lt_trans Nat.zero_lt_one h))

protected theorem pow_lt_pow_of_lt {a n m : Nat} (h : 1 < a) (w : n < m) : a ^ n < a ^ m := by
  have := Nat.exists_eq_add_of_lt w
  cases this with | intro k p
  rw [Nat.add_right_comm] at p
  subst p
  rw [Nat.pow_add, ← Nat.mul_one (a^n)]
  have t : 0 < a ^ k := Nat.pow_pos (Nat.lt_trans Nat.zero_lt_one h)
  exact Nat.mul_lt_mul_of_lt_of_le (Nat.pow_lt_pow_succ h) t t

protected theorem pow_le_pow_of_le {a n m : Nat} (h : 1 < a) (w : n ≤ m) : a ^ n ≤ a ^ m := by
  cases Nat.lt_or_eq_of_le w
  case inl lt =>
    exact Nat.le_of_lt (Nat.pow_lt_pow_of_lt h lt)
  case inr eq =>
    subst eq
    exact Nat.le_refl _

protected theorem pow_le_pow_iff_right {a n m : Nat} (h : 1 < a) :
    a ^ n ≤ a ^ m ↔ n ≤ m := by
  constructor
  · apply Decidable.by_contra
    intro w
    simp at w
    apply Nat.lt_irrefl (a ^ n)
    exact Nat.lt_of_le_of_lt w.1 (Nat.pow_lt_pow_of_lt h w.2)
  · intro w
    cases Nat.eq_or_lt_of_le w
    case inl eq => subst eq; apply Nat.le_refl
    case inr lt => exact Nat.le_of_lt (Nat.pow_lt_pow_of_lt h lt)

protected theorem pow_lt_pow_iff_right {a n m : Nat} (h : 1 < a) :
    a ^ n < a ^ m ↔ n < m := by
  constructor
  · apply Decidable.by_contra
    intro w
    simp at w
    apply Nat.lt_irrefl (a ^ n)
    exact Nat.lt_of_lt_of_le w.1 (Nat.pow_le_pow_of_le h w.2)
  · intro w
    exact Nat.pow_lt_pow_of_lt h w

@[simp]
protected theorem pow_pred_mul {x w : Nat} (h : 0 < w) :
    x ^ (w - 1) * x = x ^ w := by
  simp [← Nat.pow_succ, succ_eq_add_one, Nat.sub_add_cancel h]

protected theorem pow_pred_lt_pow {x w : Nat} (h₁ : 1 < x) (h₂ : 0 < w) :
    x ^ (w - 1) < x ^ w :=
  Nat.pow_lt_pow_of_lt h₁ (by omega)

protected theorem two_pow_pred_lt_two_pow {w : Nat} (h : 0 < w) :
    2 ^ (w - 1) < 2 ^ w :=
  Nat.pow_pred_lt_pow (by omega) h

@[simp]
protected theorem two_pow_pred_add_two_pow_pred (h : 0 < w) :
    2 ^ (w - 1) + 2 ^ (w - 1) = 2 ^ w := by
  rw [← Nat.pow_pred_mul h]
  omega

@[simp]
protected theorem two_pow_sub_two_pow_pred (h : 0 < w) :
    2 ^ w - 2 ^ (w - 1) = 2 ^ (w - 1) := by
  simp [← Nat.two_pow_pred_add_two_pow_pred h]

@[simp]
protected theorem two_pow_pred_mod_two_pow (h : 0 < w) :
    2 ^ (w - 1) % 2 ^ w = 2 ^ (w - 1) := by
  rw [mod_eq_of_lt]
  apply Nat.pow_pred_lt_pow (by omega) h

protected theorem pow_lt_pow_iff_pow_mul_le_pow {a n m : Nat} (h : 1 < a) :
    a ^ n < a ^ m ↔ a ^ n * a ≤ a ^ m := by
  rw [←Nat.pow_add_one, Nat.pow_le_pow_iff_right (by omega), Nat.pow_lt_pow_iff_right (by omega)]
  omega

protected theorem lt_pow_self {n a : Nat} (h : 1 < a) : n < a ^ n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ _ ih => exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right ih 1) (Nat.pow_lt_pow_succ h)

protected theorem lt_two_pow_self : n < 2 ^ n :=
  Nat.lt_pow_self Nat.one_lt_two

@[simp]
protected theorem mod_two_pow_self : n % 2 ^ n = n :=
  Nat.mod_eq_of_lt Nat.lt_two_pow_self

@[simp]
theorem two_pow_pred_mul_two (h : 0 < w) :
    2 ^ (w - 1) * 2 = 2 ^ w := by
  simp [← Nat.pow_succ, Nat.sub_add_cancel h]

theorem le_pow {a b : Nat} (h : 0 < b) : a ≤ a ^ b := by
  refine (eq_zero_or_pos a).elim (by rintro rfl; simp) (fun ha => ?_)
  rw [(show b = b - 1 + 1 by omega), Nat.pow_succ]
  exact Nat.le_mul_of_pos_left _ (Nat.pow_pos ha)

protected theorem pow_lt_pow_right (ha : 1 < a) (h : m < n) : a ^ m < a ^ n :=
  (Nat.pow_lt_pow_iff_right ha).2 h

protected theorem pow_le_pow_iff_left {a b n : Nat} (hn : n ≠ 0) : a ^ n ≤ b ^ n ↔ a ≤ b where
  mp := by simpa only [← Nat.not_le, Decidable.not_imp_not] using (Nat.pow_lt_pow_left · hn)
  mpr h := Nat.pow_le_pow_left h _

protected theorem pow_lt_pow_iff_left {a b n : Nat} (hn : n ≠ 0) : a ^ n < b ^ n ↔ a < b := by
  simp only [← Nat.not_le, Nat.pow_le_pow_iff_left hn]

@[simp high] protected theorem pow_eq_zero {a : Nat} : ∀ {n : Nat}, a ^ n = 0 ↔ a = 0 ∧ n ≠ 0
  | 0 => by simp
  | n + 1 => by rw [Nat.pow_succ, mul_eq_zero, Nat.pow_eq_zero]; omega

theorem le_self_pow (hn : n ≠ 0) : ∀ a : Nat, a ≤ a ^ n
  | 0 => zero_le _
  | a + 1 => by simpa using Nat.pow_le_pow_right a.succ_pos (Nat.one_le_iff_ne_zero.2 hn)

theorem one_le_pow (n m : Nat) (h : 0 < m) : 1 ≤ m ^ n := by simpa using Nat.pow_le_pow_left h n

theorem one_lt_pow (hn : n ≠ 0) (ha : 1 < a) : 1 < a ^ n := by simpa using Nat.pow_lt_pow_left ha hn

theorem two_pow_succ (n : Nat) : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by simp [Nat.pow_succ, Nat.mul_two]

theorem one_lt_pow' (n m : Nat) : 1 < (m + 2) ^ (n + 1) :=
  one_lt_pow n.succ_ne_zero (Nat.lt_of_sub_eq_succ rfl)

@[simp] theorem one_lt_pow_iff {n : Nat} (hn : n ≠ 0) : ∀ {a}, 1 < a ^ n ↔ 1 < a
 | 0 => by simp [Nat.zero_pow (Nat.pos_of_ne_zero hn)]
 | 1 => by simp
 | a + 2 => by simp [one_lt_pow hn]

theorem one_lt_two_pow' (n : Nat) : 1 < 2 ^ (n + 1) := one_lt_pow n.succ_ne_zero (by decide)

theorem mul_lt_mul_pow_succ (ha : 0 < a) (hb : 1 < b) : n * b < a * b ^ (n + 1) := by
  rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_lt_mul_right (Nat.lt_trans Nat.zero_lt_one hb)]
  exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ ha)
    ((Nat.mul_lt_mul_left ha).2 <| Nat.lt_pow_self hb)


theorem pow_two_sub_pow_two (a b : Nat) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by
  simpa [Nat.pow_succ] using Nat.mul_self_sub_mul_self_eq a b

protected theorem pow_pos_iff : 0 < a ^ n ↔ 0 < a ∨ n = 0 := by
  simp [Nat.pos_iff_ne_zero, Decidable.imp_iff_not_or]

theorem pow_self_pos : 0 < n ^ n := by simp [Nat.pow_pos_iff, n.eq_zero_or_pos.symm]

theorem pow_self_mul_pow_self_le : m ^ m * n ^ n ≤ (m + n) ^ (m + n) := by
  rw [Nat.pow_add]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left (le_add_right ..) _)
    (Nat.pow_le_pow_left (le_add_left ..) _)

protected theorem pow_right_inj (ha : 1 < a) : a ^ m = a ^ n ↔ m = n := by
  simp [Nat.le_antisymm_iff, Nat.pow_le_pow_iff_right ha]

@[simp] protected theorem pow_eq_one : a ^ n = 1 ↔ a = 1 ∨ n = 0 := by
  obtain rfl | hn := Decidable.em (n = 0)
  · simp
  · simpa [hn] using Nat.pow_left_inj hn (b := 1)

/-- For `a > 1`, `a ^ b = a` iff `b = 1`. -/
theorem pow_eq_self_iff {a b : Nat} (ha : 1 < a) : a ^ b = a ↔ b = 1 := by
  rw [← Nat.pow_right_inj (m := b) ha, Nat.pow_one]

@[simp] protected theorem pow_le_one_iff (hn : n ≠ 0) : a ^ n ≤ 1 ↔ a ≤ 1 := by
  rw [← Nat.not_lt, one_lt_pow_iff hn, Nat.not_lt]

/-! ### log2 -/

@[simp]
theorem log2_zero : Nat.log2 0 = 0 := by
  simp [Nat.log2_def]

theorem le_log2 (h : n ≠ 0) : k ≤ n.log2 ↔ 2 ^ k ≤ n := by
  match k with
  | 0 => simp [show 1 ≤ n from Nat.pos_of_ne_zero h]
  | k+1 =>
    rw [log2_def]; split
    · have n0 : 0 < n / 2 := (Nat.le_div_iff_mul_le (by decide)).2 ‹_›
      simp only [Nat.add_le_add_iff_right, le_log2 (Nat.ne_of_gt n0),
        Nat.pow_succ]
      exact Nat.le_div_iff_mul_le (by decide)
    · simp only [le_zero_eq, succ_ne_zero, false_iff]
      refine mt (Nat.le_trans ?_) ‹_›
      exact Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_add_left 1 k)

theorem log2_lt (h : n ≠ 0) : n.log2 < k ↔ n < 2 ^ k := by
  rw [← Nat.not_le, ← Nat.not_le, le_log2 h]

theorem log2_eq_iff (h : n ≠ 0) : n.log2 = k ↔ 2 ^ k ≤ n ∧ n < 2 ^ (k + 1) := by
  constructor
  · intro w
    exact ⟨(le_log2 h).mp (Nat.le_of_eq w.symm), (log2_lt h).mp (by subst w; apply lt_succ_self)⟩
  · intro w
    apply Nat.le_antisymm
    · apply Nat.le_of_lt_add_one
      exact (log2_lt h).mpr w.2
    · exact (le_log2 h).mpr w.1

theorem log2_two_mul (h : n ≠ 0) : (2 * n).log2 = n.log2 + 1 := by
  obtain ⟨h₁, h₂⟩ := (log2_eq_iff h).mp rfl
  rw [log2_eq_iff (Nat.mul_ne_zero (by decide) h)]
  constructor
  · rw [Nat.pow_succ, Nat.mul_comm]
    exact mul_le_mul_left 2 h₁
  · rw [Nat.pow_succ, Nat.mul_comm]
    rwa [Nat.mul_lt_mul_right (by decide)]

@[simp]
theorem log2_two_pow : (2 ^ n).log2 = n := by
  apply Nat.eq_of_le_of_lt_succ <;> simp [le_log2, log2_lt, NeZero.ne, Nat.pow_lt_pow_iff_right]

theorem log2_self_le (h : n ≠ 0) : 2 ^ n.log2 ≤ n := (le_log2 h).1 (Nat.le_refl _)

theorem lt_log2_self : n < 2 ^ (n.log2 + 1) :=
  match n with
  | 0 => by simp
  | n+1 => (log2_lt n.succ_ne_zero).1 (Nat.le_refl _)

/-! ### mod, dvd -/

theorem pow_dvd_pow_iff_pow_le_pow {k l : Nat} :
    ∀ {x : Nat}, 0 < x → (x ^ k ∣ x ^ l ↔ x ^ k ≤ x ^ l)
  | x + 1, w => by
    constructor
    · intro a
      exact le_of_dvd (Nat.pow_pos (succ_pos x)) a
    · intro a
      cases x
      case zero => simp
      case succ x =>
        have le :=
          (Nat.pow_le_pow_iff_right (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _)))).mp a
        refine ⟨(x + 2) ^ (l - k), ?_⟩
        rw [← Nat.pow_add, Nat.add_comm k, Nat.sub_add_cancel le]

/-- If `1 < x`, then `x^k` divides `x^l` if and only if `k` is at most `l`. -/
theorem pow_dvd_pow_iff_le_right {x k l : Nat} (w : 1 < x) : x ^ k ∣ x ^ l ↔ k ≤ l := by
  rw [pow_dvd_pow_iff_pow_le_pow (lt_of_succ_lt w), Nat.pow_le_pow_iff_right w]

theorem pow_dvd_pow_iff_le_right' {b k l : Nat} : (b + 2) ^ k ∣ (b + 2) ^ l ↔ k ≤ l :=
  pow_dvd_pow_iff_le_right (Nat.lt_of_sub_eq_succ rfl)

protected theorem pow_dvd_pow {m n : Nat} (a : Nat) (h : m ≤ n) : a ^ m ∣ a ^ n := by
  cases Nat.exists_eq_add_of_le h
  case intro k p =>
    subst p
    rw [Nat.pow_add]
    apply Nat.dvd_mul_right

protected theorem pow_sub_mul_pow (a : Nat) {m n : Nat} (h : m ≤ n) :
    a ^ (n - m) * a ^ m = a ^ n := by
  rw [← Nat.pow_add, Nat.sub_add_cancel h]

theorem pow_dvd_of_le_of_pow_dvd {p m n k : Nat} (hmn : m ≤ n) (hdiv : p ^ n ∣ k) : p ^ m ∣ k :=
  Nat.dvd_trans (Nat.pow_dvd_pow _ hmn) hdiv

theorem dvd_of_pow_dvd {p k m : Nat} (hk : 1 ≤ k) (hpk : p ^ k ∣ m) : p ∣ m := by
  rw [← Nat.pow_one p]; exact pow_dvd_of_le_of_pow_dvd hk hpk

protected theorem pow_div {x m n : Nat} (h : n ≤ m) (hx : 0 < x) : x ^ m / x ^ n = x ^ (m - n) := by
  rw [Nat.div_eq_iff_eq_mul_left (Nat.pow_pos hx) (Nat.pow_dvd_pow _ h), Nat.pow_sub_mul_pow _ h]

protected theorem div_pow {a b c : Nat} (h : a ∣ b) : (b / a) ^ c = b ^ c / a ^ c := by
  refine (Nat.eq_zero_or_pos c).elim (by rintro rfl; simp) (fun hc => ?_)
  refine (Nat.eq_zero_or_pos a).elim (by rintro rfl; simp [hc]) (fun ha => ?_)
  rw [eq_comm, Nat.div_eq_iff_eq_mul_left (Nat.pow_pos ha)
    ((Nat.pow_dvd_pow_iff (Nat.pos_iff_ne_zero.1 hc)).2 h)]
  clear hc
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Nat.pow_succ (b / a), Nat.pow_succ a, Nat.mul_comm _ a, Nat.mul_assoc, ← Nat.mul_assoc _ a,
      Nat.div_mul_cancel h, Nat.mul_comm b, ← Nat.mul_assoc, ← ih, Nat.pow_succ]

@[simp] theorem mod_two_not_eq_one : ¬n % 2 = 1 ↔ n % 2 = 0 := by
  cases mod_two_eq_zero_or_one n <;> simp [*]

@[simp] theorem mod_two_not_eq_zero : ¬n % 2 = 0 ↔ n % 2 = 1 := by
  cases mod_two_eq_zero_or_one n <;> simp [*]

theorem mod_two_ne_one : n % 2 ≠ 1 ↔ n % 2 = 0 := mod_two_not_eq_one
theorem mod_two_ne_zero : n % 2 ≠ 0 ↔ n % 2 = 1 := mod_two_not_eq_zero

/-- Variant of `Nat.lt_div_iff_mul_lt` that assumes `d ∣ n`. -/
protected theorem lt_div_iff_mul_lt' (hdn : d ∣ n) (a : Nat) : a < n / d ↔ d * a < n := by
  obtain rfl | hd := d.eq_zero_or_pos
  · simp [Nat.zero_dvd.1 hdn]
  · rw [← Nat.mul_lt_mul_left hd, ← Nat.eq_mul_of_div_eq_right hdn rfl]

theorem mul_div_eq_iff_dvd {n d : Nat} : d * (n / d) = n ↔ d ∣ n :=
  calc
    d * (n / d) = n ↔ d * (n / d) = d * (n / d) + (n % d) := by rw [div_add_mod]
    _ ↔ d ∣ n := by rw [eq_comm, Nat.add_eq_left, dvd_iff_mod_eq_zero]

theorem mul_div_lt_iff_not_dvd {n d : Nat} : d * (n / d) < n ↔ ¬ d ∣ n := by
  simp [Nat.lt_iff_le_and_ne, mul_div_eq_iff_dvd, mul_div_le]

theorem div_eq_iff_eq_of_dvd_dvd (hn : n ≠ 0) (ha : a ∣ n) (hb : b ∣ n) : n / a = n / b ↔ a = b := by
  constructor <;> intro h
  · rw [← Nat.mul_right_inj hn]
    apply Nat.eq_mul_of_div_eq_left (Nat.dvd_trans hb (Nat.dvd_mul_right _ _))
    rw [eq_comm, Nat.mul_comm, Nat.mul_div_assoc _ hb]
    exact Nat.eq_mul_of_div_eq_right ha h
  · rw [h]

theorem le_iff_ne_zero_of_dvd (ha : a ≠ 0) (hab : a ∣ b) : a ≤ b ↔ b ≠ 0 where
  mp := by rw [← Nat.pos_iff_ne_zero] at ha ⊢; exact Nat.lt_of_lt_of_le ha
  mpr hb := Nat.le_of_dvd (Nat.pos_iff_ne_zero.2 hb) hab

theorem div_ne_zero_iff_of_dvd (hba : b ∣ a) : a / b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := by
  obtain rfl | hb := Decidable.em (b = 0) <;>
    simp [Nat.le_iff_ne_zero_of_dvd, *]

theorem pow_mod (a b n : Nat) : a ^ b % n = (a % n) ^ b % n := by
  induction b with
  | zero => rfl
  | succ b ih => simp [Nat.pow_succ, Nat.mul_mod, ih]

theorem lt_of_pow_dvd_right (hb : b ≠ 0) (ha : 2 ≤ a) (h : a ^ n ∣ b) : n < b := by
  rw [← Nat.pow_lt_pow_iff_right (succ_le_iff.1 ha)]
  exact Nat.lt_of_le_of_lt (le_of_dvd (Nat.pos_iff_ne_zero.2 hb) h) (Nat.lt_pow_self ha)

theorem div_dvd_of_dvd {n m : Nat} (h : n ∣ m) : m / n ∣ m := ⟨n, (Nat.div_mul_cancel h).symm⟩

protected theorem div_div_self (h : n ∣ m) (hm : m ≠ 0) : m / (m / n) = n := by
  rcases h with ⟨_, rfl⟩
  rw [Nat.mul_ne_zero_iff] at hm
  rw [mul_div_right _ (Nat.pos_of_ne_zero hm.1), mul_div_left _ (Nat.pos_of_ne_zero hm.2)]

theorem not_dvd_of_pos_of_lt (h1 : 0 < n) (h2 : n < m) : ¬m ∣ n := by
  rintro ⟨k, rfl⟩
  rcases Nat.eq_zero_or_pos k with (rfl | hk)
  · exact Nat.lt_irrefl 0 h1
  · exact Nat.not_lt.2 (Nat.le_mul_of_pos_right _ hk) h2

theorem eq_of_dvd_of_lt_two_mul (ha : a ≠ 0) (hdvd : b ∣ a) (hlt : a < 2 * b) : a = b := by
  obtain ⟨_ | _ | c, rfl⟩ := hdvd
  · simp at ha
  · exact Nat.mul_one _
  · rw [Nat.mul_comm] at hlt
    cases Nat.not_le_of_lt hlt (Nat.mul_le_mul_right _ (by omega))

theorem mod_eq_iff_lt (hn : n ≠ 0) : m % n = m ↔ m < n :=
  ⟨fun h ↦ by rw [← h]; exact mod_lt _ <| Nat.pos_iff_ne_zero.2 hn, mod_eq_of_lt⟩

@[simp]
theorem mod_succ_eq_iff_lt {m n : Nat} : m % n.succ = m ↔ m < n.succ :=
  mod_eq_iff_lt (succ_ne_zero _)

@[simp] theorem mod_succ (n : Nat) : n % n.succ = n := mod_eq_of_lt n.lt_succ_self

theorem mod_add_div' (a b : Nat) : a % b + a / b * b = a := by rw [Nat.mul_comm]; exact mod_add_div _ _

theorem div_add_mod' (a b : Nat) : a / b * b + a % b = a := by rw [Nat.mul_comm]; exact div_add_mod _ _

/-- See also `Nat.divModEquiv` for a similar statement as an `Equiv`. -/
protected theorem div_mod_unique (h : 0 < b) :
    a / b = d ∧ a % b = c ↔ c + b * d = a ∧ c < b :=
  ⟨fun ⟨e₁, e₂⟩ ↦ e₁ ▸ e₂ ▸ ⟨mod_add_div _ _, mod_lt _ h⟩, fun ⟨h₁, h₂⟩ ↦ h₁ ▸ by
    rw [add_mul_div_left _ _ h, add_mul_mod_self_left]; simp [div_eq_of_lt, mod_eq_of_lt, h₂]⟩

/-- If `m` and `n` are equal mod `k`, `m - n` is zero mod `k`. -/
theorem sub_mod_eq_zero_of_mod_eq (h : m % k = n % k) : (m - n) % k = 0 := by
  rw [← Nat.mod_add_div m k, ← Nat.mod_add_div n k, ← h, ← Nat.sub_sub,
    Nat.add_sub_cancel_left, ← k.mul_sub, Nat.mul_mod_right]

@[simp] theorem one_mod (n : Nat) : 1 % (n + 2) = 1 :=
  Nat.mod_eq_of_lt (Nat.add_lt_add_right n.succ_pos 1)

theorem one_mod_eq_one : ∀ {n : Nat}, 1 % n = 1 ↔ n ≠ 1
  | 0 | 1 | n + 2 => by simp; try omega

theorem dvd_sub_mod (k : Nat) : n ∣ k - k % n :=
  ⟨k / n, Nat.sub_eq_of_eq_add (Nat.div_add_mod k n).symm⟩

theorem add_mod_eq_ite {m n : Nat} :
    (m + n) % k = if k ≤ m % k + n % k then m % k + n % k - k else m % k + n % k := by
  cases k with
  | zero => simp
  | succ k =>
    rw [Nat.add_mod]
    by_cases h : k + 1 ≤ m % (k + 1) + n % (k + 1)
    · rw [if_pos h, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt]
      exact (Nat.sub_lt_iff_lt_add h).mpr (Nat.add_lt_add (m.mod_lt (zero_lt_succ _))
        (n.mod_lt (zero_lt_succ _)))
    · rw [if_neg h]
      exact Nat.mod_eq_of_lt (Nat.lt_of_not_ge h)

-- TODO: Replace `Nat.dvd_add_iff_left`
protected theorem dvd_add_left {a b c : Nat} (h : a ∣ c) : a ∣ b + c ↔ a ∣ b := (Nat.dvd_add_iff_left h).symm

protected theorem dvd_add_right {a b c : Nat} (h : a ∣ b) : a ∣ b + c ↔ a ∣ c := (Nat.dvd_add_iff_right h).symm

theorem add_mod_eq_add_mod_right (c : Nat) (H : a % d = b % d) : (a + c) % d = (b + c) % d := by
  rw [← mod_add_mod, ← mod_add_mod b, H]

theorem add_mod_eq_add_mod_left (c : Nat) (H : a % d = b % d) : (c + a) % d = (c + b) % d := by
  rw [Nat.add_comm, add_mod_eq_add_mod_right _ H, Nat.add_comm]

theorem mul_dvd_of_dvd_div {a b c : Nat} (hcb : c ∣ b) (h : a ∣ b / c) : c * a ∣ b :=
  have ⟨d, hd⟩ := h
  ⟨d, by simpa [Nat.mul_comm, Nat.mul_left_comm] using Nat.eq_mul_of_div_eq_left hcb hd⟩

theorem eq_of_dvd_of_div_eq_one (hab : a ∣ b) (h : b / a = 1) : a = b := by
  rw [← Nat.div_mul_cancel hab, h, Nat.one_mul]

theorem eq_zero_of_dvd_of_div_eq_zero (hab : a ∣ b) (h : b / a = 0) : b = 0 := by
  rw [← Nat.div_mul_cancel hab, h, Nat.zero_mul]

theorem lt_mul_div_succ (a : Nat) (hb : 0 < b) : a < b * (a / b + 1) := by
  rw [Nat.mul_comm, ← Nat.div_lt_iff_lt_mul hb]
  exact lt_succ_self _

theorem mul_add_div {m : Nat} (m_pos : m > 0) (x y : Nat) : (m * x + y) / m = x + y / m := by
  match x with
  | 0 => simp
  | x + 1 =>
    rw [Nat.mul_succ, Nat.add_assoc _ m, mul_add_div m_pos x (m+y), div_eq]
    simp +arith [m_pos]

theorem mul_add_mod (m x y : Nat) : (m * x + y) % m = y % m := by
  match x with
  | 0 => simp
  | x + 1 =>
    simp [Nat.mul_succ, Nat.add_assoc _ m, mul_add_mod _ x]

-- TODO: make naming and statements consistent across all variations of `mod`, `gcd` etc. across
-- `Nat` and `Int`.
theorem mul_add_mod' (a b c : Nat) : (a * b + c) % b = c % b := by rw [Nat.mul_comm, Nat.mul_add_mod]

theorem mul_add_mod_of_lt {a b c : Nat} (h : c < b) : (a * b + c) % b = c := by
  rw [Nat.mul_add_mod', Nat.mod_eq_of_lt h]

@[simp] theorem mod_div_self (m n : Nat) : m % n / n = 0 := by
  cases n
  · exact (m % 0).div_zero
  case succ n => exact Nat.div_eq_of_lt (m.mod_lt n.succ_pos)

theorem mod_eq_iff {a b c : Nat} :
    a % b = c ↔ (b = 0 ∧ a = c) ∨ (c < b ∧ Exists fun k => a = b * k + c) :=
  ⟨fun h =>
    if w : b = 0 then
      .inl ⟨w, by simpa [w] using h⟩
    else
      .inr ⟨by subst h; exact Nat.mod_lt a (zero_lt_of_ne_zero w),
        a / b, by subst h; exact (div_add_mod a b).symm⟩,
   by
     rintro (⟨rfl, rfl⟩ | ⟨w, h, rfl⟩)
     · simp_all
     · rw [mul_add_mod, mod_eq_of_lt w]⟩

theorem mod_eq_sub_iff {a b c : Nat} (h₁ : 0 < c) (h : c ≤ b) : a % b = b - c ↔ b ∣ a + c := by
  rw [Nat.mod_eq_iff]
  refine ⟨?_, ?_⟩
  · rintro (⟨rfl, rfl⟩|⟨hlt, ⟨k, hk⟩⟩)
    · simp; omega
    · refine ⟨k + 1, ?_⟩
      rw [← Nat.add_sub_assoc h] at hk
      rw [Nat.mul_succ, eq_comm]
      apply Nat.eq_add_of_sub_eq (by omega) hk.symm
  · rintro ⟨k, hk⟩
    obtain (rfl|hb) := Nat.eq_zero_or_pos b
    · obtain rfl : c = 0 := by omega
      refine Or.inl ⟨rfl, by simpa using hk⟩
    · have : k ≠ 0 := by rintro rfl; omega
      refine Or.inr ⟨by omega, ⟨k - 1, ?_⟩⟩
      rw [← Nat.add_sub_assoc h, eq_comm]
      apply Nat.sub_eq_of_eq_add
      rw [mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ (by omega)), hk]

theorem succ_mod_succ_eq_zero_iff {a b : Nat} :
    (a + 1) % (b + 1) = 0 ↔ a % (b + 1) = b := by
  symm
  rw [mod_eq_iff, mod_eq_iff]
  simp only [add_one_ne_zero, false_and, Nat.lt_add_one, true_and, false_or, and_self, zero_lt_succ,
    Nat.add_zero]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨k + 1, ?_⟩
    simp [Nat.add_mul, Nat.mul_add, Nat.add_assoc]
  · rintro ⟨k, h⟩
    cases k with
    | zero => simp at h
    | succ k =>
      refine ⟨k, ?_⟩
      simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one, ← Nat.add_assoc,
        Nat.add_right_cancel_iff] at h
      subst h
      simp [Nat.add_mul]


theorem dvd_iff_div_mul_eq (n d : Nat) : d ∣ n ↔ n / d * d = n :=
  ⟨fun h => Nat.div_mul_cancel h, fun h => by rw [← h]; exact Nat.dvd_mul_left _ _⟩

theorem dvd_iff_le_div_mul (n d : Nat) : d ∣ n ↔ n ≤ n / d * d :=
  ((dvd_iff_div_mul_eq _ _).trans Nat.le_antisymm_iff).trans (and_iff_right (div_mul_le_self n d))

theorem dvd_iff_dvd_dvd (n d : Nat) : d ∣ n ↔ ∀ k : Nat, k ∣ d → k ∣ n :=
  ⟨fun h _ hkd => Nat.dvd_trans hkd h, fun h => h _ (Nat.dvd_refl _)⟩

theorem dvd_div_of_mul_dvd {a b c : Nat} (h : a * b ∣ c) : b ∣ c / a :=
  if ha : a = 0 then by simp [ha]
  else
    have ha : 0 < a := Nat.pos_of_ne_zero ha
    have h1 : ∃ d, c = a * b * d := h
    let ⟨d, hd⟩ := h1
    have h2 : c / a = b * d := Nat.div_eq_of_eq_mul_right ha (by simpa [Nat.mul_assoc] using hd)
    show ∃ d, c / a = b * d from ⟨d, h2⟩

@[simp] theorem dvd_div_iff_mul_dvd {a b c : Nat} (hbc : c ∣ b) : a ∣ b / c ↔ c * a ∣ b :=
  ⟨fun h => mul_dvd_of_dvd_div hbc h, fun h => dvd_div_of_mul_dvd h⟩

theorem dvd_mul_of_div_dvd {a b c : Nat} (h : b ∣ a) (hdiv : a / b ∣ c) : a ∣ b * c := by
  obtain ⟨e, rfl⟩ := hdiv
  rw [← Nat.mul_assoc, Nat.mul_comm _ (a / b), Nat.div_mul_cancel h]
  exact Nat.dvd_mul_right a e

@[simp] theorem div_div_div_eq_div {a b c : Nat} (dvd : b ∣ a) (dvd2 : a ∣ c) : c / (a / b) / b = c / a :=
  match a, b, c with
  | 0, _, _ => by simp
  | a + 1, 0, _ => by simp at dvd
  | a + 1, c + 1, _ => by
    have a_split : a + 1 ≠ 0 := succ_ne_zero a
    have c_split : c + 1 ≠ 0 := succ_ne_zero c
    rcases dvd2 with ⟨k, rfl⟩
    rcases dvd with ⟨k2, pr⟩
    have k2_nonzero : k2 ≠ 0 := fun k2_zero => by simp [k2_zero] at pr
    rw [Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero a_split), pr,
      Nat.mul_div_cancel_left k2 (Nat.pos_of_ne_zero c_split), Nat.mul_comm ((c + 1) * k2) k, ←
      Nat.mul_assoc k (c + 1) k2, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero k2_nonzero),
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero c_split)]

/-- If a small natural number is divisible by a larger natural number,
the small number is zero. -/
theorem eq_zero_of_dvd_of_lt (w : a ∣ b) (h : b < a) : b = 0 :=
  Nat.eq_zero_of_dvd_of_div_eq_zero w (by simp [h])

theorem le_of_lt_add_of_dvd {a b : Nat} (h : a < b + n) : n ∣ a → n ∣ b → a ≤ b := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  rw [← mul_succ] at h
  exact Nat.mul_le_mul_left _ (Nat.lt_succ_iff.1 <| Nat.lt_of_mul_lt_mul_left h)

/-- `m` is not divisible by `n` if it is between `n * k` and `n * (k + 1)` for some `k`. -/
theorem not_dvd_of_lt_of_lt_mul_succ (h1 : n * k < m) (h2 : m < n * (k + 1)) : ¬n ∣ m := by
  rintro ⟨d, rfl⟩
  have := Nat.lt_of_mul_lt_mul_left h1
  have := Nat.lt_of_mul_lt_mul_left h2
  omega

/-- `n` is not divisible by `a` iff it is between `a * k` and `a * (k + 1)` for some `k`. -/
theorem not_dvd_iff_lt_mul_succ (n : Nat) {a : Nat} (ha : 0 < a) :
    ¬a ∣ n ↔ (∃ k : Nat, a * k < n ∧ n < a * (k + 1)) := by
  refine Iff.symm
    ⟨fun ⟨k, hk1, hk2⟩ => not_dvd_of_lt_of_lt_mul_succ hk1 hk2, fun han =>
      ⟨n / a, ⟨Nat.lt_of_le_of_ne (mul_div_le n a) ?_, lt_mul_div_succ _ ha⟩⟩⟩
  exact mt (⟨n / a, Eq.symm ·⟩) han

theorem div_lt_div_of_lt_of_dvd {a b d : Nat} (hdb : d ∣ b) (h : a < b) : a / d < b / d := by
  rw [Nat.lt_div_iff_mul_lt' hdb]
  exact Nat.lt_of_le_of_lt (mul_div_le a d) h

/-! ### shiftLeft and shiftRight -/

@[simp, grind =] theorem shiftLeft_zero : n <<< 0 = n := rfl

/-- Shift left on successor with multiple moved inside. -/
theorem shiftLeft_succ_inside (m n : Nat) : m <<< (n+1) = (2*m) <<< n := rfl

/-- Shift left on successor with multiple moved to outside. -/
theorem shiftLeft_succ : ∀(m n), m <<< (n + 1) = 2 * (m <<< n)
| _, 0 => rfl
| _, k + 1 => by
  rw [shiftLeft_succ_inside _ (k+1)]
  rw [shiftLeft_succ _ k, shiftLeft_succ_inside]

/-- Shift right on successor with division moved inside. -/
theorem shiftRight_succ_inside : ∀m n, m >>> (n+1) = (m/2) >>> n
| _, 0 => rfl
| _, k + 1 => by
  rw [shiftRight_succ _ (k+1)]
  rw [shiftRight_succ_inside _ k, shiftRight_succ]

@[simp, grind =] theorem zero_shiftLeft : ∀ n, 0 <<< n = 0
  | 0 => by simp
  | n + 1 => by simp [zero_shiftLeft n, shiftLeft_succ]

@[simp, grind =] theorem zero_shiftRight : ∀ n, 0 >>> n = 0
  | 0 => by simp
  | n + 1 => by simp [zero_shiftRight n, shiftRight_succ]

@[grind _=_]
theorem shiftLeft_add (m n : Nat) : ∀ k, m <<< (n + k) = (m <<< n) <<< k
  | 0 => rfl
  | k + 1 => by simp [← Nat.add_assoc, shiftLeft_add _ _ k, shiftLeft_succ]

@[simp] theorem shiftLeft_shiftRight (x n : Nat) : x <<< n >>> n = x := by
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-! ### Decidability of predicates -/

instance decidableBallLT :
  ∀ (n : Nat) (P : ∀ k, k < n → Prop) [∀ n h, Decidable (P n h)], Decidable (∀ n h, P n h)
| 0, _, _ => isTrue fun _ => (by cases ·)
| n + 1, P, H =>
  match decidableBallLT n (P · <| lt_succ_of_lt ·) with
  | isFalse h => isFalse (h fun _ _ => · _ _)
  | isTrue h =>
    match H n Nat.le.refl with
    | isFalse p => isFalse (p <| · _ _)
    | isTrue p => isTrue fun _ h' => (Nat.lt_succ_iff_lt_or_eq.1 h').elim (h _) fun hn => hn ▸ p

instance decidableForallFin (P : Fin n → Prop) [DecidablePred P] : Decidable (∀ i, P i) :=
  decidable_of_iff (∀ k h, P ⟨k, h⟩) ⟨fun m ⟨k, h⟩ => m k h, fun m k h => m ⟨k, h⟩⟩

instance decidableBallLE (n : Nat) (P : ∀ k, k ≤ n → Prop) [∀ n h, Decidable (P n h)] :
    Decidable (∀ n h, P n h) :=
  decidable_of_iff (∀ (k) (h : k < succ n), P k (le_of_lt_succ h))
    ⟨fun m k h => m k (lt_succ_of_le h), fun m k _ => m k _⟩

instance decidableExistsLT [h : DecidablePred p] : DecidablePred fun n => ∃ m : Nat, m < n ∧ p m
  | 0 => isFalse (by simp only [not_lt_zero, false_and, exists_const, not_false_eq_true])
  | n + 1 =>
    @decidable_of_decidable_of_iff _ _ (@instDecidableOr _ _ (decidableExistsLT (p := p) n) (h n))
      (by simp only [Nat.lt_succ_iff_lt_or_eq, or_and_right, exists_or, exists_eq_left])

instance decidableExistsLE [DecidablePred p] : DecidablePred fun n => ∃ m : Nat, m ≤ n ∧ p m :=
  fun n => decidable_of_iff (∃ m, m < n + 1 ∧ p m)
    (exists_congr fun _ => and_congr_left' Nat.lt_succ_iff)

/-- Dependent version of `decidableExistsLT`. -/
instance decidableExistsLT' {p : (m : Nat) → m < k → Prop} [I : ∀ m h, Decidable (p m h)] :
    Decidable (∃ m : Nat, ∃ h : m < k, p m h) :=
  match k, p, I with
  | 0, _, _ => isFalse (by simp)
  | (k + 1), p, I => @decidable_of_iff _ ((∃ m, ∃ h : m < k, p m (by omega)) ∨ p k (by omega))
      ⟨by rintro (⟨m, h, w⟩ | w); exact ⟨m, by omega, w⟩; exact ⟨k, by omega, w⟩,
        fun ⟨m, h, w⟩ => if h' : m < k then .inl ⟨m, h', w⟩ else
          by obtain rfl := (by omega : m = k); exact .inr w⟩
      (@instDecidableOr _ _
        (decidableExistsLT' (p := fun m h => p m (by omega)) (I := fun m h => I m (by omega)))
        inferInstance)

/-- Dependent version of `decidableExistsLE`. -/
instance decidableExistsLE' {p : (m : Nat) → m ≤ k → Prop} [I : ∀ m h, Decidable (p m h)] :
    Decidable (∃ m : Nat, ∃ h : m ≤ k, p m h) :=
  decidable_of_iff (∃ m, ∃ h : m < k + 1, p m (by omega)) <| by
    apply exists_congr
    intro
    exact ⟨fun ⟨h, w⟩ => ⟨le_of_lt_succ h, w⟩, fun ⟨h, w⟩ => ⟨lt_add_one_of_le h, w⟩⟩

instance decidableExistsFin (P : Fin n → Prop) [DecidablePred P] : Decidable (∃ i, P i) :=
  decidable_of_iff (∃ k, k < n ∧ ((h: k < n) → P ⟨k, h⟩))
    ⟨fun ⟨k, a⟩ => Exists.intro ⟨k, a.left⟩ (a.right a.left),
    fun ⟨i, e⟩ => Exists.intro i.val ⟨i.isLt, fun _ => e⟩⟩


  /-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

prelude
public import Init.Data.Ord.Basic
import all Init.Data.Ord.Basic

public section

/-! # Basic lemmas about comparing natural numbers

This file introduce some basic lemmas about compare as applied to natural
numbers.

Import `Std.Classes.Ord` in order to obtain the `TransOrd` and `LawfulEqOrd` instances for `Nat`.
-/
namespace Nat

theorem compare_eq_ite_lt (a b : Nat) :
    compare a b = if a < b then .lt else if b < a then .gt else .eq := by
  simp only [compare, compareOfLessAndEq]
  split
  · rfl
  next h =>
    match Nat.lt_or_eq_of_le (Nat.not_lt.1 h) with
    | .inl h => simp [h, Nat.ne_of_gt h]
    | .inr rfl => simp

@[deprecated compare_eq_ite_lt (since := "2025-03_28")]
def compare_def_lt := compare_eq_ite_lt

theorem compare_eq_ite_le (a b : Nat) :
    compare a b = if a ≤ b then if b ≤ a then .eq else .lt else .gt := by
  rw [compare_eq_ite_lt]
  split
  next hlt => simp [Nat.le_of_lt hlt, Nat.not_le.2 hlt]
  next hge =>
    split
    next hgt => simp [Nat.not_le.2 hgt]
    next hle => simp [Nat.not_lt.1 hge, Nat.not_lt.1 hle]

@[deprecated compare_eq_ite_le (since := "2025-03_28")]
def compare_def_le := compare_eq_ite_le

protected theorem compare_swap (a b : Nat) : (compare a b).swap = compare b a := by
  simp only [compare_eq_ite_le]; (repeat' split) <;> try rfl
  next h1 h2 => cases h1 (Nat.le_of_not_le h2)

protected theorem compare_eq_eq {a b : Nat} : compare a b = .eq ↔ a = b := by
  rw [compare_eq_ite_lt]; (repeat' split) <;> simp [Nat.ne_of_lt, Nat.ne_of_gt, *]
  next hlt hgt => exact Nat.le_antisymm (Nat.not_lt.1 hgt) (Nat.not_lt.1 hlt)

protected theorem compare_eq_lt {a b : Nat} : compare a b = .lt ↔ a < b := by
  rw [compare_eq_ite_lt]; (repeat' split) <;> simp [*]

protected theorem compare_eq_gt {a b : Nat} : compare a b = .gt ↔ b < a := by
  rw [compare_eq_ite_lt]; (repeat' split) <;> simp [Nat.le_of_lt, *]

protected theorem compare_ne_gt {a b : Nat} : compare a b ≠ .gt ↔ a ≤ b := by
  rw [compare_eq_ite_le]; (repeat' split) <;> simp [*]

protected theorem compare_ne_lt {a b : Nat} : compare a b ≠ .lt ↔ b ≤ a := by
  rw [compare_eq_ite_le]; (repeat' split) <;> simp [Nat.le_of_not_le, *]

protected theorem isLE_compare {a b : Nat} :
    (compare a b).isLE ↔ a ≤ b := by
  simp only [Nat.compare_eq_ite_le]
  repeat' split <;> simp_all

protected theorem isGE_compare {a b : Nat} :
    (compare a b).isGE ↔ b ≤ a := by
  rw [← Nat.compare_swap, Ordering.isGE_swap]
  exact Nat.isLE_compare

end Nat


/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module

prelude
public import Init.Omega

public section

set_option linter.missingDocs true

namespace Nat
universe u v

/--
Executes a monadic action on all the numbers less than some bound, in increasing order.

Example:
````lean example
#eval Nat.forM 5 fun i _ => IO.println i
````
````output
0
1
2
3
4
````
-/
@[inline] def forM {m} [Monad m] (n : Nat) (f : (i : Nat) → i < n → m Unit) : m Unit :=
  let rec @[specialize] loop : ∀ i, i ≤ n → m Unit
    | 0,   _ => pure ()
    | i+1, h => do f (n-i-1) (by omega); loop i (Nat.le_of_succ_le h)
  loop n (by simp)

/--
Executes a monadic action on all the numbers less than some bound, in decreasing order.

Example:
````lean example
#eval Nat.forRevM 5 fun i _ => IO.println i
````
````output
4
3
2
1
0
````
-/
@[inline] def forRevM {m} [Monad m] (n : Nat) (f : (i : Nat) → i < n → m Unit) : m Unit :=
  let rec @[specialize] loop : ∀ i, i ≤ n → m Unit
    | 0,   _ => pure ()
    | i+1, h => do f i (by omega); loop i (Nat.le_of_succ_le h)
  loop n (by simp)

/--
Iterates the application of a monadic function `f` to a starting value `init`, `n` times. At each
step, `f` is applied to the current value and to the next natural number less than `n`, in
increasing order.
-/
@[inline] def foldM {α : Type u} {m : Type u → Type v} [Monad m] (n : Nat) (f : (i : Nat) → i < n → α → m α) (init : α) : m α :=
  let rec @[specialize] loop : ∀ i, i ≤ n → α → m α
    | 0,   h, a => pure a
    | i+1, h, a => f (n-i-1) (by omega) a >>= loop i (Nat.le_of_succ_le h)
  loop n (by omega) init

/--
Iterates the application of a monadic function `f` to a starting value `init`, `n` times. At each
step, `f` is applied to the current value and to the next natural number less than `n`, in
decreasing order.
-/
@[inline] def foldRevM {α : Type u} {m : Type u → Type v} [Monad m] (n : Nat) (f : (i : Nat) → i < n → α → m α) (init : α) : m α :=
  let rec @[specialize] loop : ∀ i, i ≤ n → α → m α
    | 0,   h, a => pure a
    | i+1, h, a => f i (by omega) a >>= loop i (Nat.le_of_succ_le h)
  loop n (by omega) init

/--
Checks whether the monadic predicate `p` returns `true` for all numbers less that the given bound.
Numbers are checked in increasing order until `p` returns false, after which no further are checked.
-/
@[inline] def allM {m} [Monad m] (n : Nat) (p : (i : Nat) → i < n → m Bool) : m Bool :=
  let rec @[specialize] loop : ∀ i, i ≤ n → m Bool
    | 0,   _ => pure true
    | i+1 , h => do
      match (← p (n-i-1) (by omega)) with
      | true  => loop i (by omega)
      | false => pure false
  loop n (by simp)

/--
Checks whether there is some number less that the given bound for which the monadic predicate `p`
returns `true`. Numbers are checked in increasing order until `p` returns true, after which
no further are checked.
-/
@[inline] def anyM {m} [Monad m] (n : Nat) (p : (i : Nat) → i < n → m Bool) : m Bool :=
  let rec @[specialize] loop : ∀ i, i ≤ n → m Bool
    | 0,   _ => pure false
    | i+1, h => do
      match (← p (n-i-1) (by omega)) with
      | true  => pure true
      | false => loop i (Nat.le_of_succ_le h)
  loop n (by simp)

end Nat


/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
module
prelude

public import Init.Data.Nat.Gcd

public section

/-!
# Definitions and properties of `coprime`
-/

namespace Nat

/-!
### `coprime`
-/

/-- `m` and `n` are coprime, or relatively prime, if their `gcd` is 1. -/
@[reducible, expose] def Coprime (m n : Nat) : Prop := gcd m n = 1

-- if we don't inline this, then the compiler computes the GCD even if it already has it
@[inline] instance (m n : Nat) : Decidable (Coprime m n) := inferInstanceAs (Decidable (_ = 1))

theorem coprime_iff_gcd_eq_one : Coprime m n ↔ gcd m n = 1 := .rfl

theorem Coprime.gcd_eq_one : Coprime m n → gcd m n = 1 := id

theorem Coprime.symm : Coprime n m → Coprime m n := (gcd_comm m n).trans

theorem coprime_comm : Coprime n m ↔ Coprime m n := ⟨Coprime.symm, Coprime.symm⟩

theorem Coprime.dvd_of_dvd_mul_right (H1 : Coprime k n) (H2 : k ∣ m * n) : k ∣ m := by
  have t := dvd_gcd (Nat.dvd_mul_left k m) H2
  rwa [gcd_mul_left, H1.gcd_eq_one, Nat.mul_one] at t

theorem Coprime.dvd_of_dvd_mul_left (H1 : Coprime k m) (H2 : k ∣ m * n) : k ∣ n :=
  H1.dvd_of_dvd_mul_right (by rwa [Nat.mul_comm])

theorem Coprime.gcd_mul_left_cancel (m : Nat) (H : Coprime k n) : gcd (k * m) n = gcd m n :=
  have H1 : Coprime (gcd (k * m) n) k := by
    rw [Coprime, Nat.gcd_assoc, H.symm.gcd_eq_one, gcd_one_right]
  Nat.dvd_antisymm
    (dvd_gcd (H1.dvd_of_dvd_mul_left (gcd_dvd_left _ _)) (gcd_dvd_right _ _))
    (gcd_dvd_gcd_mul_left_left _ _ _)

theorem Coprime.gcd_mul_right_cancel (m : Nat) (H : Coprime k n) : gcd (m * k) n = gcd m n := by
  rw [Nat.mul_comm m k, H.gcd_mul_left_cancel m]

theorem Coprime.gcd_mul_left_cancel_right (n : Nat)
    (H : Coprime k m) : gcd m (k * n) = gcd m n := by
  rw [gcd_comm m n, gcd_comm m (k * n), H.gcd_mul_left_cancel n]

theorem Coprime.gcd_mul_right_cancel_right (n : Nat)
    (H : Coprime k m) : gcd m (n * k) = gcd m n := by
  rw [Nat.mul_comm n k, H.gcd_mul_left_cancel_right n]

theorem coprime_div_gcd_div_gcd
    (H : 0 < gcd m n) : Coprime (m / gcd m n) (n / gcd m n) := by
  rw [coprime_iff_gcd_eq_one, gcd_div (gcd_dvd_left m n) (gcd_dvd_right m n), Nat.div_self H]

theorem not_coprime_of_dvd_of_dvd (dgt1 : 1 < d) (Hm : d ∣ m) (Hn : d ∣ n) : ¬ Coprime m n :=
  fun co => Nat.not_le_of_gt dgt1 <| Nat.le_of_dvd Nat.zero_lt_one <| by
    rw [← co.gcd_eq_one]; exact dvd_gcd Hm Hn

theorem exists_coprime (m n : Nat) :
    ∃ m' n', Coprime m' n' ∧ m = m' * gcd m n ∧ n = n' * gcd m n := by
  cases eq_zero_or_pos (gcd m n) with
  | inl h0 =>
    rw [gcd_eq_zero_iff] at h0
    refine ⟨1, 1, gcd_one_left 1, ?_⟩
    simp [h0]
  | inr hpos =>
    exact ⟨_, _, coprime_div_gcd_div_gcd hpos,
      (Nat.div_mul_cancel (gcd_dvd_left m n)).symm,
      (Nat.div_mul_cancel (gcd_dvd_right m n)).symm⟩

theorem exists_coprime' (H : 0 < gcd m n) :
    ∃ g m' n', 0 < g ∧ Coprime m' n' ∧ m = m' * g ∧ n = n' * g :=
  let ⟨m', n', h⟩ := exists_coprime m n; ⟨_, m', n', H, h⟩

theorem Coprime.mul_left (H1 : Coprime m k) (H2 : Coprime n k) : Coprime (m * n) k :=
  (H1.gcd_mul_left_cancel n).trans H2

theorem Coprime.mul_right (H1 : Coprime k m) (H2 : Coprime k n) : Coprime k (m * n) :=
  (H1.symm.mul_left H2.symm).symm

theorem Coprime.coprime_dvd_left (H1 : m ∣ k) (H2 : Coprime k n) : Coprime m n := by
  apply eq_one_of_dvd_one
  rw [Coprime] at H2
  have := Nat.gcd_dvd_gcd_of_dvd_left n H1
  rwa [← H2]

theorem Coprime.coprime_dvd_right (H1 : n ∣ m) (H2 : Coprime k m) : Coprime k n :=
  (H2.symm.coprime_dvd_left H1).symm

theorem Coprime.coprime_mul_left (H : Coprime (k * m) n) : Coprime m n :=
  H.coprime_dvd_left (Nat.dvd_mul_left _ _)

theorem Coprime.coprime_mul_right (H : Coprime (m * k) n) : Coprime m n :=
  H.coprime_dvd_left (Nat.dvd_mul_right _ _)

theorem Coprime.coprime_mul_left_right (H : Coprime m (k * n)) : Coprime m n :=
  H.coprime_dvd_right (Nat.dvd_mul_left _ _)

theorem Coprime.coprime_mul_right_right (H : Coprime m (n * k)) : Coprime m n :=
  H.coprime_dvd_right (Nat.dvd_mul_right _ _)

theorem Coprime.coprime_div_left (cmn : Coprime m n) (dvd : a ∣ m) : Coprime (m / a) n := by
  match eq_zero_or_pos a with
  | .inl h0 =>
    rw [h0] at dvd
    rw [Nat.eq_zero_of_zero_dvd dvd] at cmn ⊢
    simp; assumption
  | .inr hpos =>
    let ⟨k, hk⟩ := dvd
    rw [hk, Nat.mul_div_cancel_left _ hpos]
    rw [hk] at cmn
    exact cmn.coprime_mul_left

theorem Coprime.coprime_div_right (cmn : Coprime m n) (dvd : a ∣ n) : Coprime m (n / a) :=
  (cmn.symm.coprime_div_left dvd).symm

theorem coprime_mul_iff_left : Coprime (m * n) k ↔ Coprime m k ∧ Coprime n k :=
  ⟨fun h => ⟨h.coprime_mul_right, h.coprime_mul_left⟩,
   fun ⟨h, _⟩ => by rwa [coprime_iff_gcd_eq_one, h.gcd_mul_left_cancel n]⟩

theorem coprime_mul_iff_right : Coprime k (m * n) ↔ Coprime k m ∧ Coprime k n := by
  rw [@coprime_comm k, @coprime_comm k, @coprime_comm k, coprime_mul_iff_left]

theorem Coprime.gcd_left (k : Nat) (hmn : Coprime m n) : Coprime (gcd k m) n :=
  hmn.coprime_dvd_left <| gcd_dvd_right k m

theorem Coprime.gcd_right (k : Nat) (hmn : Coprime m n) : Coprime m (gcd k n) :=
  hmn.coprime_dvd_right <| gcd_dvd_right k n

theorem Coprime.gcd_both (k l : Nat) (hmn : Coprime m n) : Coprime (gcd k m) (gcd l n) :=
  (hmn.gcd_left k).gcd_right l

theorem Coprime.mul_dvd_of_dvd_of_dvd (hmn : Coprime m n) (hm : m ∣ a) (hn : n ∣ a) : m * n ∣ a :=
  let ⟨_, hk⟩ := hm
  hk.symm ▸ Nat.mul_dvd_mul_left _ (hmn.symm.dvd_of_dvd_mul_left (hk ▸ hn))

@[simp] theorem coprime_zero_left (n : Nat) : Coprime 0 n ↔ n = 1 := by simp [Coprime]

@[simp] theorem coprime_zero_right (n : Nat) : Coprime n 0 ↔ n = 1 := by simp [Coprime]

theorem coprime_one_left : ∀ n, Coprime 1 n := gcd_one_left

theorem coprime_one_right : ∀ n, Coprime n 1 := gcd_one_right

@[simp] theorem coprime_one_left_eq_true (n) : Coprime 1 n = True := eq_true (coprime_one_left _)

@[simp] theorem coprime_one_right_eq_true (n) : Coprime n 1 = True := eq_true (coprime_one_right _)

@[simp] theorem coprime_self (n : Nat) : Coprime n n ↔ n = 1 := by simp [Coprime]

theorem Coprime.pow_left (n : Nat) (H1 : Coprime m k) : Coprime (m ^ n) k := by
  induction n with
  | zero => exact coprime_one_left _
  | succ n ih => have hm := H1.mul_left ih; rwa [Nat.pow_succ, Nat.mul_comm]

theorem Coprime.pow_right (n : Nat) (H1 : Coprime k m) : Coprime k (m ^ n) :=
  (H1.symm.pow_left n).symm

theorem Coprime.pow {k l : Nat} (m n : Nat) (H1 : Coprime k l) : Coprime (k ^ m) (l ^ n) :=
  (H1.pow_left _).pow_right _

theorem Coprime.eq_one_of_dvd {k m : Nat} (H : Coprime k m) (d : k ∣ m) : k = 1 := by
  rw [← H.gcd_eq_one, gcd_eq_left d]

theorem Coprime.gcd_mul (k : Nat) (h : Coprime m n) : gcd k (m * n) = gcd k m * gcd k n :=
  Nat.dvd_antisymm
    (gcd_mul_right_dvd_mul_gcd k m n)
    ((h.gcd_both k k).mul_dvd_of_dvd_of_dvd
      (gcd_dvd_gcd_mul_right_right ..)
      (gcd_dvd_gcd_mul_left_right ..))

theorem Coprime.mul_gcd (h : Coprime m n) (k : Nat) : gcd (m * n) k = gcd m k * gcd n k := by
  rw [gcd_comm, h.gcd_mul, gcd_comm k, gcd_comm k]

theorem gcd_mul_gcd_of_coprime_of_mul_eq_mul
    (cop : Coprime c d) (h : a * b = c * d) : a.gcd c * b.gcd c = c := by
  apply Nat.dvd_antisymm
  · apply ((cop.gcd_left _).mul_left (cop.gcd_left _)).dvd_of_dvd_mul_right
    rw [← h]
    apply Nat.mul_dvd_mul (gcd_dvd ..).1 (gcd_dvd ..).1
  · rw [gcd_comm a, gcd_comm b]
    refine Nat.dvd_trans ?_ (gcd_mul_right_dvd_mul_gcd ..)
    rw [h, gcd_mul_right_right d c]; apply Nat.dvd_refl


/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

prelude
public import Init.Meta

public section

namespace Nat

@[simp] protected theorem dvd_refl (a : Nat) : a ∣ a := ⟨1, by simp⟩

@[simp] protected theorem dvd_zero (a : Nat) : a ∣ 0 := ⟨0, by simp⟩

protected theorem dvd_mul_left (a b : Nat) : a ∣ b * a := ⟨b, Nat.mul_comm b a⟩
protected theorem dvd_mul_right (a b : Nat) : a ∣ a * b := ⟨b, rfl⟩

protected theorem dvd_trans {a b c : Nat} (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c :=
  match h₁, h₂ with
  | ⟨d, (h₃ : b = a * d)⟩, ⟨e, (h₄ : c = b * e)⟩ =>
    ⟨d * e, show c = a * (d * e) by simp[h₃,h₄, Nat.mul_assoc]⟩

protected theorem dvd_mul_left_of_dvd {a b : Nat} (h : a ∣ b) (c : Nat) : a ∣ c * b :=
  Nat.dvd_trans h (Nat.dvd_mul_left _ _)

protected theorem dvd_mul_right_of_dvd {a b : Nat} (h : a ∣ b) (c : Nat) : a ∣ b * c :=
  Nat.dvd_trans h (Nat.dvd_mul_right _ _)

protected theorem eq_zero_of_zero_dvd {a : Nat} (h : 0 ∣ a) : a = 0 :=
  let ⟨c, H'⟩ := h; H'.trans c.zero_mul

@[simp] protected theorem zero_dvd {n : Nat} : 0 ∣ n ↔ n = 0 :=
  ⟨Nat.eq_zero_of_zero_dvd, fun h => h.symm ▸ Nat.dvd_zero 0⟩

protected theorem dvd_add {a b c : Nat} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c :=
  let ⟨d, hd⟩ := h₁; let ⟨e, he⟩ := h₂; ⟨d + e, by simp [Nat.left_distrib, hd, he]⟩

protected theorem dvd_add_iff_right {k m n : Nat} (h : k ∣ m) : k ∣ n ↔ k ∣ m + n :=
  ⟨Nat.dvd_add h,
    match m, h with
    | _, ⟨d, rfl⟩ => fun ⟨e, he⟩ =>
      ⟨e - d, by rw [Nat.mul_sub_left_distrib, ← he, Nat.add_sub_cancel_left]⟩⟩

protected theorem dvd_add_iff_left {k m n : Nat} (h : k ∣ n) : k ∣ m ↔ k ∣ m + n := by
  rw [Nat.add_comm]; exact Nat.dvd_add_iff_right h

theorem dvd_mod_iff {k m n : Nat} (h: k ∣ n) : k ∣ m % n ↔ k ∣ m := by
  have := Nat.dvd_add_iff_left (m := m % n) <| Nat.dvd_trans h <| Nat.dvd_mul_right n (m / n)
  rwa [mod_add_div] at this

theorem le_of_dvd {m n : Nat} (h : 0 < n) : m ∣ n → m ≤ n
  | ⟨k, e⟩ => by
    revert h
    rw [e]
    match k with
    | 0 => intro hn; simp at hn
    | pk+1 =>
      intro
      have := Nat.mul_le_mul_left m (succ_pos pk)
      rwa [Nat.mul_one] at this

protected theorem dvd_antisymm : ∀ {m n : Nat}, m ∣ n → n ∣ m → m = n
  | _, 0, _, h₂ => Nat.eq_zero_of_zero_dvd h₂
  | 0, _, h₁, _ => (Nat.eq_zero_of_zero_dvd h₁).symm
  | _+1, _+1, h₁, h₂ => Nat.le_antisymm (le_of_dvd (succ_pos _) h₁) (le_of_dvd (succ_pos _) h₂)

theorem pos_of_dvd_of_pos {m n : Nat} (H1 : m ∣ n) (H2 : 0 < n) : 0 < m :=
  Nat.pos_of_ne_zero fun m0 => Nat.ne_of_gt H2 <| Nat.eq_zero_of_zero_dvd (m0 ▸ H1)

@[simp] protected theorem one_dvd (n : Nat) : 1 ∣ n := ⟨n, n.one_mul.symm⟩

theorem eq_one_of_dvd_one {n : Nat} (H : n ∣ 1) : n = 1 := Nat.dvd_antisymm H n.one_dvd

theorem mod_eq_zero_of_dvd {m n : Nat} (H : m ∣ n) : n % m = 0 := by
  let ⟨z, H⟩ := H; rw [H, mul_mod_right]

theorem dvd_of_mod_eq_zero {m n : Nat} (H : n % m = 0) : m ∣ n := by
  exists n / m
  have := (mod_add_div n m).symm
  rwa [H, Nat.zero_add] at this

theorem dvd_iff_mod_eq_zero {m n : Nat} : m ∣ n ↔ n % m = 0 :=
  ⟨mod_eq_zero_of_dvd, dvd_of_mod_eq_zero⟩

instance decidable_dvd : @DecidableRel Nat Nat (·∣·) :=
  fun _ _ => decidable_of_decidable_of_iff dvd_iff_mod_eq_zero.symm

theorem emod_pos_of_not_dvd {a b : Nat} (h : ¬ a ∣ b) : 0 < b % a := by
  rw [dvd_iff_mod_eq_zero] at h
  exact Nat.pos_of_ne_zero h

protected theorem mul_div_cancel' {n m : Nat} (H : n ∣ m) : n * (m / n) = m := by
  have := mod_add_div m n
  rwa [mod_eq_zero_of_dvd H, Nat.zero_add] at this

protected theorem div_mul_cancel {n m : Nat} (H : n ∣ m) : m / n * n = m := by
  rw [Nat.mul_comm, Nat.mul_div_cancel' H]

@[simp] theorem mod_mod_of_dvd (a : Nat) (h : c ∣ b) : a % b % c = a % c := by
  rw (occs := [2]) [← mod_add_div a b]
  have ⟨x, h⟩ := h
  subst h
  rw [Nat.mul_assoc, add_mul_mod_self_left]

protected theorem dvd_of_mul_dvd_mul_left
    (kpos : 0 < k) (H : k * m ∣ k * n) : m ∣ n := by
  let ⟨l, H⟩ := H
  rw [Nat.mul_assoc] at H
  exact ⟨_, Nat.eq_of_mul_eq_mul_left kpos H⟩

protected theorem dvd_of_mul_dvd_mul_right (kpos : 0 < k) (H : m * k ∣ n * k) : m ∣ n := by
  rw [Nat.mul_comm m k, Nat.mul_comm n k] at H; exact Nat.dvd_of_mul_dvd_mul_left kpos H

theorem dvd_sub {k m n : Nat} (h₁ : k ∣ m) (h₂ : k ∣ n) : k ∣ m - n :=
  if H : n ≤ m then
    (Nat.dvd_add_iff_left h₂).2 <| by rwa [Nat.sub_add_cancel H]
  else
    Nat.sub_eq_zero_of_le (Nat.le_of_not_le H) ▸ Nat.dvd_zero k

theorem dvd_sub_iff_right {m n k : Nat} (hkn : k ≤ n) (h : m ∣ n) : m ∣ n - k ↔ m ∣ k := by
  refine ⟨?_, dvd_sub h⟩
  let ⟨x, hx⟩ := h
  cases hx
  intro hy
  let ⟨y, hy⟩ := hy
  have hk : k = m * (x - y) := by
    rw [Nat.sub_eq_iff_eq_add hkn] at hy
    rw [Nat.mul_sub, hy, Nat.add_comm, Nat.add_sub_cancel]
  exact hk ▸ Nat.dvd_mul_right _ _

theorem dvd_sub_iff_left {m n k : Nat} (hkn : k ≤ n) (h : m ∣ k) : m ∣ n - k ↔ m ∣ n := by
  rw (occs := [2]) [← Nat.sub_add_cancel hkn]
  exact Nat.dvd_add_iff_left h

protected theorem mul_dvd_mul {a b c d : Nat} : a ∣ b → c ∣ d → a * c ∣ b * d
  | ⟨e, he⟩, ⟨f, hf⟩ =>
    ⟨e * f, by simp [he, hf, Nat.mul_left_comm, Nat.mul_comm]⟩

protected theorem mul_dvd_mul_left (a : Nat) (h : b ∣ c) : a * b ∣ a * c :=
  Nat.mul_dvd_mul (Nat.dvd_refl a) h

protected theorem mul_dvd_mul_right (h: a ∣ b) (c : Nat) : a * c ∣ b * c :=
  Nat.mul_dvd_mul h (Nat.dvd_refl c)

@[simp] theorem dvd_one {n : Nat} : n ∣ 1 ↔ n = 1 :=
  ⟨eq_one_of_dvd_one, fun h => h.symm ▸ Nat.dvd_refl _⟩

protected theorem mul_div_assoc (m : Nat) (H : k ∣ n) : m * n / k = m * (n / k) := by
  match Nat.eq_zero_or_pos k with
  | .inl h0 => rw [h0, Nat.div_zero, Nat.div_zero, Nat.mul_zero]
  | .inr hpos =>
    have h1 : m * n / k = m * (n / k * k) / k := by rw [Nat.div_mul_cancel H]
    rw [h1, ← Nat.mul_assoc, Nat.mul_div_cancel _ hpos]

/-! Helper theorems for `dvd` simproc -/

protected theorem dvd_eq_true_of_mod_eq_zero {m n : Nat} (h : n % m == 0) : (m ∣ n) = True := by
  simp [Nat.dvd_of_mod_eq_zero, eq_of_beq h]

protected theorem dvd_eq_false_of_mod_ne_zero {m n : Nat} (h : n % m != 0) : (m ∣ n) = False := by
  simp at h
  simp [dvd_iff_mod_eq_zero, h]

end Nat


/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Kim Morrison
-/
module

prelude
public import Init.Data.List.FinRange

public section

set_option linter.missingDocs true -- keep it documented
universe u

namespace Nat

/--
Iterates the application of a function `f` to a starting value `init`, `n` times. At each step, `f`
is applied to the current value and to the next natural number less than `n`, in increasing order.

Examples:
* `Nat.fold 3 f init = (init |> f 0 (by simp) |> f 1 (by simp) |> f 2 (by simp))`
* `Nat.fold 4 (fun i _ xs => xs.push i) #[] = #[0, 1, 2, 3]`
* `Nat.fold 0 (fun i _ xs => xs.push i) #[] = #[]`
-/
@[specialize] def fold {α : Type u} : (n : Nat) → (f : (i : Nat) → i < n → α → α) → (init : α) → α
  | 0,      f, a => a
  | succ n, f, a => f n (by omega) (fold n (fun i h => f i (by omega)) a)


/--
Iterates the application of a function `f` to a starting value `init`, `n` times. At each step, `f`
is applied to the current value and to the next natural number less than `n`, in increasing order.

This is a tail-recursive version of `Nat.fold` that's used at runtime.

Examples:
* `Nat.foldTR 3 f init = (init |> f 0 (by simp) |> f 1 (by simp) |> f 2 (by simp))`
* `Nat.foldTR 4 (fun i _ xs => xs.push i) #[] = #[0, 1, 2, 3]`
* `Nat.foldTR 0 (fun i _ xs => xs.push i) #[] = #[]`
-/
@[inline] def foldTR {α : Type u} (n : Nat) (f : (i : Nat) → i < n → α → α) (init : α) : α :=
  let rec @[specialize] loop : ∀ j, j ≤ n → α → α
    | 0,      h, a => a
    | succ m, h, a => loop m (by omega) (f (n - succ m) (by omega) a)
  loop n (by omega) init

/--
Iterates the application of a function `f` to a starting value `init`, `n` times. At each step, `f`
is applied to the current value and to the next natural number less than `n`, in decreasing order.

Examples:
* `Nat.foldRev 3 f init = (f 0 (by simp) <| f 1 (by simp) <| f 2 (by simp) init)`
* `Nat.foldRev 4 (fun i _ xs => xs.push i) #[] = #[3, 2, 1, 0]`
* `Nat.foldRev 0 (fun i _ xs => xs.push i) #[] = #[]`
-/
@[specialize] def foldRev {α : Type u} : (n : Nat) → (f : (i : Nat) → i < n → α → α) → (init : α) → α
  | 0,      f, a => a
  | succ n, f, a => foldRev n (fun i h => f i (by omega)) (f n (by omega) a)

/--
Checks whether there is some number less that the given bound for which `f` returns `true`.

Examples:
 * `Nat.any 4 (fun i _ => i < 5) = true`
 * `Nat.any 7 (fun i _ => i < 5) = true`
 * `Nat.any 7 (fun i _ => i % 2 = 0) = true`
 * `Nat.any 1 (fun i _ => i % 2 = 1) = false`
-/
@[specialize] def any : (n : Nat) → (f : (i : Nat) → i < n → Bool) → Bool
  | 0,      f => false
  | succ n, f => any n (fun i h => f i (by omega)) || f n (by omega)

/--
Checks whether there is some number less that the given bound for which `f` returns `true`.

This is a tail-recursive equivalent of `Nat.any` that's used at runtime.

Examples:
 * `Nat.anyTR 4 (fun i _ => i < 5) = true`
 * `Nat.anyTR 7 (fun i _ => i < 5) = true`
 * `Nat.anyTR 7 (fun i _ => i % 2 = 0) = true`
 * `Nat.anyTR 1 (fun i _ => i % 2 = 1) = false`
-/
@[inline] def anyTR (n : Nat) (f : (i : Nat) → i < n → Bool) : Bool :=
  let rec @[specialize] loop : (i : Nat) → i ≤ n → Bool
    | 0,      h => false
    | succ m, h => f (n - succ m) (by omega) || loop m (by omega)
  loop n (by omega)

/--
Checks whether `f` returns `true` for every number strictly less than a bound.

Examples:
 * `Nat.all 4 (fun i _ => i < 5) = true`
 * `Nat.all 7 (fun i _ => i < 5) = false`
 * `Nat.all 7 (fun i _ => i % 2 = 0) = false`
 * `Nat.all 1 (fun i _ => i % 2 = 0) = true`
-/
@[specialize] def all : (n : Nat) → (f : (i : Nat) → i < n → Bool) → Bool
  | 0,      f => true
  | succ n, f => all n (fun i h => f i (by omega)) && f n (by omega)

/--
Checks whether `f` returns `true` for every number strictly less than a bound.

This is a tail-recursive equivalent of `Nat.all` that's used at runtime.

Examples:
 * `Nat.allTR 4 (fun i _ => i < 5) = true`
 * `Nat.allTR 7 (fun i _ => i < 5) = false`
 * `Nat.allTR 7 (fun i _ => i % 2 = 0) = false`
 * `Nat.allTR 1 (fun i _ => i % 2 = 0) = true`
-/
@[inline] def allTR (n : Nat) (f : (i : Nat) → i < n → Bool) : Bool :=
  let rec @[specialize] loop : (i : Nat) → i ≤ n   → Bool
    | 0,      h => true
    | succ m, h => f (n - succ m) (by omega) && loop m (by omega)
  loop n (by omega)

/-! # csimp theorems -/

theorem fold_congr {α : Type u} {n m : Nat} (w : n = m)
     (f : (i : Nat) → i < n → α → α) (init : α) :
     fold n f init = fold m (fun i h => f i (by omega)) init := by
  subst m
  rfl

theorem foldRev_congr {α : Type u} {n m : Nat} (w : n = m)
     (f : (i : Nat) → i < n → α → α) (init : α) :
     foldRev n f init = foldRev m (fun i h => f i (by omega)) init := by
  subst m
  rfl

private theorem foldTR_loop_congr {α : Type u} {n m : Nat} (w : n = m)
     (f : (i : Nat) → i < n → α → α) (j : Nat) (h : j ≤ n) (init : α) :
     foldTR.loop n f j h init = foldTR.loop m (fun i h => f i (by omega)) j (by omega) init := by
  subst m
  rfl

@[csimp] theorem fold_eq_foldTR : @fold = @foldTR :=
  funext fun α => funext fun n => funext fun f => funext fun init =>
  let rec go : ∀ m n f, fold (m + n) f init = foldTR.loop (m + n) f m (by omega) (fold n (fun i h => f i (by omega)) init)
    | 0,      n, f => by
      simp only [foldTR.loop]
      have t : 0 + n = n := by omega
      rw [fold_congr t]
    | succ m, n, f => by
      have t : (m + 1) + n = m + (n + 1) := by omega
      rw [foldTR.loop]
      simp only [succ_eq_add_one]
      rw [fold_congr t, foldTR_loop_congr t, go, fold]
      congr
      omega
  go n 0 f

theorem any_congr {n m : Nat} (w : n = m) (f : (i : Nat) → i < n → Bool) : any n f = any m (fun i h => f i (by omega)) := by
  subst m
  rfl

private theorem anyTR_loop_congr {n m : Nat} (w : n = m) (f : (i : Nat) → i < n → Bool) (j : Nat) (h : j ≤ n) :
    anyTR.loop n f j h = anyTR.loop m (fun i h => f i (by omega)) j (by omega) := by
  subst m
  rfl

@[csimp] theorem any_eq_anyTR : @any = @anyTR :=
  funext fun n => funext fun f =>
  let rec go : ∀ m n f, any (m + n) f = (any n (fun i h => f i (by omega)) || anyTR.loop (m + n) f m (by omega))
    | 0,      n, f => by
      simp [anyTR.loop]
      have t : 0 + n = n := by omega
      rw [any_congr t]
    | succ m, n, f => by
      have t : (m + 1) + n = m + (n + 1) := by omega
      rw [anyTR.loop]
      simp only [succ_eq_add_one]
      rw [any_congr t, anyTR_loop_congr t, go, any, Bool.or_assoc]
      congr
      omega
  go n 0 f

theorem all_congr {n m : Nat} (w : n = m) (f : (i : Nat) → i < n → Bool) : all n f = all m (fun i h => f i (by omega)) := by
  subst m
  rfl

private theorem allTR_loop_congr {n m : Nat} (w : n = m) (f : (i : Nat) → i < n → Bool) (j : Nat) (h : j ≤ n) : allTR.loop n f j h = allTR.loop m (fun i h => f i (by omega)) j (by omega) := by
  subst m
  rfl

@[csimp] theorem all_eq_allTR : @all = @allTR :=
  funext fun n => funext fun f =>
  let rec go : ∀ m n f, all (m + n) f = (all n (fun i h => f i (by omega)) && allTR.loop (m + n) f m (by omega))
    | 0,      n, f => by
      simp [allTR.loop]
      have t : 0 + n = n := by omega
      rw [all_congr t]
    | succ m, n, f => by
      have t : (m + 1) + n = m + (n + 1) := by omega
      rw [allTR.loop]
      simp only [succ_eq_add_one]
      rw [all_congr t, allTR_loop_congr t, go, all, Bool.and_assoc]
      congr
      omega
  go n 0 f

/-! # `dfold` -/

private def dfoldCast {n : Nat} (α : (i : Nat) → (h : i ≤ n := by omega) → Type u)
    {i j : Nat} {hi : i ≤ n} (w : i = j) (x : α i hi) : α j (by omega) := by
  subst w
  exact x

@[local simp] private theorem dfoldCast_rfl (h : i ≤ n) (w : i = i) (x : α i h) : dfoldCast α w x = x := by
  simp [dfoldCast]

@[local simp] private theorem dfoldCast_trans (h : i ≤ n) (w₁ : i = j) (w₂ : j = k) (x : α i h) :
    dfoldCast @α w₂ (dfoldCast @α w₁ x) = dfoldCast @α (w₁.trans w₂) x := by
  cases w₁
  cases w₂
  simp [dfoldCast]

@[local simp] private theorem dfoldCast_eq_dfoldCast_iff {α : (i : Nat) → (h : i ≤ n := by omega) → Type u} {w₁ w₂ : i = j} {h : i ≤ n} {x : α i h} :
    dfoldCast @α w₁ x = dfoldCast (n := n) (fun i h => α i) (hi := hi) w₂ x ↔ w₁ = w₂ := by
  cases w₁
  cases w₂
  simp [dfoldCast]

private theorem apply_dfoldCast {α : (i : Nat) → (h : i ≤ n := by omega) → Type u}
    (f : (i : Nat) → (h : i < n) → α i → α (i + 1)) {i j : Nat} (h : i < n) {w : i = j} {x : α i (by omega)} :
    f j (by omega) (dfoldCast @α w x) = dfoldCast (n := n) (fun i h => α i) (hi := by omega) (by omega) (f i h x) := by
  subst w
  simp

/--
`Nat.dfold` evaluates `f` on the numbers up to `n` exclusive, in increasing order:
* `Nat.dfold f 3 init = init |> f 0 |> f 1 |> f 2`
The input and output types of `f` are indexed by the current index, i.e. `f : (i : Nat) → (h : i < n) → α i → α (i + 1)`.
-/
@[specialize]
def dfold (n : Nat) {α : (i : Nat) → (h : i ≤ n := by omega) → Type u}
    (f : (i : Nat) → (h : i < n) → α i → α (i + 1)) (init : α 0) : α n :=
  let rec @[specialize] loop : ∀ j, j ≤ n → α (n - j) → α n
    | 0,      h, a => a
    | succ m, h, a =>
      loop m (by omega) (dfoldCast @α (by omega) (f (n - succ m) (by omega) a))
  loop n (by omega) (dfoldCast @α (by omega) init)

/--
`Nat.dfoldRev` evaluates `f` on the numbers up to `n` exclusive, in decreasing order:
* `Nat.dfoldRev f 3 init = f 0 <| f 1 <| f 2 <| init`
The input and output types of `f` are indexed by the current index, i.e. `f : (i : Nat) → (h : i < n) → α (i + 1) → α i`.
-/
@[specialize]
def dfoldRev (n : Nat) {α : (i : Nat) → (h : i ≤ n := by omega) → Type u}
    (f : (i : Nat) → (h : i < n) → α (i + 1) → α i) (init : α n) : α 0 :=
  match n with
  | 0       => init
  | (n + 1) => dfoldRev n (α := fun i h => α i) (fun i h => f i (by omega)) (f n (by omega) init)

/-! # Theorems -/

/-! ### `fold` -/

@[simp] theorem fold_zero {α : Type u} (f : (i : Nat) → i < 0 → α → α) (init : α) :
    fold 0 f init = init := by simp [fold]

@[simp] theorem fold_succ {α : Type u} (n : Nat) (f : (i : Nat) → i < n + 1 → α → α) (init : α) :
    fold (n + 1) f init = f n (by omega) (fold n (fun i h => f i (by omega)) init) := by simp [fold]

@[grind =] theorem fold_eq_finRange_foldl {α : Type u} (n : Nat) (f : (i : Nat) → i < n → α → α) (init : α) :
    fold n f init = (List.finRange n).foldl (fun acc ⟨i, h⟩ => f i h acc) init := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [ih, List.finRange_succ_last, List.foldl_map]

theorem fold_add
    {α n m} (f : (i : Nat) → i < n + m → α → α) (init : α) :
    fold (n + m) f init =
      fold m (fun i h => f (n + i) (by omega))
        (fold n (fun i h => f i (by omega)) init) := by
  induction m with
  | zero => simp; rfl
  | succ m ih =>
    simp [fold_congr (Nat.add_assoc n m 1).symm, ih]

/-! ### `foldRev` -/

@[simp] theorem foldRev_zero {α : Type u} (f : (i : Nat) → i < 0 → α → α) (init : α) :
    foldRev 0 f init = init := by simp [foldRev]

@[simp] theorem foldRev_succ {α : Type u} (n : Nat) (f : (i : Nat) → i < n + 1 → α → α) (init : α) :
    foldRev (n + 1) f init = foldRev n (fun i h => f i (by omega)) (f n (by omega) init) := by
  simp [foldRev]

@[grind =] theorem foldRev_eq_finRange_foldr {α : Type u} (n : Nat) (f : (i : Nat) → i < n → α → α) (init : α) :
    foldRev n f init = (List.finRange n).foldr (fun ⟨i, h⟩ acc => f i h acc) init := by
  induction n generalizing init with
  | zero => simp
  | succ n ih => simp [ih, List.finRange_succ_last, List.foldr_map]

theorem foldRev_add
    {α n m} (f : (i : Nat) → i < n + m → α → α) (init : α) :
    foldRev (n + m) f init =
      foldRev n (fun i h => f i (by omega))
        (foldRev m (fun i h => f (n + i) (by omega)) init) := by
  induction m generalizing init with
  | zero => simp; rfl
  | succ m ih =>
    rw [foldRev_congr (Nat.add_assoc n m 1).symm]
    simp [ih]

/-! ### `any` -/

@[simp] theorem any_zero {f : (i : Nat) → i < 0 → Bool} : any 0 f = false := by simp [any]

@[simp] theorem any_succ {n : Nat} (f : (i : Nat) → i < n + 1 → Bool) :
    any (n + 1) f = (any n (fun i h => f i (by omega)) || f n (by omega)) := by simp [any]

@[grind =] theorem any_eq_finRange_any {n : Nat} (f : (i : Nat) → i < n → Bool) :
    any n f = (List.finRange n).any (fun ⟨i, h⟩ => f i h) := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, List.finRange_succ_last, List.any_map, Function.comp_def]

/-! ### `all` -/

@[simp] theorem all_zero {f : (i : Nat) → i < 0 → Bool} : all 0 f = true := by simp [all]

@[simp] theorem all_succ {n : Nat} (f : (i : Nat) → i < n + 1 → Bool) :
    all (n + 1) f = (all n (fun i h => f i (by omega)) && f n (by omega)) := by simp [all]

@[grind =] theorem all_eq_finRange_all {n : Nat} (f : (i : Nat) → i < n → Bool) :
    all n f = (List.finRange n).all (fun ⟨i, h⟩ => f i h) := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, List.finRange_succ_last, List.all_map, Function.comp_def]

/-! ### `dfold` -/

@[simp]
theorem dfold_zero
    {α : (i : Nat) → (h : i ≤ 0 := by omega) → Type u}
    (f : (i : Nat) → (h : i < 0) → α i → α (i + 1)) (init : α 0) :
    dfold 0 f init = init := by
  simp [dfold, dfold.loop]

private theorem dfold_loop_succ
    {α : (i : Nat) → (h : i ≤ n + 1 := by omega) → Type u}
    (f : (i : Nat) → (h : i < n + 1) → α i → α (i + 1))
    (a : α (n + 1 - (j + 1))) (w : j ≤ n):
    dfold.loop (n + 1) f (j + 1) (by omega) a =
      f n (by omega)
        (dfold.loop n (α := fun i h => α i) (fun i h => f i (by omega)) j w (dfoldCast @α (by omega) a)) := by
  induction j with
  | zero => simp [dfold.loop]
  | succ j ih =>
    rw [dfold.loop, ih _ (by omega)]
    congr 2
    simp only [succ_eq_add_one, dfoldCast_trans]
    rw [apply_dfoldCast (h := by omega) f]
    · erw [dfoldCast_trans (h := by omega)]
      erw [dfoldCast_eq_dfoldCast_iff]
      omega

@[simp]
theorem dfold_succ
    {α : (i : Nat) → (h : i ≤ n + 1 := by omega) → Type u}
    (f : (i : Nat) → (h : i < n + 1) → α i → α (i + 1)) (init : α 0) :
    dfold (n + 1) f init =
      f n (by omega) (dfold n (α := fun i h => α i) (fun i h => f i (by omega)) init) := by
  simp [dfold]
  rw [dfold_loop_succ (w := Nat.le_refl _)]
  congr 2
  simp only [dfoldCast_trans]
  erw [dfoldCast_eq_dfoldCast_iff]
  exact le_add_left 0 (n + 1)

-- This isn't a proper `@[congr]` lemma, but it doesn't seem possible to state one.
theorem dfold_congr
    {n m : Nat} (w : n = m)
    {α : (i : Nat) → (h : i ≤ n := by omega) → Type u}
    (f : (i : Nat) → (h : i < n) → α i → α (i + 1)) (init : α 0) :
      dfold n f init =
        cast (by subst w; rfl)
          (dfold m (α := fun i h => α i) (fun i h => f i (by omega)) init) := by
  subst w
  rfl

theorem dfold_add
    {α : (i : Nat) → (h : i ≤ n + m := by omega) → Type u}
    (f : (i : Nat) → (h : i < n + m) → α i → α (i + 1)) (init : α 0) :
    dfold (n + m) f init =
      dfold m (α := fun i h => α (n + i)) (fun i h => f (n + i) (by omega))
        (dfold n (α := fun i h => α i) (fun i h => f i (by omega)) init) := by
  induction m with
  | zero => simp; rfl
  | succ m ih =>
    simp [dfold_congr (Nat.add_assoc n m 1).symm, ih]

@[simp] theorem dfoldRev_zero
    {α : (i : Nat) → (h : i ≤ 0 := by omega) → Type u}
    (f : (i : Nat) → (_ : i < 0) → α (i + 1) → α i) (init : α 0) :
    dfoldRev 0 f init = init := by
  simp [dfoldRev]

@[simp] theorem dfoldRev_succ
    {α : (i : Nat) → (h : i ≤ n + 1 := by omega) → Type u}
    (f : (i : Nat) → (h : i < n + 1) → α (i + 1) → α i) (init : α (n + 1)) :
    dfoldRev (n + 1) f init =
      dfoldRev n (α := fun i h => α i) (fun i h => f i (by omega)) (f n (by omega) init) := by
  simp [dfoldRev]

@[congr]
theorem dfoldRev_congr
    {n m : Nat} (w : n = m)
    {α : (i : Nat) → (h : i ≤ n := by omega) → Type u}
    (f : (i : Nat) → (h : i < n) → α (i + 1) → α i) (init : α n) :
      dfoldRev n f init =
        dfoldRev m (α := fun i h => α i) (fun i h => f i (by omega))
          (cast (by subst w; rfl) init) := by
  subst w
  rfl

theorem dfoldRev_add
    {α : (i : Nat) → (h : i ≤ n + m := by omega) → Type u}
    (f : (i : Nat) → (h : i < n + m) → α (i + 1) → α i) (init : α (n + m)) :
    dfoldRev (n + m) f init =
      dfoldRev n (α := fun i h => α i) (fun i h => f i (by omega))
        (dfoldRev m (α := fun i h => α (n + i)) (fun i h => f (n + i) (by omega)) init) := by
  induction m with
  | zero => simp; rfl
  | succ m ih => simp [← Nat.add_assoc, ih]

end Nat
