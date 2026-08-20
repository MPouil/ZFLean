/-
Copyright (c) 2026 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/
import ZFLean.Naturals
import ZFLean.Integers
import ZFLean.Rationals
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith

/-!
# Transferring goals to the mathlib types

`ZFNat`, `ZFInt` and `ZFRat` are built inside ZF set theory, and each of them is the same type as
its mathlib counterpart. The `transfer` tactic uses that: it rewrites a goal about the ZF type
into the same goal about `ℕ`, `ℤ` or `ℚ`, runs the block on it, and since the rewriting happens in
place, closing the transferred goal closes the original one.

What is transported is not only the elements. A binder whose type is *built out of* the ZF type is
transported by congruence, so `ZFNat → ZFNat` becomes `ℕ → ℕ`, `ZFNat → ZFNat → ZFNat` becomes
`ℕ → ℕ → ℕ`, `(ZFNat → ZFNat) → ZFNat` becomes `(ℕ → ℕ) → ℕ`, `ZFNat → Prop` becomes `ℕ → Prop`,
and the same goes through products. Binders of the goal itself, quantifiers nested anywhere inside
it, and the hypotheses of the context all travel. The higher-order examples of the first section
are what that buys; the arithmetic of the second is the everyday use.
-/

open ZFSet

/-! ## Higher-order statements -/

/-- A curried binary operation on `ZFNat` becomes one on `ℕ`: `f : ℕ → ℕ → ℕ`, with its defining
equation. -/
example (f : ZFNat → ZFNat → ZFNat) (hf : ∀ a b, f a b = a + b) :
    ∀ a b c, f (f a b) c = f a (f b c) := by
  transfer ZFNat → ℕ =>
    intro a b c
    simp only [hf]
    omega

/-- A functional `(ZFNat → ZFNat) → ZFNat`, together with a hypothesis quantifying over the
functions it eats. -/
example (F : (ZFNat → ZFNat) → ZFNat) (hF : ∀ f g, (∀ n, f n = g n) → F f = F g)
    (f g : ZFNat → ZFNat) (h : ∀ n, f n = g n) : F f = F g := by
  transfer ZFNat → ℕ =>
    exact hF f g h

/-- A binary relation is a curried predicate, and travels as one. -/
example (R : ZFNat → ZFNat → Prop) (hR : ∀ a b, R a b ↔ a ≤ b) :
    ∀ a b c, R a b → R b c → R a c := by
  transfer ZFNat → ℕ =>
    intro a b c hab hbc
    rw [hR] at *
    omega

/-- Second order: a property of properties of `ZFNat` becomes one of properties of `ℕ`. -/
example (S : (ZFNat → Prop) → Prop) (hS : ∀ P : ZFNat → Prop, S P → ∃ n, P n)
    (P : ZFNat → Prop) (hP : S P) : ∃ n, P n := by
  transfer ZFNat → ℕ =>
    exact hS P hP

/-- The quantifier may be over a function type, and inside the goal rather than in front of it:
here `g` ranges over `ZFNat × ZFNat → ZFNat` and comes back as `ℕ × ℕ → ℕ`. -/
example (f : ZFNat → ZFNat → ZFNat) :
    ∃ g : ZFNat × ZFNat → ZFNat, ∀ a b, f a b = g (a, b) := by
  transfer ZFNat → ℕ =>
    exact ⟨fun p => f p.1 p.2, fun a b => rfl⟩

/-- Iteration travels: `f^[n]` is conjugated to the iterate of the transported `f`. -/
example (f : ZFNat → ZFNat) (h : ∀ m, f m = m + 1) (n : ℕ) : f^[n] 0 = (n : ZFNat) := by
  transfer ZFNat → ℕ =>
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, h]

/-- Strong induction on `ZFNat`, imported from `ℕ` rather than proved again. -/
example (P : ZFNat → Prop) (ih : ∀ n, (∀ m, m < n → P m) → P n) : ∀ n, P n := by
  transfer ZFNat → ℕ =>
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih' => exact ih n ih'

/-- The least number principle, from `Nat.find`. -/
example (P : ZFNat → Prop) (h : ∃ n, P n) : ∃ m, P m ∧ ∀ k, P k → m ≤ k := by
  transfer ZFNat → ℕ =>
    classical
    obtain ⟨n, hn⟩ := h
    exact ⟨Nat.find ⟨n, hn⟩, Nat.find_spec _, fun k hk => Nat.find_le hk⟩

/-- There is no infinite strictly decreasing sequence of `ZFNat`s. -/
example (f : ZFNat → ZFNat) : ¬ ∀ n, f (n + 1) < f n := by
  transfer ZFNat → ℕ =>
    intro h
    have key : ∀ n, f n + n ≤ f 0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => have := h n; omega
    have := key (f 0 + 1)
    omega

/-- A function pinned down by a recurrence, solved by induction in `ℕ`. -/
example (f : ZFNat → ZFNat) (h0 : f 0 = 0) (hs : ∀ n, f (n + 1) = f n + 2) :
    ∀ n, f n = 2 * n := by
  transfer ZFNat → ℕ =>
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih => rw [hs n, ih]; ring

/-- A strictly monotone function on `ZFNat` is injective. -/
example (f : ZFNat → ZFNat) (hm : ∀ a b : ZFNat, a < b → f a < f b) :
    ∀ a b, f a = f b → a = b := by
  transfer ZFNat → ℕ =>
    intro a b hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (Nat.ne_of_lt (hm a b h))
    · exact h
    · exact absurd hab.symm (Nat.ne_of_lt (hm b a h))

/-- An involution of `ZFRat` is surjective. -/
example (f : ZFRat → ZFRat) (hf : ∀ x, f (f x) = x) : ∀ y, ∃ x, f x = y := by
  transfer ZFRat → ℚ =>
    exact fun y => ⟨f y, hf y⟩

/-! ## Arithmetic imported from mathlib -/

/-- Divisibility travels, so the divisibility theory of `ℕ` is available on `ZFNat`. -/
example (n m : ZFNat) (h : n ∣ m) (hm : m ≠ 0) : n ≤ m := by
  transfer ZFNat → ℕ =>
    exact Nat.le_of_dvd (by omega) h

/-- One of two consecutive integers is even. -/
example (a : ZFInt) : 2 ∣ a * (a + 1) := by
  transfer ZFInt → ℤ =>
    exact Int.two_dvd_mul_add_one a

/-- Congruence modulo `n` is divisibility of the difference: the whole `Int.ModEq` API applies to
the `%` of `ZFInt`, which is `Int.emod` transported. -/
example (a b n : ZFInt) : a % n = b % n ↔ n ∣ (b - a) := by
  transfer ZFInt → ℤ =>
    exact _root_.Int.modEq_iff_dvd

/-- Euclidean division satisfies its defining identity, with a nonnegative remainder. -/
example (a b : ZFInt) (hb : b ≠ 0) : b * (a / b) + a % b = a ∧ 0 ≤ a % b := by
  transfer ZFInt → ℤ =>
    exact ⟨Int.mul_ediv_add_emod a b, Int.emod_nonneg _ hb⟩

/-- `ZFRat` is archimedean, because `ℚ` is. `n` ranges over `ℕ`, a type the transfer leaves
alone, and the cast `(n : ZFRat)` becomes the cast `(n : ℚ)`. -/
example (x : ZFRat) : ∃ n : ℕ, x < n := by
  transfer ZFRat → ℚ =>
    exact exists_nat_gt x

/-- `ZFRat` is densely ordered, because `ℚ` is. -/
example (x y : ZFRat) (h : x < y) : ∃ z : ZFRat, x < z ∧ z < y := by
  transfer ZFRat → ℚ =>
    exact ⟨(x + y) / 2, by constructor <;> linarith⟩

/-- A `ℚ` sitting in a `ZFRat` statement through the `RatCast` instance comes back as itself. -/
example (q : ℚ) (x : ZFRat) (hq : (q : ZFRat) ≠ 0) (h : x = q) : x / q = 1 := by
  transfer ZFRat → ℚ =>
    subst h
    exact div_self hq

/-! ## The tactic itself -/

/-- The equivalence may be named instead of the two types; the direction is read off its type. -/
example (n m : ZFNat) : n * m = m * n := by
  transfer ZFNat.ringEquivNat =>
    rw [Nat.mul_comm]

/-- Or given explicitly, next to the types. -/
example (a b : ZFInt) : a * b = b * a := by
  transfer ZFInt → ℤ using ZFInt.equivInt =>
    ring

/-- The block does not have to close the goal: what it leaves is a goal about `ℕ`, and closing it
later closes the goal about `ZFNat`. -/
example (n m : ZFNat) : n + m = m + n := by
  transfer ZFNat → ℕ => skip
  omega
