/-
Copyright (c) 2025 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/
import ZFLean.Basic
import ZFLean.Tactics
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Order.SuccPred.Basic
import Mathlib.Tactic.Ring

/-! # ZFC Natural numbers

This file defines the natural numbers in ZF set theory. The definition is based on the construction
of the Von Neumann ordinals, where each natural number is represented as the set of all smaller
natural numbers.

The set of all natural numbers is defined as the smallest inductive set. Because of the axiom of
separation, the definition relies on the existence of an infinite set, which is provided by the
`some_inf` constant. It can be shown that the choice of `some_inf` does not affect the definition of
the natural numbers and leads to isomorphic definitions.

The file also includes the definition of the `ZFNat` type for ZF natural numbers, and provides
various properties and usual arithmetic operations on natural numbers.

-/

namespace ZFSet

/-! ## Preliminary definitions -/

section Preamble

/--
A set `x` is transitive if every element of `x` is a subset of `x`:
`∀ y ∈ x, y ⊆ x`.
-/
def transitive (x : ZFSet) := ∀ y ∈ x, y ⊆ x

/--
An inductive set is defined as a set that contains the empty set `∅` and is closed
under successor.

The "successor" of a set `x` is defined as the insertion of `x` into itself.
-/
def inductive_set (E : ZFSet) : Prop := ∅ ∈ E ∧ ∀ n, n ∈ E → insert n n ∈ E

theorem trans_imp_insert_trans {x : ZFSet} : transitive x → transitive (insert x x) := by
  intro trans y
  rw [mem_insert_iff]
  rintro ⟨rfl | _⟩
  · simp_rw [subset_def, mem_insert_iff]
    exact fun _ => Or.inr
  · simp_rw [subset_def, mem_insert_iff]
    exact fun _ _ => Or.inr (trans y ‹_› ‹_›)

theorem inductive_sep {S} (P : ZFSet → Prop) (ind : inductive_set S)
  (h₀ : P ∅) (h₁ : ∀ n ∈ S, P n → P (insert n n)) : inductive_set <| S.sep P := by
  unfold inductive_set at *
  simp_rw [mem_sep]
  apply And.intro
  · exact ⟨ind.left, h₀⟩
  · rintro n ⟨_,_⟩
    apply And.intro
    · exact ind.right n ‹_›
    · exact h₁ n ‹_› ‹_›

theorem inductive_imp_transitive {E : ZFSet} (h : inductive_set E) :
  inductive_set (E.sep transitive) := by
  unfold inductive_set
  rcases h with ⟨_, hind⟩
  apply And.intro <;> simp_rw [mem_sep]
  · exact ⟨‹_›, by intro; rw [imp_iff_or_not]; exact Or.inr <| notMem_empty _⟩
  · rintro n ⟨_,_⟩
    apply And.intro
    · exact hind n ‹_›
    · exact trans_imp_insert_trans ‹_›

notation "ω" => omega

/-- The first Von Neumann ordinal `ω` is an inductive set. -/
theorem omega_inductive : inductive_set ω := ⟨omega_zero, fun _ => omega_succ⟩

/-- Witness for an infinite set, meant to be used for definitional purpose only. -/
private noncomputable abbrev some_inf := @Classical.choose _ inductive_set ⟨_, omega_inductive⟩

/-- The set `some_inf` is inductive. -/
private lemma inductive_some_inf : inductive_set some_inf := Classical.choose_spec _

private lemma some_inf_nonempty : some_inf ≠ ∅ := by
  intro h
  let h' := inductive_some_inf.left
  rw [h] at h'
  exact (ZFSet.notMem_empty ∅) h'

private lemma some_inf_mem_sep_inductive_set : some_inf ∈ some_inf.powerset.sep inductive_set := by
  simp only [mem_sep, mem_powerset, subset_refl, true_and]
  exact inductive_some_inf

end Preamble

/-! ## Natural numbers -/

section Naturals

/--
The set of natural numbers `Nat` is defined as the smallest inductive set.
This definition avoids the use of `ω`, even though `ω` may be thought of as `ℕ`.
-/
noncomputable def Nat : ZFSet := ⋂₀ ((powerset some_inf).sep inductive_set)

/-- The type of natural numbers `ZFNat` is defined as the subtype of `Nat`. -/
abbrev ZFNat := {x // x ∈ Nat}

namespace ZFNat

/--
`some_inf` is an inductive subset of `some_inf`:
`some_inf ∈ { a ⊆ some_inf | inductive_set a }`.
-/
private theorem some_inf_mem_powerset_some_inf_ind :
  some_inf ∈ some_inf.powerset.sep inductive_set :=
  mem_sep.mpr ⟨mem_powerset.mpr fun _ => id, inductive_some_inf⟩

/-- `Nat` is an infinite inductive set. -/
theorem Nat_subset_some_inf : Nat ⊆ some_inf := by
  intro n hn
  unfold Nat at hn
  rw [mem_sInter] at hn
  · have aux :
      n ∈ (⋃₀ (powerset some_inf).sep inductive_set : ZFSet) ∧
      (fun b => ∀ c, c ∈ (powerset some_inf).sep inductive_set → b ∈ c) n := by
        simp only [mem_sUnion, mem_sep, and_imp] at *
        exact ⟨
          ⟨some_inf,
            ⟨mem_powerset.mpr fun _ => id, inductive_some_inf⟩,
            hn some_inf (mem_powerset.mpr fun _ => id) (inductive_some_inf)⟩,
          fun _ _ _ => hn _ ‹_› ‹_›⟩
    simp only [mem_sep, mem_powerset, and_imp, mem_sUnion] at aux
    obtain ⟨⟨_, ⟨left, _⟩, _⟩, _⟩ := aux
    apply left
    assumption
  · exact ⟨some_inf, some_inf_mem_powerset_some_inf_ind⟩

theorem zero_in_Nat : ∅ ∈ Nat := by
  unfold Nat
  rw [mem_sInter]
  · intro x hx
    rw [mem_sep] at hx
    exact hx.right.left
  · exact ⟨some_inf, some_inf_mem_powerset_some_inf_ind⟩

abbrev nat_zero : ZFNat := ⟨∅, zero_in_Nat⟩

def nat_lt (x y : ZFNat) : Prop := x.val ∈ y.val
def nat_le (x y : ZFNat) : Prop := nat_lt x y ∨ x = y

theorem not_lt_zero {n : ZFNat} : ¬ nat_lt n nat_zero := fun _ => notMem_empty _ ‹_›
theorem zero_lt_ne_zero {n : ZFNat} : nat_lt nat_zero  n → n ≠ nat_zero := by
  intro h h'
  subst h'
  absurd not_lt_zero h
  trivial

/-- Any inductive set contains zero. -/
lemma zero_mem_inductive {a} (h : inductive_set a) : ↑nat_zero.val ∈ a := h.left

/-- Any inductive set containing an element also contains its successor. -/
theorem insert_mem_inductive {a n} (h : inductive_set a) (h' : n ∈ a) : insert n n ∈ a :=
  h.right n h'

theorem some_inf_powerset_sep_inductive_nonempty : (some_inf.powerset.sep inductive_set).Nonempty :=
  ⟨some_inf, some_inf_mem_powerset_some_inf_ind⟩

/-- Any inductive set is a subset of `some_inf`. -/
theorem inductive_subset_some_inf_contains_Nat {a} (h : inductive_set a) (h' : a ⊆ some_inf) :
  Nat ⊆ a := by
  intro n hn
  unfold Nat at hn
  rw [mem_sInter] at hn
  · have aux :
      n ∈ (⋃₀ (powerset some_inf).sep inductive_set : ZFSet) ∧
      (fun b => ∀ c, c ∈ (powerset some_inf).sep inductive_set → b ∈ c) n := by
        simp only [mem_sUnion, mem_sep, and_imp] at *
        exact ⟨
          ⟨some_inf,
            ⟨mem_powerset.mpr fun _ => id, inductive_some_inf⟩,
            hn some_inf (mem_powerset.mpr fun _ => id) (inductive_some_inf)⟩,
            fun _ _ _ => hn _ ‹_› ‹_›⟩
    simp only [mem_sep, mem_powerset, and_imp, mem_sUnion] at aux
    exact aux.2 _ h' h
  · exact some_inf_powerset_sep_inductive_nonempty

theorem succ_mem_Nat' {n} (h : n ∈ Nat) : insert n n ∈ Nat := by
  have all_sub_ind : ∀ a, a ∈ some_inf.powerset.sep inductive_set → insert n n ∈ a := by
    intro a ha
    rw [mem_sep] at ha
    exact ha.2.2 n (inductive_subset_some_inf_contains_Nat ha.2 (mem_powerset.mp ha.1) h)
  unfold Nat
  rw [mem_sInter]
  · exact (all_sub_ind · ·)
  · exact some_inf_powerset_sep_inductive_nonempty

/--
The successor function `succ` is build from the insertion of a set into itself embedded into the
`ZFNat` type.
-/
def succ (n : ZFNat) : ZFNat :=
  let ⟨n, h⟩ := n
  have p : insert n n ∈ Nat := succ_mem_Nat' h
  ⟨insert n n, p⟩

instance nat_one : One ZFNat := ⟨succ nat_zero⟩

theorem nat_one_eq : 1 = succ nat_zero := rfl

theorem succ_ne_zero : ∀ n, succ n ≠ nat_zero := by
  rintro ⟨n, hn⟩ h
  rw [succ, Subtype.mk.injEq, ZFSet.ext_iff] at h
  simp only [mem_insert_iff, notMem_empty, iff_false, not_or] at h
  exact h n |>.1 rfl

theorem succ_inj_aux {m n a : ZFSet} (h : insert m m = insert n n) (h' : a ∈ m) : a ∈ n := by
  have d' : a ∈ m ∨ a = m ↔ a ∈ n ∨ a = n := by
    have : a ∈ insert m m ↔ a ∈ n ∨ a = n := by
      rw [h, mem_insert_iff]
      exact Or.comm
    rw [mem_insert_iff, _root_.or_comm] at this
    assumption
  let h'' := mem_insert m m
  rw [h] at h''
  simp only [mem_insert_iff] at h''
  rcases h'' with rfl | h''
  · assumption
  · rcases d'.mp (Or.inl h') with _ | rfl
    · assumption
    · absurd mem_asymm h''
      assumption

theorem succ_inj_aux' {m n : ZFSet} (h : insert m m = insert n n) : m = n :=
  ext fun _ => ⟨succ_inj_aux h, succ_inj_aux <| Eq.symm h⟩

theorem succ_inj {m n} (h : succ m = succ n) : m = n := by
  let ⟨m, hm⟩ := m
  let ⟨n, hn⟩ := n
  simp only [succ, Subtype.mk.injEq] at *
  ext1
  exact ⟨succ_inj_aux h, succ_inj_aux (Eq.symm h)⟩

/-- Any inductive set `a` separated by an inductive predicate `P` is inductive. -/
theorem sep_of_ind_is_ind (P : ZFSet → Prop) {a} (h : inductive_set a)
  (h₀ : P ∅) (ih : ∀ n, n ∈ a → P n → P (insert n n)) : inductive_set (a.sep P) := by
  unfold inductive_set at *
  apply And.intro
  · exact mem_sep.mpr ⟨h.left, h₀⟩
  · simp only [mem_sep, and_imp]
    intros
    exact ⟨h.right _ ‹_›, ih _ ‹_› ‹_›⟩

/-! ## Recursion on natural numbers -/

section Recursion

theorem succ_subrelation_mem' :
  Subrelation (fun x y => insert x x = y) (fun x y : ZFSet => x ∈ y) := by
  intro _ _ _
  subst_eqs
  rw [mem_insert_iff]
  left
  rfl

theorem succ_wf' : @WellFounded ZFSet (fun x y => insert x x = y) := by
  apply Subrelation.wf
  · exact succ_subrelation_mem'
  · exact mem_wf

open Function in
theorem mem_wf' : @WellFounded ZFNat (·.1 ∈ ·.1) := by
  have : (fun x y : ZFNat => x.1 ∈ y.1) = ((fun x y : ZFSet => x ∈ y) on Subtype.val) := rfl
  rw [this]
  apply WellFounded.onFun
  exact mem_wf

/-- The relation built over the successor function is a subrelation of the membership relation. -/
theorem succ_subrelation_mem : Subrelation (succ · = ·) (·.1 ∈ ·.1) := by
  intro _ _ _
  simp only [succ] at *
  subst_eqs
  rw [mem_insert_iff]
  left
  rfl

theorem succ_wf : @WellFounded ZFNat (succ · = ·) := by
  apply Subrelation.wf
  · exact succ_subrelation_mem
  · exact mem_wf'

theorem lt_wf : @WellFounded ZFNat nat_lt := mem_wf'

instance : WellFoundedRelation ZFNat where
  rel := nat_lt
  wf := lt_wf

/--
The induction principle for sets in `Nat`. This principle is meant to be used for definitional
purposes only.
-/
lemma ind {P : ZFSet → Prop} (n : ZFSet)
  (h : n ∈ Nat) (zero : P ∅) (succ : ∀ n ∈ Nat, P n → P (insert n n)) : P n := by
  have : Nat.sep P |>.inductive_set := by
    unfold inductive_set
    apply And.intro
    · exact mem_sep.mpr ⟨zero_in_Nat, ‹_›⟩
    · simp only [mem_sep, and_imp]
      intros
      exact ⟨succ_mem_Nat' ‹_›, succ _ ‹_› ‹_›⟩
  let p := inductive_subset_some_inf_contains_Nat this
  let p' := fun x (_ : x ∈ Nat.sep P) => Nat_subset_some_inf (ZFSet.sep_subset_self ‹_›)
  simp_rw [subset_def, mem_sep] at p
  simp only [mem_sep] at p'
  exact p p' h |>.right

/-- The (weak) induction principle for natural numbers. -/
theorem induction {P : ZFNat → Prop} (n : ZFNat)
  (zero : P nat_zero) (succ : ∀ n, P n → P (succ n)) : P n := by classical
  let ⟨n, hn⟩ := n
  let P' x := if hx : x ∈ Nat then P ⟨x, hx⟩ else unreachable!
  have : P' n = P ⟨n, hn⟩ := dif_pos hn
  rw [← this]
  apply @ind P' n hn
  · unfold P'
    simpa [hn, zero_in_Nat] using zero
  · intro m hm hm'
    unfold P' at *
    rw [dif_pos hm] at hm'
    rw [dif_pos <| succ_mem_Nat' hm]
    exact succ ⟨m, hm⟩ hm'

--@[cases_eliminator]
--theorem cases {P : ZFNat → Prop} (n : ZFNat) (zero : P nat_zero.zero) (succ : ∀ n, P (succ n)) : P n :=
--  induction n zero fun n _ => succ n

theorem every_nat_transitive {n : ZFSet} (h : n ∈ Nat) : transitive n := by
  unfold transitive
  apply ind _ h
  · intros _ _
    exact False.elim (notMem_empty _ ‹_›)
  · intros _ _ ih _ hy _ _
    rw [mem_insert_iff] at hy ⊢
    rcases hy with rfl | _
    · exact Or.inr ‹_›
    · exact Or.inr (ih _ ‹_› ‹_›)

theorem lt_succ {n : ZFNat} : nat_lt n (succ n) := mem_insert _ _
theorem le_succ {n : ZFNat} : nat_le n (succ n) := Or.inl lt_succ

theorem lt_trans {x y z : ZFNat} : nat_lt x y → nat_lt y z → nat_lt x z :=
  fun _ _ => every_nat_transitive z.2 _ ‹_› ‹_›

theorem lt_le_iff {n m} : nat_le n m ↔ nat_lt n (succ m) := by
  apply Iff.intro
  · rintro (_ | rfl)
    · exact lt_trans ‹_› lt_succ
    · exact lt_succ
  · intro h
    let ⟨n, hn⟩ := n
    let ⟨m, hm⟩ := m
    dsimp [nat_lt, succ] at *
    rw [mem_insert_iff] at h
    rcases h with rfl | _
    · right; rfl
    · left; assumption

/-- The (strong) induction principle for natural numbers. -/
theorem strong_induction {P : ZFNat → Prop} (n : ZFNat)
  (ind : ∀ n, (∀ m, nat_lt m n → P m) → P n) : P n := by
  let Q x := ∀ (m : ZFNat) (_ : nat_lt m x), P m
  have aux {x} : Q x := by
    induction x using induction with
    | zero =>
      intros _ _
      exact False.elim (not_lt_zero ‹_›)
    | succ n ih =>
      intros m hm
      unfold Q at ih
      by_cases h : m = n
      · subst h
        exact ind _ ih
      · have h' : nat_lt m n := by
          rcases lt_le_iff.mpr hm with (_ | rfl)
          · assumption
          · contradiction
        exact ih m h'
  exact ind _ aux

theorem mem_Nat_of_mem_mem_Nat {n m : ZFSet} (hn : n ∈ Nat) : m ∈ n → m ∈ Nat := by
  apply ZFNat.ind n hn
  · intro h
    nomatch notMem_empty m h
  · intro n hn ih hm
    rw [mem_insert_iff] at hm
    rcases hm with rfl | hm
    · exact hn
    · exact ih hm

theorem not_zero_imp_succ {n : ZFNat} : n ≠ nat_zero → ∃ m, n = succ m := by
  induction n using induction with
  | zero => intro h; contradiction
  | succ n _ =>
    intro
    exact exists_apply_eq_apply' succ n

lemma sUnion_insert_nat {x : ZFSet} (h : x ∈ Nat) : (⋃₀ (insert x x) : ZFSet) = x := by
  apply ind _ h
  · rw [sUnion_insert, sUnion_empty]
    ext1
    simp only [mem_union, notMem_empty, or_self]
  · intros n _ ih
    rw [sUnion_insert, ih]
    ext1
    simp only [mem_union, mem_insert_iff, or_self_right]

theorem pred_in_Nat' ⦃x : ZFSet⦄ (h : x ∈ Nat) : (⋃₀ x : ZFSet) ∈ Nat := by
  apply ind _ h
  · rw [sUnion_empty]
    exact zero_in_Nat
  · intros
    rw [sUnion_insert_nat] <;> assumption

/-- The predecessor function on natural numbers, defined directly as the union of a set. -/
def pred (x : ZFNat) : ZFNat := x.map sUnion pred_in_Nat'

theorem pred_eq (n : ZFNat) : pred n = ⟨⋃₀ n.val, pred_in_Nat' n.property⟩ := rfl

@[simp]
theorem pred_zero : pred nat_zero = nat_zero := by
  unfold pred
  rw [Subtype.map, Subtype.mk.injEq, sUnion_empty]

@[simp]
theorem pred_one : pred 1 = nat_zero := by
  unfold pred
  rw [nat_one_eq, Subtype.map, Subtype.mk.injEq]
  dsimp [succ]
  rw [LawfulSingleton.insert_empty_eq, sUnion_singleton]

@[simp]
theorem pred_succ {n : ZFNat} : pred (succ n) = n := by
  let ⟨_, _⟩ := n
  simp only [pred, succ, Subtype.map]
  congr
  exact sUnion_insert_nat ‹_›

@[simp]
theorem succ_pred {n : ZFNat} (h : n ≠ nat_zero) : succ (pred n) = n := by
  induction n using strong_induction with
  | ind n ih =>
    obtain ⟨m, hm⟩ := not_zero_imp_succ h
    subst hm
    by_cases h' : m = nat_zero <;> subst_eqs <;> rw [pred_succ]

private theorem succ_lift_eq {x : ZFNat} : ↑(succ x) = insert x.val x.val := by rfl

private theorem succ_eq (n : ZFSet) (n_Nat : n ∈ Nat) :
  ⟨insert n n, succ_mem_Nat' n_Nat⟩ = succ ⟨n, n_Nat⟩ := by rfl

/--
The recursion principle for sets in `Nat`. This principle is meant to be used for definitional
purposes only.
-/
noncomputable def rec'.{u} {motive : ZFSet → Sort u} (n : ZFSet) (h : n ∈ Nat)
  (zero : motive ∅) (succ : Π x ∈ Nat, motive x → motive (insert x x)) : motive n := by
  apply succ_wf.fix (C := fun x => motive x.val) (x := ⟨n, h⟩)
  intro x ih
  by_cases x_eq_0 : x = nat_zero
  · subst x_eq_0
    exact zero
  · specialize ih _ (succ_pred x_eq_0)
    specialize succ (pred x) (pred x).2 ih
    conv at succ =>
      arg 1
      rw [← succ_lift_eq, succ_pred x_eq_0]
    assumption
--
/-- Provides the base case of the recursion principle for sets in `Nat`. -/
theorem rec'_zero.{u} {motive : ZFSet → Sort u}
  (zero : motive ∅) (succ : Π x ∈ Nat, motive x → motive (insert x x)) :
  ZFNat.rec' ∅ zero_in_Nat zero succ = zero := by
    unfold ZFNat.rec' WellFounded.fix
    beta_reduce
    rw [WellFounded.fixF_eq, dite_cond_eq_true]
    exact eq_self _


/-- Provides the inductive step of the recursion principle for sets in `Nat`. -/
theorem rec'_succ.{u} {motive : ZFSet → Sort u} (n : ZFSet) (n_Nat : n ∈ Nat)
  (zero : motive ∅) (succ : Π x ∈ Nat, motive x → motive (insert x x)) :
  rec' (insert n n) (succ_mem_Nat' n_Nat) zero succ = succ n n_Nat (rec' n n_Nat zero succ) := by
    unfold ZFNat.rec' WellFounded.fix
    beta_reduce
    rw [WellFounded.fixF_eq, dite_cond_eq_false]
    · apply cast_eq_iff_heq.mpr
      · congr
        · conv => enter [1, 1]; rw [succ_eq _ n_Nat, pred_succ]
        · exact proof_irrel_heq ..
        · conv =>
            left
            conv => arg 1; rw [succ_eq _ n_Nat]
            rw [pred_succ]
        · exact proof_irrel_heq ..
        · apply succ_pred
          rw [succ_eq _ n_Nat]
          exact succ_ne_zero _
      · apply eq_false
        intro h
        rw [succ_eq _ n_Nat] at h
        exact succ_ne_zero _ h

/--
The recursion principle for natural numbers. This recursor allows inductive
definitions over natural numbers to be defined in a more natural way.
-/
@[induction_eliminator]
noncomputable def rec.{u} {motive : ZFNat → Sort u} (n : ZFNat)
  (zero : motive nat_zero) (succ : Π x, motive x → motive (succ x)) : motive n := by classical
  let ⟨n, hn⟩ := n
  let motive' (x : ZFSet) := if hx : x ∈ Nat then motive ⟨x, hx⟩ else unreachable!
  have : motive' n = motive ⟨n, hn⟩ := dif_pos hn
  rw [← this]
  apply @ZFNat.rec' motive' n hn
  · unfold motive'
    simpa [hn, zero_in_Nat] using zero
  · intro m hm hm'
    unfold motive' at *
    rw [dif_pos hm] at hm'
    rw [dif_pos <| succ_mem_Nat' hm]
    exact succ ⟨m, hm⟩ hm'

/--
The induction principle of `ZFNat` is a universe-specialized version of the recursion principle.
-/
@[simp]
theorem induction_is_rec_into_Prop {motive : ZFNat → Prop} :
  induction = ZFNat.rec (motive := motive) := rfl

theorem rec_zero.{u} {motive : ZFNat → Sort u}
  (zero : motive nat_zero) (succ : Π x, motive x → motive (succ x)) :
  rec nat_zero zero succ = zero := by conv => arg 1; simp [ZFNat.rec,ZFNat.rec'_zero]

theorem rec_succ.{u} {motive : ZFNat → Sort u} (n : ZFNat)
  (zero : motive nat_zero) (succ' : Π x, motive x → motive (succ x)) :
  rec (succ n) zero succ' = succ' n (ZFNat.rec n zero succ') := by
    simp [ZFNat.rec, succ, ZFNat.rec'_succ _ n.property]

end Recursion

section Arithmetic

/-- The addition function on natural numbers, defined inductively. -/
protected noncomputable abbrev add (n m : ZFNat) : ZFNat := ZFNat.rec n m (fun _ : ZFNat => succ)

lemma add_one_eq_succ {n : ZFNat} : n.add 1 = succ n := by
  induction n with
  | zero => rw [ZFNat.add, ZFNat.rec_zero, nat_one_eq]
  | succ _ ih => rw [ZFNat.add, ZFNat.rec_succ, ← ZFNat.add, ih]

lemma add_one_eq_succ' {n : ZFNat} : ZFNat.add 1 n = succ n := by
  rw [ZFNat.add, nat_one_eq, rec_succ, rec_zero]

end Arithmetic

noncomputable abbrev nsmul.{u} : ℕ → ZFNat.{u} → ZFNat.{u}
  | 0, _ => nat_zero
  | n+1, m => m.add <| nsmul n m

noncomputable def toNat (n : ZFNat) : ℕ := ZFNat.rec n 0 (fun _ => Nat.succ)
noncomputable def ofNat (n : ℕ) : ZFNat := nsmul n 1

/-- `Nat` is an inductive set. -/
theorem ZNat'.is_inductive : inductive_set Nat where
  left := ZFNat.zero_in_Nat
  right := fun _ _ => ZFNat.succ_mem_Nat' ‹_›

noncomputable def eNat : ZFNat ≃ ℕ where
  toFun := toNat
  invFun := ofNat
  left_inv := by
    intro n
    induction n with
    | zero =>
      rw [toNat, ZFNat.rec_zero]
      rfl
    | succ n ih =>
      rw [toNat, ZFNat.rec_succ,
        ←toNat, ofNat, nsmul, ←ofNat, ih, add_one_eq_succ']
  right_inv := by
    intro n
    induction n with
    | zero =>
      rw [ofNat, toNat, ZFNat.rec_zero]
    | succ n ih =>
      rw [ofNat, nsmul, add_one_eq_succ', ←ofNat, toNat, ZFNat.rec_succ, ←toNat, ih]

theorem eNat_def (n : ZFNat) : eNat n = ZFNat.rec n 0 (fun _ => Nat.succ) := by rfl

noncomputable instance : DecidableEq ZFNat := fun a b => Classical.propDecidable (a = b)
noncomputable instance inst_commsemiring : CommSemiring ZFNat := eNat.commSemiring
noncomputable instance inst_isdomain : IsDomain ZFNat := eNat.isDomain
noncomputable instance inst_div : Div ZFNat := eNat.div
noncomputable instance inst_preord : Preorder ZFNat := eNat.preorder
noncomputable instance inst_linord : LinearOrder ZFNat := eNat.linearOrder
/--
There are instances of < and ≤ derived from the fact that ZFNat is a subtype of ZFSet.
They (should) are logically equivalent but the proof hasn't been written yet.
-/
--instance inst_add : Add ZFNat := inst_commsemiring.toAdd
noncomputable instance inst_lt : LT ZFNat := inst_linord.toLT
noncomputable instance inst_le : LE ZFNat := inst_linord.toLE
noncomputable instance inst_mem : Membership ZFNat ZFNat := ⟨fun x Y => x.val ∈ Y.val⟩


theorem hom_zero : (0 : ZFNat) = ⟨∅, ZFNat.zero_in_Nat⟩ := by rfl
theorem hom_one :
    (1 : ZFNat) = ⟨insert ∅ ∅, by exact insert_mem_inductive ZNat'.is_inductive ZFNat.zero_in_Nat⟩
    := by rfl
theorem hom_succ {a : ZFNat} {b : ℕ} : (eNat a = b) → (eNat a.succ = b.succ) := by
  rw [eNat_def, eNat_def, ZFNat.rec_succ]
  induction b with
  | zero =>
    intro atz
    by_cases aez : a = nat_zero
    · rw [aez, ZFNat.rec_zero]
    · obtain ⟨c, hc⟩ := ZFNat.not_zero_imp_succ aez
      rw [hc, ZFNat.rec_succ] at atz
      nomatch Nat.succ_ne_zero _ atz
  | succ i ih =>
    rw [Nat.add_one]
    intro ats
    rw [ats]

@[zfnat_to_nat]
theorem transfer_succ (a : ZFNat) : eNat a.succ = (eNat a).succ := hom_succ rfl

@[zfnat_to_nat]
theorem transfer_zero : eNat 0 = 0 := by rw [eNat_def, hom_zero, rec_zero]

@[zfnat_to_nat← ]
def transfer_lt := eNat.lt_def

@[zfnat_to_nat← ]
def transfer_le := eNat.le_def

@[zfnat_to_nat]
def transfer_add (a b : ZFNat) := eNat.eq_symm_apply.mp <| eNat.add_def a  b

@[zfnat_to_nat]
def transfer_mul (a b : ZFNat) := eNat.eq_symm_apply.mp <| eNat.mul_def a  b

@[zfnat_to_nat]
def transfer_div (a b : ZFNat) := eNat.eq_symm_apply.mp <| eNat.div_def a  b


@[zfnat_to_nat]
def transfer_ofNat (a : ℕ) : eNat a = a := eNat.right_inv a

@[zfnat_to_nat]
def transfer_eq (a b : ZFNat) : a = b ↔ eNat a = eNat b := eNat.apply_eq_iff_eq.symm

theorem succ_le_iff {a b : ZFNat} : a.succ ≤ b ↔ a < b := by
  enat
  exact Nat.succ_le_iff

instance : SuccOrder ZFNat where
  succ := succ
  le_succ := by enat; exact fun _ => Nat.le_succ _
  max_of_succ_le := by
    enat
    simp only [Nat.succ_eq_add_one, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero,
      IsEmpty.forall_iff, implies_true]
  succ_le_of_lt := by
    enat
    simp only [Nat.succ_eq_add_one]
    exact fun {a b} h ↦ Nat.succ_le_of_lt h


theorem zero_lt_succ {n : ZFNat} : 0 < n.succ := by
  enat
  set n := eNat n
  exact Nat.zero_lt_succ _

end ZFNat
end Naturals
end ZFSet
