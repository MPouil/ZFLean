/-
Copyright (c) 2025 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/
import Mathlib.CategoryTheory.Category.Basic

/-!
# Custom tactics for ZF

This file registers label attributes and defines the `zrel`, `zpfun`, `zfun`, and `zdom`
tactics used to discharge relation, partial-function, function, and domain-membership side
goals.
-/

register_label_attr zrel
register_label_attr zpfun
register_label_attr zfun
register_label_attr zdom

/-!
Thanks to Ghilain for the idea of registering specific attributes
-/
namespace ZFTactics
set_option hygiene false

-- `sorry_if_sorry` (Mathlib, `Mathlib/CategoryTheory/Category/Basic.lean`) closes the main goal
-- with `sorry` when the goal's type already *contains* a `sorry`, and fails otherwise. It is the
-- first branch of each `first | …` so that goals already poisoned by an upstream `sorry` are
-- discharged instantly instead of sending `solve_by_elim` on a hopeless search. In the released
-- 0-sorry artifact it never fires; it only matters while a development is in progress.

macro "zrel" : tactic => `(tactic|
  first
  | sorry_if_sorry
  | solve_by_elim using zrel, zpfun, zfun)

set_option hygiene false in
macro "zpfun" : tactic => `(tactic|
  first
  | sorry_if_sorry
  | solve_by_elim using zpfun, zfun)

set_option hygiene false in
macro "zfun" : tactic => `(tactic|
  first
  | sorry_if_sorry
  | solve_by_elim using zfun)

/-
`zdom` discharges the membership side conditions that show up at function-application sites:
`x ∈ f.Dom`, the `x ∈ A` and `(@ᶻf ⟨x, _⟩).val ∈ B` goals that feed them, and the
`pair`/`funs`/`powerset` membership goals of the same shape.

It searches with the `zdom` seed lemmas and falls back on the three function-shaped attribute
sets, because most `zdom` seeds carry an `IsFunc`/`IsPFunc`/`⊆ prod` hypothesis. Note that
`is_func_dom_eq` itself is an *equation*, hence invisible to `solve_by_elim`; the membership
bridge `mem_dom_of_mem` (`ZFLean/Functions.lean`) is what makes `x ∈ f.Dom` reachable.
-/
set_option hygiene false in
macro "zdom" : tactic => `(tactic|
  first
  | sorry_if_sorry
  | solve_by_elim using zdom, zfun, zpfun, zrel)
end ZFTactics
