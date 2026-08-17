/-
Copyright (c) 2026 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/
import ZFLean.Integers
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Order.Ring.Cast

/-! # Euclidean Division on ZFC Integers

This file equips `ZFInt` with both common integer-division conventions, transported along the
canonical ring equivalence from `ZFInt` to `ℤ`.

The higher-priority Euclidean-domain instance makes `/` and `%` use `Int.ediv` and `Int.emod`; for
`b ≠ 0`, its remainder satisfies `0 ≤ a % b < |b|`. Floor division remains available through the
explicitly named `fdiv` and `fmod` operations and through the lower-priority
`floorEuclideanDomain` instance.
-/

namespace ZFSet.ZFInt

universe u

noncomputable section

instance instNontrivial : Nontrivial ZFInt :=
  ⟨⟨1, 0, one_ne_zero⟩⟩

instance instCharZero : CharZero ZFInt :=
  AddMonoidWithOne.toCharZero

private theorem intCast_surjective : Function.Surjective (Int.cast : ℤ → ZFInt) := by
  intro z
  induction z using ZFInt.induction with
  | zero =>
      exact ⟨0, rfl⟩
  | pos z ih =>
      obtain ⟨n, rfl⟩ := ih
      exact ⟨n + 1, by rw [Int.cast_add, Int.cast_one]⟩
  | neg z ih =>
      obtain ⟨n, rfl⟩ := ih
      exact ⟨n - 1, by rw [Int.cast_sub, Int.cast_one]⟩

/-- The canonical ring equivalence between the quotient construction `ZFInt` and Lean's `ℤ`. -/
def equivInt : ZFInt ≃+* ℤ :=
  (RingEquiv.ofBijective (Int.castRingHom ZFInt)
    ⟨Int.cast_injective, intCast_surjective⟩).symm

@[simp]
theorem equivInt_intCast (z : ℤ) : equivInt (z : ZFInt) = z := by
  change equivInt (equivInt.symm z) = z
  exact equivInt.apply_symm_apply z

@[simp]
theorem intCast_equivInt (z : ZFInt) : ((equivInt z : ℤ) : ZFInt) = z := by
  change equivInt.symm (equivInt z) = z
  exact equivInt.symm_apply_apply z

theorem equivInt_le (a b : ZFInt) : equivInt a ≤ equivInt b ↔ a ≤ b := by
  constructor <;> intro h
  · have h' : ((equivInt a : ℤ) : ZFInt) ≤ ((equivInt b : ℤ) : ZFInt) :=
      Int.cast_mono h
    rwa [intCast_equivInt, intCast_equivInt] at h'
  · rwa [← intCast_equivInt a, ← intCast_equivInt b, Int.cast_le] at h

theorem equivInt_lt (a b : ZFInt) : equivInt a < equivInt b ↔ a < b := by
  rw [lt_iff_not_ge, lt_iff_not_ge, equivInt_le]

@[simp]
theorem equivInt_abs (z : ZFInt) : equivInt |z| = |equivInt z| := by
  rcases _root_.le_total 0 z with hz | hz
  · have hz' : (0 : ℤ) ≤ equivInt z := by
      rwa [←equivInt_le 0 z, map_zero] at hz
    rw [abs_of_nonneg hz, abs_of_nonneg hz']
  · have hz' : equivInt z ≤ (0 : ℤ) := by
      rwa [←equivInt_le z 0, map_zero] at hz
    rw [abs_of_nonpos hz, abs_of_nonpos hz', map_neg]

@[reducible] private def intFloorEuclideanDomain : EuclideanDomain ℤ :=
  { (inferInstance : CommRing ℤ), (inferInstance : Nontrivial ℤ) with
    quotient := Int.fdiv
    quotient_zero := Int.fdiv_zero
    remainder := Int.fmod
    quotient_mul_add_remainder_eq := Int.mul_fdiv_add_fmod
    r := fun a b ↦ a.natAbs < b.natAbs
    r_wellFounded := (measure Int.natAbs).wf
    remainder_lt := by
      intro a b hb
      rcases lt_or_gt_of_ne hb with hb | hb
      · have hbounds :=
          (Int.fdiv_fmod_unique' (a := a) (b := b) (r := a.fmod b) (q := a.fdiv b) hb).mp
            ⟨rfl, rfl⟩
        simpa only [Int.natAbs_neg] using
          Int.natAbs_lt_natAbs_of_nonneg_of_lt
            (Int.neg_nonneg_of_nonpos hbounds.2.2) (Int.neg_lt_neg hbounds.2.1)
      · exact Int.natAbs_lt_natAbs_of_nonneg_of_lt
          (Int.fmod_nonneg_of_pos a hb) (Int.fmod_lt_of_pos a hb)
    mul_left_not_lt := fun a b hb ↦
      not_lt_of_ge <| by
        rw [← Int.natAbs_pos] at hb
        grw [← Nat.mul_one a.natAbs, Int.natAbs_mul, Nat.mul_le_mul_left _ hb]
  }

/-- The floor-division Euclidean-domain structure on `ZFInt`. -/
@[reducible] def floorEuclideanDomain : EuclideanDomain ZFInt := by
  letI : EuclideanDomain ℤ := intFloorEuclideanDomain
  exact equivInt.euclideanDomain

/-- The nonnegative-remainder Euclidean-domain structure on `ZFInt`. -/
@[reducible] def edivEuclideanDomain : EuclideanDomain ZFInt :=
  equivInt.euclideanDomain

/-- The floor convention remains available as a lower-priority instance. -/
instance (priority := low) instFloorEuclideanDomain : EuclideanDomain ZFInt :=
  floorEuclideanDomain

/-- The `ediv` convention is the default convention used by `/` and `%`. -/
instance (priority := high) instEuclideanDomain : EuclideanDomain ZFInt :=
  edivEuclideanDomain

@[simp]
theorem equivInt_div (a b : ZFInt) : equivInt (a / b) = equivInt a / equivInt b :=
  equivInt.apply_symm_apply _

@[simp]
theorem equivInt_mod (a b : ZFInt) : equivInt (a % b) = equivInt a % equivInt b :=
  equivInt.apply_symm_apply _

theorem div_add_mod (a b : ZFInt) : b * (a / b) + a % b = a :=
  EuclideanDomain.div_add_mod a b

theorem mod_nonneg (a : ZFInt) {b : ZFInt} (hb : b ≠ 0) : 0 ≤ a % b := by
  apply (equivInt_le 0 (a % b)).mp
  rw [equivInt_mod, map_zero]
  apply Int.emod_nonneg
  intro hb'
  apply hb
  apply equivInt.injective
  rw [hb', map_zero]

theorem mod_lt_abs (a : ZFInt) {b : ZFInt} (hb : b ≠ 0) : a % b < |b| := by
  apply (equivInt_lt (a % b) |b|).mp
  rw [equivInt_mod, equivInt_abs]
  apply Int.emod_lt_abs
  intro hb'
  apply hb
  apply equivInt.injective
  rw [hb', map_zero]

@[simp]
theorem mod_eq_zero {a b : ZFInt} : a % b = 0 ↔ b ∣ a :=
  EuclideanDomain.mod_eq_zero

/-! ## Explicit Euclidean division -/

/-- Euclidean quotient with a nonnegative remainder. This is also the operation used by `/`. -/
def ediv (a b : ZFInt.{u}) : ZFInt.{u} :=
  equivInt.symm (equivInt a / equivInt b)

/-- Euclidean remainder in the interval `[0, |b|)` when `b ≠ 0`.
This is also the operation used by `%`. -/
def emod (a b : ZFInt.{u}) : ZFInt.{u} :=
  equivInt.symm (equivInt a % equivInt b)

@[simp]
theorem equivInt_ediv (a b : ZFInt) :
    equivInt (ediv a b) = equivInt a / equivInt b :=
  equivInt.apply_symm_apply _

@[simp]
theorem equivInt_emod (a b : ZFInt) :
    equivInt (emod a b) = equivInt a % equivInt b :=
  equivInt.apply_symm_apply _

@[simp]
theorem ediv_eq_div (a b : ZFInt) : ediv a b = a / b := by
  apply equivInt.injective
  rw [equivInt_ediv, equivInt_div]

@[simp]
theorem emod_eq_mod (a b : ZFInt) : emod a b = a % b := by
  apply equivInt.injective
  rw [equivInt_emod, equivInt_mod]

theorem ediv_add_emod (a b : ZFInt) : b * ediv a b + emod a b = a := by
  erw [div_add_mod a b]

theorem emod_nonneg (a : ZFInt) {b : ZFInt} (hb : b ≠ 0) : 0 ≤ emod a b := by
  apply (equivInt_le 0 (emod a b)).mp
  rw [equivInt_emod, map_zero]
  apply Int.emod_nonneg
  intro hb'
  apply hb
  apply equivInt.injective
  rw [hb', map_zero]

theorem emod_lt_abs (a : ZFInt) {b : ZFInt} (hb : b ≠ 0) : emod a b < |b| := by
  apply (equivInt_lt (emod a b) |b|).mp
  rw [equivInt_emod, equivInt_abs]
  apply Int.emod_lt_abs
  intro hb'
  apply hb
  apply equivInt.injective
  rw [hb', map_zero]

@[simp]
theorem emod_eq_zero {a b : ZFInt} : emod a b = 0 ↔ b ∣ a := by
  constructor <;> intro h
  · apply (map_dvd_iff equivInt).mp
    rw [Int.dvd_iff_emod_eq_zero, ←equivInt_emod, h, map_zero]
  · apply equivInt.injective
    rwa [equivInt_emod, map_zero, ← Int.dvd_iff_emod_eq_zero, map_dvd_iff equivInt]

/-! ## Explicit floor division -/

/-- Floor quotient: the quotient of `a` by `b`, rounded toward negative infinity. -/
def fdiv (a b : ZFInt.{u}) : ZFInt.{u} :=
  equivInt.symm ((equivInt a).fdiv (equivInt b))

/-- Floor remainder. For a nonzero divisor, it has the sign of the divisor. -/
def fmod (a b : ZFInt.{u}) : ZFInt.{u} :=
  equivInt.symm ((equivInt a).fmod (equivInt b))

@[simp]
theorem equivInt_fdiv (a b : ZFInt) :
    equivInt (fdiv a b) = (equivInt a).fdiv (equivInt b) :=
  equivInt.apply_symm_apply _

@[simp]
theorem equivInt_fmod (a b : ZFInt) :
    equivInt (fmod a b) = (equivInt a).fmod (equivInt b) :=
  equivInt.apply_symm_apply _

theorem fdiv_add_fmod (a b : ZFInt) : b * fdiv a b + fmod a b = a := by
  apply equivInt.injective
  simp only [map_add, map_mul, equivInt_fdiv, equivInt_fmod]
  apply Int.mul_fdiv_add_fmod

theorem fmod_nonneg_of_pos (a : ZFInt) {b : ZFInt} (hb : 0 < b) : 0 ≤ fmod a b := by
  apply (equivInt_le 0 (fmod a b)).mp
  rw [equivInt_fmod, map_zero]
  apply Int.fmod_nonneg_of_pos
  rwa [←equivInt_lt 0 b, map_zero] at hb

theorem fmod_lt_of_pos (a : ZFInt) {b : ZFInt} (hb : 0 < b) : fmod a b < b := by
  apply (equivInt_lt (fmod a b) b).mp
  rw [equivInt_fmod]
  apply Int.fmod_lt_of_pos
  rwa [←equivInt_lt 0 b, map_zero] at hb

theorem fmod_nonpos_of_neg (a : ZFInt) {b : ZFInt} (hb : b < 0) : fmod a b ≤ 0 := by
  apply (equivInt_le (fmod a b) 0).mp
  rw [equivInt_fmod, map_zero]
  have hb' : equivInt b < (0 : ℤ) := by
    rwa [← equivInt_lt b 0, map_zero] at hb
  exact ((Int.fdiv_fmod_unique' hb').mp ⟨rfl, rfl⟩).2.2

theorem lt_fmod_of_neg (a : ZFInt) {b : ZFInt} (hb : b < 0) : b < fmod a b := by
  apply (equivInt_lt b (fmod a b)).mp
  rw [equivInt_fmod]
  have hb' : equivInt b < (0 : ℤ) := by
    rwa [← equivInt_lt b 0, map_zero] at hb
  exact ((Int.fdiv_fmod_unique' hb').mp ⟨rfl, rfl⟩).2.1

@[simp]
theorem fmod_eq_zero {a b : ZFInt} : fmod a b = 0 ↔ b ∣ a := by
  calc
    fmod a b = 0 ↔ equivInt (fmod a b) = equivInt 0 := equivInt.injective.eq_iff.symm
    _ ↔ (equivInt a).fmod (equivInt b) = 0 := by rw [equivInt_fmod, map_zero]
    _ ↔ equivInt b ∣ equivInt a := Int.dvd_iff_fmod_eq_zero.symm
    _ ↔ b ∣ a := map_dvd_iff equivInt

end

end ZFSet.ZFInt
