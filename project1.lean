import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic
import CmuItp24.Autograde

set_option pp.rawOnError true
set_option linter.unusedTactic false

/-
Project 2 for 21-321 Interactive Theorem Proving
Authors: David Lessure and Zachary Gelman
-/

/-
For the problem that we are trying to prove, we will use this
definition of the factorial function fac n = n! and
the theorem fac_pos : 0 < fac n from Assignment 7.
-/

open Nat
open Finset

variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)
#check Finset.prod s f


def fac : ℕ → ℕ
  | 0     => 1
  | n + 1 => (n + 1) * fac n

theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  . simp [fac]
  simp [fac, ih]

example (n : ℕ) : fac n - 1 + 1 = fac n := by
  have := fac_pos n
  omega


/-
The problem for this project is a modified version from the 2002-2003 British
Mathematical Olympiad. Prove that the equation a! * b! = a! + b! + c! has the
unique solution a = b = 3, c = 4 for a, b, c in ℕ. This is equivalent to saying
Prove that fac a * fac b = fac a + fac b + fac c iff (a = 3 ∧ b = 3 ∧ c = 4).
We chose to formalize this popular problem in number theory based on a YouTube
video by Presh Talwalker (AKA MindYoueDecisions), titled: "Solving the hardest
question of a British Mathematical Olympiad". The link for this is below.
Source: https://youtu.be/9dyK_op-Ocw?si=g71KnjUSMggfQ0bO
-/

theorem factorial_eqn_abc {a b c : ℕ} : fac a * fac b = fac a + fac b + fac c
↔ (a = 3 ∧ b = 3 ∧ c = 4) := by
  sorry

/-
The general outline for this proof is below.
If (a, b, c) is a solution, then (b, a, c) is a solution by commutativity.
If a solution exists, then a solution (a, b, c) with a ≤ b exists.
Without any loss of generality (WLOG), suppose that a ≤ b.
This will be proven in 6 steps.
First, Prove that 3 ≤ a.
Second, Prove that b < c.
Third, Prove that a = b.
Fourth, Prove that c ≤ a + 2.
Fifth, Prove that c = a + 1.
Final, Show that a=3, b=3, c=4.
-/


/-
Here we have formalized some basic lemmas about factorials that might be useful in
answering this problem. With help from your feedback we will polish and complete
this proof.
-/


lemma fac_mono {n : ℕ} (h : 0 < n) : fac (n) < fac (n+1) := by
  simp [fac]
  refine (lt_mul_iff_one_lt_left ?hb).mpr ?_
  apply fac_pos
  exact Nat.lt_add_of_pos_left h

lemma fac_d {n m : ℕ} (h : n < m) (h1 : 0 < n) : fac n < fac m := by
  induction m with
  | zero =>
    trivial

  | succ m ih =>
    by_cases nltm : n < m
    case pos =>
      have : fac m < fac (m+1) := by
        apply fac_mono
        exact zero_lt_of_lt nltm
      exact lt_trans (ih nltm) this

    case neg =>
      have : n = m := by
        exact Nat.eq_of_lt_succ_of_not_lt h nltm
      rw [← this]
      apply fac_mono
      apply h1

lemma fac_monotone : ∀ {n m : ℕ}, n ≤ m → fac n ≤ fac m := by
  intros n m h
  induction' h with m _ ih
  case refl =>
    rfl

  case step =>
    calc fac n ≤ fac m := ih
      _ ≤ (m + 1) * fac m := by
        refine Nat.le_mul_of_pos_left (fac m) ?h
        apply succ_pos

lemma fac_diff_monotone {n m : ℕ} (h : n < m) : --by is below
fac (n+1) - fac n < fac (m+1) - fac m := by
  simp [fac]
  have (n : ℕ) : (n+1) * fac n - fac n = n * fac n := by
    refine (Nat.sub_eq_iff_eq_add ?h).mpr ?_
    refine Nat.le_mul_of_pos_left (fac n) ?h.h
    exact zero_lt_succ n
    exact succ_mul n (fac n)

  rw [this n]
  rw [this m]
  refine Nat.mul_lt_mul_of_lt_of_le' h ?hbd ?hb
  apply fac_monotone
  exact le_of_succ_le h
  apply fac_pos

lemma fac_dvd_fac {a b : ℕ} (alb : a < b) : fac a ∣ fac b := by
  induction' b with b ih
  exfalso
  exact not_lt_zero a alb

  cases lt_or_eq_of_le (le_of_succ_le_succ alb) with
    | inl h' =>
      exact dvd_mul_of_dvd_right (ih h') (b + 1)

    | inr rfl =>
      simp [fac]
      rw [← rfl]
      exact dvd_mul_left (fac a) (a + 1)




example {m n : ℕ} (h : m ≤ n) : (m)! ≤ (n)! := by
  exact factorial_le h
example {m n : ℕ} (h : m ≤ n) : m.factorial ≤ n.factorial := by
  exact factorial_le h


lemma no_factorial_difference_of_two' {b c : ℕ} : b ! ≠ 2 + c ! := by
  rcases le_or_gt b c with h | h
  . have : b ! ≤ c ! := factorial_le h
    linarith

  cases' b with b
  . norm_num
    omega
  cases' b with b
  . norm_num
    omega
  cases' b with b
  . have : 0 < c ! := factorial_pos c
    norm_num
    omega

  rw [factorial_succ, add_mul, one_mul, add_comm]
  apply Nat.ne_of_gt
  apply add_lt_add_of_le_of_lt
  apply factorial_le (m := 2)
  omega

  have : c ! ≤ (b + 2)! := by
    apply factorial_le
    omega
  apply lt_of_le_of_lt this
  rw [lt_mul_iff_one_lt_left]
  omega
  exact factorial_pos (b + 2)

lemma eq_fac_factorial : ∀ n, fac n = (n)! := by
  intros n
  induction n with
    | zero => rfl
    | succ n ih => simp [fac, factorial_succ, ih]


/-
First, Prove that 3 ≤ a.
To prove that 3 ≤ a, suppose that a ≤ b
Suppose that a = 0,1. Then a! = 1. Then by subbing into a! * b! = a! + b! + c!
we get b! = 1 + b! + c! which is equivalent to 0 = 1 + c! This is a
contradiction since 1 + c! is > 0. Therefore a cannot be 0,1.
If a = 2, then a! = 2. subbing into a! * b! = a! + b! + c! we get b! = 2 + c!
This is a contradiction since factorials go in sequence 1, 2, 6, 24, ... so no
factorial is 2 greater than another factorial is a contradiction.
Therefore a cannot be 2. This means that a has to at least be 3. This gives us
the inequality 3 ≤ a ≤ b.
-/

lemma no_factorial_difference_of_two {b c : ℕ} : fac b ≠ 2 + fac c := by
  rw [eq_fac_factorial b, eq_fac_factorial c]
  exact no_factorial_difference_of_two'

theorem step1_age3 {a b c : ℕ} (h : fac a * fac b = fac a + fac b + fac c)
 : a ≥ 3 := by
  -- WLOG, suppose a ≤ b

  cases a with
  | zero =>
    -- a = 0, thus fac 0 = 1, so 1 * fac b = 1 + fac b + fac c
    have : fac b = fac b + 1 + fac c := by
      simp [fac] at h
      linarith
    linarith

  | succ a =>
    cases a with
    | zero =>
      -- a = 1, thus fac 1 = 1, so 1 * fac b = 1 + fac b + fac c
      have : fac b = fac b + 1 + fac c := by
        simp [fac] at h
        linarith
      linarith

    | succ a =>
      cases a with
      | zero =>
        -- a = 2, thus fac 2 = 2, so 2 * fac b = 2 + fac b + fac c
        have : fac b = 2 + fac c := by
          simp [fac] at h
          linarith
        exfalso
        apply no_factorial_difference_of_two this

      | succ a =>
        --We have 3 ≤ a
        linarith


/-
Second, Prove that b < c.
To prove that b < c, Assume for the sake of contradiction (AFSOC)that b ≥ c.
Then we can upper bound a! + b! + c! ≤ b! + b! + b! = 3b! since 3 ≤ a ≤ b and
(we assumed) that b ≥ c. But we can find a lower bound a! + b! + c! = a! * b!
≥ 3!b! = 6b! since 3 ≤ a ≤ b but this means that the lower bound is more than
the upper bound. This is a contradiction. Our only assumption that b ≥ c
must have been wrong, thus b < c. This gives us the inequality 3 ≤ a ≤ b < c.
-/

theorem step2_bltc {a b c : ℕ} (h : fac a * fac b = fac a + fac b + fac c)
  (aleb : a ≤ b) : b < c := by
  -- AFSOC, that b ≥ c.
  by_contra h_not_lt
  have hbc : c ≤ b := le_of_not_lt h_not_lt

  have ub : fac a + fac b + fac c ≤ 3 * fac b := by
    calc
      fac a + fac b + fac c ≤ fac b + fac b + fac b := by
        apply Nat.add_le_add (Nat.add_le_add (fac_monotone aleb)
        (fac_monotone (le_refl b))) (fac_monotone hbc)
      _ = 3 * fac b := by ring

  have lb : fac a * fac b ≥ 6 * fac b := by
    have ha : 3 ≤ a := step1_age3 h
    calc
      fac a * fac b ≥ fac 3 * fac b := by
        apply mul_le_mul_right (fac b) (fac_monotone ha)
      _ = 6 * fac b := by
        have : fac 3 = 6 := by simp [fac]
        rw [this]

  have contra : 6 * fac b ≤ 3 * fac b := by
    calc
      6 * fac b ≤ fac a * fac b := lb
      _ = fac a + fac b + fac c := by rw [h]
      _ ≤ 3 * fac b := ub

  -- WTS that the lower bound being more than the upper bound is a contradiction
  have : 6 * fac b ≤ 3 * fac b := contra
  have : 6 ≤ 3 := le_of_mul_le_mul_right this (fac_pos b)
  have : 6 > 3 := lt_of_succ_lt_succ (by norm_num)
  contradiction


/-
Third, Prove that a = b.
To prove that a = b, AFSOC that a ≠ b which means 3 ≤ a < b < c.
Starting with a! * b! = a! + b! + c! divide both sides by a! to get
b! = 1 + (b! / a!) + (c! / a!) So b! will be the sum of 3 integers since we
assumed b and c are greater than a. Since 3 ≤ b, 2 divides b!. This means that
2 must divide the entire right hand side. Since 3 ≤ a < b < c, b ≥ a + 1, and
c ≥ a + 2. From this, it must be that (a + 2)(a + 1) is an even factor of
(c! / a!) since the product of 2 consecutive numbers is an even number. This
means that 2 divides (c! / a!). For the RHS 1 + (b! / a!) + (c! / a!) to be an
even number, then 1 + (b! / a!) must be even. This implies that (b! / a!) is
odd. Since b > a, then b = a + 1. If a + 2 ≤ b, then (b! / a!) would have an
even factor (a + 2)(a + 1) which is not possible since (b! / a!) is odd.
Since b = a + 1, we have b! = 1 + (b! / a!) + (c! / a!) =
(a + 1)! = 1 + ((a + 1)! / a!) + (c! / a!) = (a + 1)! = 1 + (a + 1) + (c! / a!).
From this obviously (a + 1) divides (a + 1)! on the left hand side (LHS) and
(a + 1) divides (a + 1) on the RHS. Also, (a + 1) divides (c! / a!) since
(a + 2)(a + 1) is a factor of (c! / a!) and c ≥ a + 2. Therefore (a + 1) must
also divide 1, but this is only possible when a = 0, but this is a contradiction
since 3 ≤ a. Our assumption that a ≠ b is wrong, thus a = b. This gives us the
inequality 3 ≤ a = b < c.
-/

def p1 (x: ℕ) := x + 1

lemma facprod1 (a : ℕ): fac a = Finset.prod (Finset.range (a)) p1 := by
  induction a with
  | zero =>
    trivial

  | succ a ih =>
    induction a with
    | zero =>
      trivial

    | succ a' _ =>
      have : fac ((a' + 1) + 1) = ((a' + 1) + 1) * fac (a' + 1) := by
        exact rfl
      rw [this]

      have : (range (a' + 1 + 1)).prod p1 = ((range (a' + 1)).prod p1) * (a' + 1 + 1) := by
        exact prod_range_succ p1 (a' + 1)
      rw [this]
      rw [ih]
      exact Nat.mul_comm (a' + 1 + 1) ((range (a' + 1)).prod p1)

lemma facprod3 (n b: ℕ) (ng0 : n > 0) (nr : n ∈ Finset.range b)
: n ∣ Finset.prod (Finset.range b) p1 := by
  have nlb : n < b := by
    exact List.mem_range.mp nr
  rw [← facprod1]

  have h1: n ∣ fac n := by
    induction' n with n _
    . trivial
    . simp [fac]

  have h2: fac n ∣ fac b := by
    exact fac_dvd_fac nlb
  exact Nat.dvd_trans h1 h2

lemma facprod4 (n b: ℕ) (nr : n ≤ b):
(Finset.prod (Finset.range n) p1) ∣ Finset.prod (Finset.range b) p1 := by
  refine prod_dvd_prod_of_subset (range n) (range b) p1 ?h
  exact GCongr.finset_range_subset_of_le nr

theorem step3_aeqb {a b c : ℕ} (h : fac a * fac b = fac a + fac b + fac c)
  (aleb : a ≤ b) (bltc : b < c) (age3 : a ≥ 3): a = b := by
  -- AFSOC, assume a ≠ b, i.e., a < b
  by_contra h_neq
  have altb : a < b := lt_of_le_of_ne aleb h_neq
  have ap2lec : a + 2 ≤ c := by
    have ap1leb : a + 1 ≤ b := add_one_le_iff.mp altb
    refine succ_le_of_lt ?h
    apply lt_of_lt_of_le' bltc ap1leb

  -- Divide both sides of the equation by fac a
  have h_div : fac b = 1 + fac b / fac a + fac c / fac a := by
    have fac_a_pos : 0 < fac a := fac_pos a
    have : fac a * fac b / fac a = fac b := Nat.mul_div_cancel_left (fac b) fac_a_pos
    rw [← mul_add_div fac_a_pos (1 + fac b / fac a) (fac c)]
    rw [left_distrib, mul_one, Nat.mul_div_cancel']
    rw [← h, this]
    apply fac_dvd_fac altb

  -- We now derive a contradiction since 1 + (fac b / fac a) + (fac c / fac a) is even
  -- but the RHS would have to be odd from the above analysis.
  have fac_b_even : fac b % 2 = 0 := by
    have twoltb : 2 < b := by
      linarith

    have : fac 2 = 2 := by
      simp [fac]
    rw [← this]
    apply mod_eq_zero_of_dvd
    apply fac_dvd_fac twoltb

  have even_sum : (1 + fac b / fac a + fac c / fac a) % 2 = 0 := by
    rw [← fac_b_even]
    rw [← h_div]

  have even_ap1ap2 : Even ((a + 1) * (a + 2)) := by
    cases even_or_odd (a+1) with
      | inl h' =>
        apply Even.mul_right h'

      | inr h'' =>
        have : Even (a+2) := by
          rw [← one_add_one_eq_two,← add_assoc]
          apply Odd.add_odd h''
          exact odd_one
        rw [mul_comm]
        apply Even.mul_right this

  rcases le.dest ap2lec with ⟨d, hd⟩
  have cfact : (a + 2) * (a + 1) ∣ (fac c / fac a):= by
  -- This is True since we have ap2lec : a + 2 ≤ c
    rw [facprod1]
    rw [facprod1]
    apply Nat.dvd_div_of_mul_dvd

    have a1d: (range a).prod p1 * (a + 1)= (range (a+1)).prod p1 := by
      exact Eq.symm (prod_range_succ p1 a)
    have a2d: (range (a +1)).prod p1 * (a + 2)= (range (a+2)).prod p1 := by
      exact Eq.symm (prod_range_succ p1 (a + 1))
    have a3d : (range a).prod p1 * (a + 1) * (a + 2) = (range (a + 2)).prod p1 := by
      rw [a1d]
      rw [a2d]

    have : (range a).prod p1 * (a + 1) * (a + 2) = (range a).prod p1 * ((a + 2) * (a + 1)) := by
      ring

    rw [← this]
    rw [a3d]
    refine facprod4 (a + 2) ?h.nr ?h.nlb
    exact ap2lec

  have twodvdfcdfa : 2 ∣ (fac c / fac a) := by
    cases even_or_odd a with
    | inl ha =>
      exact dvd_trans (Dvd.dvd.mul_right
        (Nat.dvd_add_self_right.mpr (even_iff_two_dvd.mp ha)) (a + 1)) cfact

    | inr hb =>
      exact dvd_trans (Dvd.dvd.mul_left
        (even_iff_two_dvd.mp (Odd.add_odd hb odd_one)) (a + 2)) cfact

  have onebfact : (fac b / fac a) % 2 = 1 := by
    omega

  have ap1eqb : a + 1 = b := by
    by_contra
    have ind_bit {i : ℕ } : Even ((fac (a + 2 + i)) / fac (a)) := by
      induction i with

      | zero =>
        simp [fac]
        have h1: (a + 1 + 1) * ((a + 1)* fac a) = (a + 2) * (a + 1) * fac a := by
          linarith
        rw [h1]

        have h2: (a + 2) * (a + 1) * fac a / fac a = (a + 2) * (a + 1) * (fac a / fac a) := by
          refine Nat.mul_div_assoc ((a + 2) * (a + 1)) ?_
          exact Nat.dvd_refl (fac a)
        rw [h2]

        have h3: fac a / fac a = 1 := by
          refine Nat.div_self (fac_pos a)
        rw [h3]
        simp
        refine even_mul.mpr ?zero.a
        exact Or.symm ((fun {m n} ↦ even_mul.mp) even_ap1ap2)

      | succ i' ih =>
      simp [fac]
      have : ((a + 2 + i' + 1) * fac (a + 2 + i') / fac a) = (a + 2 + i' + 1) * (fac (a + 2 + i') / fac a) := by
        refine Nat.mul_div_assoc (a + 2 + i' + 1) ?_
        apply fac_dvd_fac
        omega
      rw [this]
      exact Even.mul_left ih (a + 2 + i' + 1)

    have ap2leqb : a + 2 < b ∨ a + 2 = b := by
      omega

    have beven : Even (fac b / fac a) := by
      have h2: ∃ i, a + 2 + i = b := by
        refine le.dest ?_
        omega
      have h3: ∃ i, fac (a + 2 + i) = fac b := by
        exact Exists.imp (fun a_1 ↦ congrArg fac) h2
      obtain ⟨i, h4⟩ := h3
      rw [← h4]
      apply ind_bit

    have : (fac b / fac a) % 2 = 0 := by
      exact even_iff.mp beven
    have : 0 = 1 := by
      rw [← this]
      rw [onebfact]
    trivial

  have : fac b / fac a  = a + 1 := by
    rw [← ap1eqb]
    simp [fac]
    refine Nat.div_eq_of_eq_mul_left ?H1 rfl
    apply fac_pos

  have : fac (a+1) = 1 + (a + 1) + (fac c) / (fac a) := by
    nth_rewrite 2 [← this]
    rw [ap1eqb]
    trivial

  have ap1divfap1 : (a + 1) ∣ fac (a + 1) := by
    simp [fac]
  have ap1divfc_fa : (a+1) ∣ (fac c / fac a) := by
    exact dvd_of_mul_left_dvd cfact
  have ap1divap1 : (a + 1) ∣ (a + 1) := by
    exact dvd_refl (a + 1)

  have ap1divall : (a + 1) ∣ 1 + (a + 1) + fac c / fac a := by
    exact
      (ModEq.dvd_iff (congrFun (congrArg HMod.hMod this) (fac (a + 1))) ap1divfap1).mp
        ap1divfap1
  have ap1div1: (a + 1) ∣ 1 := by
    have : (a + 1) ∣ 1 + (a + 1) := by
      exact (Nat.dvd_add_iff_left ap1divfc_fa).mpr ap1divall
    exact (Nat.dvd_add_iff_left ap1divap1).mpr this

  have : a + 1 ≤ 1 := by
    apply le_of_dvd
    trivial
    exact ap1div1

  have : a = 0 := by
    exact lt_one_iff.mp this
  have : 0 ≥ 3 := by
    rw [← this]
    exact age3
  contradiction


/-
Fourth, Prove that c ≤ a + 2.
To prove that c ≤ a + 2, again take a! * b! = a! + b! + c! divide both sides
by a! to get b! = 1 + (b! / a!) + (c! / a!). Subbing a = b gives us the equation
a! = 1 + (a! / a!) + (c! / a!) simplifies to a! = 1 + 1 + (c! / a!) which
simplifies to a! = 2 + (c! / a!) which equals a! - 2 =  (c! / a!). We know that
3 divides a! since 3 ≤ a. But 3 does not divide a! - 2, so also 3 does not
divide (c! / a!). If c ≥ a + 3, then (c! / a!) would have a factor of
(a + 3)(a + 2)(a + 1). But 3 would divide this product since one of the three
consecutive numbers must be a multiple of 3. Therefore, c ≤ a + 2.
-/

lemma divthing (a b : ℕ) : a ∣ a * b := by
  exact Nat.dvd_mul_right a b

theorem step4_cleap2 {a b c : ℕ} (h : fac a * fac b = fac a + fac b + fac c)
  (age3 : 3 ≤ a) (aleb : a ≤ b) (bltc : b < c) (aeqb : a= b): c ≤ a + 2 := by
  -- Substitute b = a
  rw [←aeqb] at h
  have h3 : (fac a * fac a) / fac a = fac a := by
    refine mul_div_left (fac a) ?H
    apply fac_pos

  have h4 : fac a + fac a = 2 * fac a := by
    exact Eq.symm (two_mul (fac a))

  have h6 : (2 * fac a + fac c) / (fac a) = 2 * fac a / fac a + fac c / fac a := by
    refine Nat.add_div_of_dvd_left ?hca
    apply fac_dvd_fac
    exact lt_of_le_of_lt aleb bltc

  have h7 : 2 * fac a / fac a + fac c / fac a = 2 + fac c / fac a := by
    refine add_right_cancel_iff.mpr ?_
    refine Nat.mul_div_cancel 2 (fac_pos a)

  have h8 : fac a = 2 + fac c / fac a := by
    nth_rewrite 1 [← h3]
    rw [← h7]
    rw [← h6]
    rw [← h4]
    exact congrFun (congrArg HDiv.hDiv h) (fac a)
  have h10 : fac a - 2 = fac c / fac a := by
    exact Nat.sub_eq_of_eq_add' h8

  have threedivfa : 3 ∣ fac a := by
    have f3dfa: fac 3 ∣ fac a := by
      by_cases ih : 3 = a
      case pos =>
        rw [ih]

      case neg =>
        apply fac_dvd_fac
        exact lt_of_le_of_ne age3 ih

    have : 3 ∣ fac 3 := by
      trivial
    exact dvd_trans this f3dfa

  have not3divfam2: ¬ (3 ∣ fac a - 2) := by
    by_contra ih
    have : 3 ∣ fac a + 1 := by
      omega

    have : 3 ∣ fac a + 1 - fac a := by
      apply Nat.dvd_sub
      exact le_add_right (fac a) 1
      apply this
      apply threedivfa

    have : 3 = 1 := by
      omega
    contradiction

  have not3divfcdfa: ¬ (3 ∣ fac c / fac a) := by
    rw [← h10]
    apply not3divfam2

  have ap3gc: a + 3 > c := by
    by_contra h11
    have h12 : a + 3 ≤ c := by
      exact le_of_not_lt h11

    have : fac (a + 3) ≤ fac c := by
      apply fac_monotone
      apply h12

    have h13 : (a + 1) ∣ fac c / fac a := by
      rw [facprod1]
      rw [facprod1]
      apply Nat.dvd_div_of_mul_dvd

      have a1d: (range a).prod p1 * (a + 1) = (range (a + 1)).prod p1 := by
        exact Eq.symm (prod_range_succ p1 a)
      rw [a1d]
      refine facprod4 (a + 1) ?h.nr ?h.nlb
      exact add_le_of_add_le_right bltc aleb

    have h14 : (a + 2) ∣ fac c / fac a := by
      rw [facprod1]
      rw [facprod1]
      apply Nat.dvd_div_of_mul_dvd

      have x: (range a).prod p1 * (a + 1) * (a + 2) ∣ (range c).prod p1 := by
        have a1d: (range a).prod p1 * (a + 1)= (range (a + 1)).prod p1 := by
          exact Eq.symm (prod_range_succ p1 a)
        have a2d: (range (a + 1)).prod p1 * (a + 2) = (range (a + 2)).prod p1 := by
          exact Eq.symm (prod_range_succ p1 (a + 1))
        have a3d : (range a).prod p1 * (a + 1) * (a + 2) = (range (a + 2)).prod p1 := by
          rw [a1d]
          rw [a2d]
        rw [a3d]
        refine facprod4 (a + 2) c ?nr
        exact le_of_succ_le h12

      have y: (range a).prod p1 * (a + 2) ∣ (range a).prod p1 * (a + 1) * (a + 2) := by
        refine Nat.mul_dvd_mul ?_ ?_
        exact Nat.dvd_mul_right ((range a).prod p1) (a + 1)
        rfl
      exact Nat.dvd_trans y x

    have h15 : (a + 3) ∣ fac c / fac a := by
      rw [facprod1]
      rw [facprod1]
      apply Nat.dvd_div_of_mul_dvd

      have x: (range a).prod p1 * (a + 1) * (a + 2) * (a + 3)∣ (range c).prod p1 := by
        have a1d: (range a).prod p1 * (a + 1)= (range (a + 1)).prod p1 := by
          exact Eq.symm (prod_range_succ p1 a)
        have a2d: (range (a + 1)).prod p1 * (a + 2)= (range (a + 2)).prod p1 := by
          exact Eq.symm (prod_range_succ p1 (a + 1))
        have amd: (range (a + 2)).prod p1 * (a + 3)= (range (a + 3)).prod p1 := by
          exact Eq.symm (prod_range_succ p1 (a + 2))
        have a3d : (range a).prod p1 * (a + 1) * (a + 2) * (a + 3)= (range (a + 3)).prod p1 := by
          rw [a1d]
          rw [a2d]
          rw [amd]
        rw [a3d]
        exact facprod4 (a + 3) c h12

      have y: (range a).prod p1 * (a + 3) ∣ (range a).prod p1 * (a + 1) * (a + 2) * (a + 3) := by
        refine Nat.mul_dvd_mul ?_ ?_
        have z : ((range a).prod p1) * (a + 1) * (a + 2) = ((range a).prod p1) * ((a + 1) * (a + 2)) := by
          exact Nat.mul_assoc ((range a).prod p1) (a + 1) (a + 2)
        rw [z]
        exact divthing ((range a).prod p1) ((a + 1) * (a + 2))
        exact Nat.dvd_refl (a + 3)
      exact Nat.dvd_trans y x

    have div_cases : (3 ∣ a) ∨ (3 ∣ a + 1) ∨ (3 ∣ a + 2) := by
      omega

    cases div_cases with
    | inl ha =>
      have : 3 ∣ a + 3 := by
        omega
      have : 3 ∣ fac c / fac a := by
        exact dvd_trans this h15
      contradiction

    | inr hb =>
      cases hb with
      | inl hb =>
        have : 3 ∣ fac c / fac a := by
          exact dvd_trans hb h13
        contradiction

      | inr hc =>
        have : 3 ∣ fac c / fac a := by
          exact dvd_trans hc h14
        contradiction
  omega


/-Fifth prove that c=a+1.
Suppose that c = a + 2. Then a! - 2 =  (c! / a!) is equivalent to
a! - 2 =  ((a + 2)! / a!) which simplifies to a! - 2 = (a + 2)(a + 1). This is
equivalent to a! - 2 = a^2 + 3a + 2 is equivalent to a! -(a^2) - 3a = 4. Clearly
the LHS is divisible by a. This means that 4 must be divisible by a. Since 3 ≤ a,
then a = 4. So we would have a = b, c = a + 2 which means that a = b = 4, c = 6.
This gives us a potential solution (a, b, c) = (4, 4, 6). However, when plugged
into a! * b! = a! + b! + c!, 4! * 4! ≠ 4! + 4! + 6! simplifies to 524 ≠ 768.
So we need to consider the other case of c ≤ a + 2, that is c = a + 1.
-/

theorem step5_ceqap1 {a b c : ℕ} (h : fac a * fac b = fac a + fac b + fac c)
(h2 : fac a - 2 = fac c / fac a) (age3 : a ≥ 3) (aeqb : a = b)
  (bltc : b < c) (cleap2 : c ≤ a + 2): c = a + 1 := by

  by_cases ih : c = a + 2
  case pos =>
    exfalso
    have h4 : fac (a + 2) / fac a = (a + 2) * (a + 1) := by
      simp [fac]
      refine Nat.div_eq_of_eq_mul_left ?H1 ?H2
      apply fac_pos
      ring_nf

    have _ : fac a - 2 = (a + 2) * (a + 1) := by
      rw [← h4]
      rw [← ih]
      apply h2

    have _: a^2 + 3*a + 2 = (a + 2) * (a + 1) := by
      ring
    have h7: (fac a) - a^2 - 3*a = 4 := by
      omega

    have : a ∣ fac a - a^2 - 3*a := by
      have adfa: a ∣ fac a := by
        induction' a with a _
        . trivial
        . simp [fac]
      refine dvd_sub' ?h₁ ?h₂
      exact dvd_sub' adfa (Dvd.intro_left (a.pow 1) rfl)
      exact dvd_mul_left a 3

    have : a ≤ 4 := by
      apply Nat.le_of_dvd
      trivial
      rw [← h7]
      exact this
    interval_cases a <;> contradiction

  case neg =>
    omega

/- Finally, we show that a=3, b=3, c=4.
In this case, c = a+1. Note that a! - 2 =  (c! / a!) is equivalent to a! - 2 =
((a + 1)! / a!) which simplifies to a! - 2 = a + 1 and is equivalent to a! - a = 3.
Clearly the LHS is divisible by a. This means that a divides 3, and since 3 ≤ a,
then a = 3. This gives us a potential solution (a, b, c) = (3, 3, 4). This time
when plugged into a! * b! = a! + b! + c!, 3! * 3! = 3! + 3! + 4! is equivalent
to 36 = 36 which is True. Therefore, we have determined the unique solution to
this problem is (a, b, c) = (3, 3, 4).
-/

theorem aeq_beq3_ceq4 {a b c : ℕ} (age3 : 3 ≤ a) (aeqb : a = b) (_ : b < c)
 (ceqap1 : c = a + 1) (h : fac a - 2 = fac c / fac a): a = 3 ∧ b = 3 ∧ c = 4 := by
  rw [ceqap1]
  rw [←aeqb]

  have aeq3 : a = 3 := by
    have h1: fac a - 2 = fac (a + 1) / fac a := by
      rw [← ceqap1]
      exact h

    have : fac (a + 1) / fac a = a + 1 := by
      simp [fac]
      refine mul_div_left (a + 1) ?H
      apply fac_pos

    have : fac a - 2 = a + 1 := by
      rw [← this]
      exact h1

    have h2: fac a - a = 3 := by
      omega

    have : a ∣ fac a - a := by
      have adfa: a ∣ fac a := by
        induction' a with a _
        . trivial
        . simp [fac]
      refine dvd_sub' ?h₁ ?h₂
      apply adfa
      exact dvd_refl a

    have : a ∣ 3 := by
      exact (ModEq.dvd_iff (congrFun (congrArg HMod.hMod h2) (fac a - a)) this).mp this

    have ale3 : a ≤ 3 := by
      apply le_of_dvd
      tauto
      exact this
    exact le_antisymm ale3 age3

  have : a+1 = 4 → a = 3 := by
    omega
  rw [this]
  omega
  rw [aeq3]
