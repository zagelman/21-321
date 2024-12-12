import Mathlib.Tactic
import Mathlib.Data.Nat.Defs
import CmuItp24.Autograde

open Nat

set_option maxHeartbeats 0
-- We ended up spending most of our time fixing project 1, and have left this here as a proof of concept
-- We figured that it would be best to turn in at least one fully complete project
theorem pow_pow (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by
  induction n with
  | zero =>
    rw [Nat.mul_zero, Nat.pow_zero, Nat.pow_zero]
  | succ n ih =>
    rw [Nat.pow_succ, ih, Nat.mul_add, Nat.mul_one, Nat.pow_add]

-- Source: https://math.stackexchange.com/questions/3504067/find-all-positive-integers-satisfying-ab2-ba

/-
Problem: Find all positive integers satisfying a^(b^2) = b^a

Proof:
Let d := gcd(a, b) so that a = du and b = dv so that u and v are coprime.
Then b^a = (dv)^(du) = ((dv)^u)^d and a^(b^2) = (du)^((d^2) * (v^2)) = ((du)^((d) * (v^2))^d.
From this it follows that (dv)^u = (du)^((d) * (v^2)).
Because u and v are coprime, we either have u = 1 or v = 1.
If u = 1, then dv = d^((d) * (v^2)), and so v = d^(((d) * (v^2)) - 1)
from which it quickly follows that also v = d = 1. Hence a = b = 1.
If v = 1, then d^u = (du)^d from which it follows that u^d = d^(u-d),
and in particular u >= d. Let c := gcd(d, u) so that d = ce and u = cw
with e and w coprime and w >= e. Then u^d = (cw)^(ce) = ((cw)^e)^c
and d^(u-d) = (ce)^(cw - ce) = ((ce)^(w-e))^c from which it follows that
(cw)^e = (ce)^(w-e). As e and w are coprime and w >= e it follows that
e = 1, so cw = c^(w-1), and hence w = c^(w-2), from which it quickly follows
that w <= 4. We check these few cases: 1. If w = 1, then c = d = 1 which leads
a = b = 1. If w = 2, then u = 2d and hence a = 2(b^2), and plugging this in
shows that b^((2b)^2) = (2(b^2))^(b^2) = 2^(b^2) * (b^(2 * (b^2)) contradicting
the fact that b is a positive integer. 3. If w = 3, then c = d = 3 which leads
to a = 27 and b = 3. 4. If w = 4, then c = d = 2 which leads to a = 16 and b = 2.
-/

/-
Step 1: Show that v = 1 ∨ u = 1.
To prove this, we start by considering the equation (dv)^u = (du)^((d) * (v^2))
and use the fact that u and v are coprime.
-/

lemma nth_root (d v u n: ℕ) (npos : 0 < n): ((d*v)^u)^n = ((d*u)^(d * (v^2)))^n
→ (d*v)^u = (d*u)^(d*(v^2)) := by
  -- something involving pow_left_inj
  -- apply pow_left_inj
  sorry

theorem step1_v_or_u_is_1 (a b d u v : ℕ) (agt0 : a > 0) (bgt0 : b > 0)
(dgt0 : d > 0) (ugt0 : u > 0) (vgt0 : v > 0) (hd : d = Nat.gcd a b)
(ha : a = d * u) (hb : b = d * v) (huv : Coprime u v) (h : a^(b^2) = b^a) :
  (v = 1 ∨ u = 1) := by
  have h5 : (d*v)^u = (d*u)^(d*(v^2)) := by
    apply nth_root --FIX THIS
    apply dgt0
    rw [← pow_mul', ← hb]
    rw [pow_two]
    rw [← ha]
    rw [pow_pow]
    rw [mul_right_comm]
    rw [← pow_two, ← pow_two]
    rw [← mul_pow, ← hb]
    exact id (Eq.symm h)

  have h6 : d^u * v^u = d^(d*(v^2)) * u^(d*(v^2)) := by
    rw [← mul_pow]
    rw [← mul_pow]
    exact h5

  have vucopudv2 : (v^u).Coprime (u^(d*v^2)) := by
    apply Nat.Coprime.symm
    exact Coprime.pow (d * v ^ 2) u huv
  have ddiv1: d ∣ d^u := by
    refine dvd_pow_self d ?hn
    exact not_eq_zero_of_lt ugt0
  have ddiv2 : d ∣ d^(d*(v^2)) := by
    have : d*(v^2) ≠ 0 := by
      refine Nat.mul_ne_zero ?_ ?_
      exact not_eq_zero_of_lt dgt0
      refine pow_ne_zero 2 ?refine_2.h
      exact not_eq_zero_of_lt vgt0
    refine dvd_pow_self d this
  have : v^u ∣ d^(d*(v^2)) * u^(d*(v^2)) := by
    exact Dvd.intro_left (d ^ u) h6
  have : v^u ∣ d^(d*(v^2)) := by
    exact Coprime.dvd_of_dvd_mul_right vucopudv2 this
  have : u^(d*(v^2)) ∣ d ^ u * v^u := by
    exact Dvd.intro_left (d ^ (d * v ^ 2)) (id (Eq.symm h6))
  have : u^(d*(v^2)) ∣ d ^ u := by
    exact Coprime.dvd_of_dvd_mul_right (Coprime.pow (d * v ^ 2) u huv) this
  have : u^(d*(v^2)) ≤ d ^ u := by
    apply Nat.le_of_dvd
    exact pos_pow_of_pos u dgt0
    exact this
  have : d^u = d^(d*(v^2)) * u^(d*(v^2)) / v^u := by
    refine Nat.eq_div_of_mul_eq_left ?hc h6
    refine pow_ne_zero u ?hc.h
    exact not_eq_zero_of_lt vgt0
  have : u = d*v^2 → v=1 := by --(u=1 ∨ v=1):= by
    intros hu
    have dv2cop: (d*v^2).Coprime (v^2) := by
      rw [← hu]
      exact Coprime.pow_right 2 huv
    -- have : (d*v^2 /d).Coprime (v^2) := by
    --   apply Nat.Coprime.coprime_div_left
    --   apply dv2cop
    have : (v^2).Coprime (v^2) := by
      exact Coprime.coprime_mul_left dv2cop
    have : (v^2) = 1 := by
      exact (coprime_self (v ^ 2)).mp this
    exact eq_one_of_mul_eq_one_left this
  have : u ≠ d*v^2 → v=1 := by
    intros hu
    have : d^u ≠ d^(d*v^2) := by
      sorry --should be simple, idk why this doesn't work
      -- by_contra hdu
      -- have : Nat.log u = Nat.log d*v^2 := by
    sorry
  sorry



lemma powdiff (a b: ℕ) (apos : a > 0) (bneq : b ≠ 0): a ^ (b) / a = a ^ (b-1) := by
  refine Nat.div_eq_of_eq_mul_right apos ?H2
  refine Eq.symm (mul_pow_sub_one ?H2.hn a)
  apply bneq
lemma ineq (a b c : ℕ) (apos : a > 0) (aeqc : c = a) (bg1 : b > 1): a < b * c := by
  rw [aeqc]
  rw [propext (Nat.lt_mul_iff_one_lt_left apos)]
  trivial


theorem step2_ueq1 (a b d u v : ℕ) (hd : d = Nat.gcd a b) (ha : a = d * u) (dgt0 : d > 0)
(vgt0 : v > 0) (hb : b = d * v) (huv : Coprime u v) (ueq1 : u = 1)
(hdvu : (d*v)^u = (d*u)^(d*(v^2))) (hdvueq1 : d^(d*v)^2 = (d*v)^d) (h : a^(b^2) = b^a):
(v=1) ∧ (a=1):= by

  rw [ueq1] at hdvu
  simp at hdvu

  have : v = d^((d * v^2) - 1) := by
    have : v = d ^ (d* v ^ 2) / d := by
      exact Eq.symm (Nat.div_eq_of_eq_mul_right dgt0 (id (Eq.symm hdvu)))
    nth_rewrite 1 [this]
    apply powdiff
    apply dgt0
    refine Nat.mul_ne_zero_iff.mpr ?bneq.a
    constructor
    exact not_eq_zero_of_lt dgt0
    refine pow_ne_zero 2 ?bneq.a.right.h
    exact not_eq_zero_of_lt vgt0

  have h1 : d^((d*v)^2) = (d)^((d^2) * (v^2)) := by
    rw [Nat.mul_pow]

  have h2 : (d*v)^d = (d^d)*(v^d) := by
    rw [Nat.mul_pow]

  sorry

theorem step3_veq1 (a b d u v c w e : ℕ) (h : d = Nat.gcd a b) (ha : a = d * u)
(hb : b = d * v) (hc : c = Nat.gcd d u) (huv : Coprime u v) (veq1 : v = 1)
(hdvu : (d*v)^u = (d*u)^(d*(v^2))) (hd : d = c*e) (hu : u = c*w) (hew : Coprime e w)
(wgee : w ≥ e):
  (w ≤ 4) := by
  rw [veq1] at hdvu
  simp at hdvu

  have : d^u = (d*u)^d := by
    rw [hdvu]

  have : u^d = d^(u-d) := by
    sorry

  have uged : u ≥ d := by
    sorry

  have h1 : u^d = ((c*w)^e)^c := by
    rw [hu]
    rw [hd]
    rw [pow_mul']

  have h2 : d^(u-d) = (c*e)^((c*w)-(c*e)) := by
    rw [hu]
    rw [hd]

  have h3 : (c*e)^((c*w)-((c*e))) = ((c*e)^(w-e))^c := by
    nth_rewrite 1 [← hd]
    nth_rewrite 2 [← hd]
    rw [pow_pow]
    rw [Nat.sub_mul]
    rw [Nat.mul_comm]
    nth_rewrite 2 [Nat.mul_comm]
    rfl

  have : d^(u-d) = ((c*e)^(w-e))^c := by
    rw [h2]
    rw [h3]

  have h5 : (c*w)^e = (c*e)^(w-e) := by
    sorry

  have eeq1 : e = 1 := by
    --Since e and w are Coprime and w ≥ e
    have gcd_ew : Nat.gcd e w = 1 := hew.gcd_eq_one
    sorry

  have h6 : (c*w) = c^(w-1) := by
    rw [eeq1] at h5
    simp at h5
    exact h5

  have h7 : w = c^(w-2) := by
    sorry

  have wle4 : w ≤ 4 := by
    sorry


  sorry

theorem step4_check_cases (a b c d u v w : ℕ) (h : d = Nat.gcd a b) (ha : a = d * u)
(hb : b = d * v) (huv : Coprime u v) (hw : w = c^(w-2)) (wgt0 : w > 0) (wle4 : w ≤ 4):
  ((a = 1 ∧ b = 1) ∧ (a = 27 ∧ b = 3) ∧ (a = 16 ∧ b = 2)) := by

  interval_cases w
  constructor
  sorry
  sorry
  sorry
  sorry
  sorry
