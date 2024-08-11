import Mathlib.Tactic
import Mathlib.Data.Int.NatPrime
import Mathlib.Data.Set.Card

/-
Here we are formalizing Zagier's 'one-sentence proof' that each prime congruent to one modulo four
is the sum of two squares. You can find it at

`https://en.wikipedia.org/wiki/Fermat%27s_theorem_on_sums_of_two_squares`

Even informally, there is quite a lot going on in the proof.

One of the challenges with formalizing is that, while it's a proof about natural numbers,
it uses subtraction, and the definition of subtraction in `ℕ` is awkward, since for example
`(4 : ℕ) - (17 : ℕ) = (0 : ℕ)`. There are ways to keep track of this carefully, but we
adopt the alternative approach of working in the integers, where subtraction behaves nicely
and the `ring` tactic works.

Another challenge is that we need to work with cardinality,
which requires thinking about finiteness. Finiteness is more complicated than you might think,
and in fact there are a few different notions of set cardinality.
The most commonly used one is `Finset.card` - a `Finset` is a 'bundled' finite set.
Some of the syntax for finsets is a bit complicated though, so we opt for
We use `Set.ncard`, which looks notationally more like what you would expect.

-/

open Nat

variable {p : Nat}

section Prime

/-
  A few lemmas about primality when working in the integers. What they say is simple enough,
  but the proofs are a bit in the weeds; just read and understand the statements.
-/

lemma Int.eq_one_or_eq_one_of_mul_prime {m n : ℤ} (hm : 0 ≤ m) (hn : 0 ≤ n) (hp : p.Prime)
    (hmnp : m * n = p) : m = 1 ∨ n = 1 := by
  lift m to ℕ using hm
  lift n to ℕ using hn
  by_contra! hmn
  exact Int.not_prime_of_int_mul (fun hm' ↦ hmn.1 <| by simpa [hm'])
    (fun hn' ↦ hmn.2 <| by simpa [hn']) hmnp hp

lemma Int.eq_or_eq_of_mul_prime {m n : ℤ} (hm : 0 ≤ m) (hn : 0 ≤ n) (hp : p.Prime)
    (hmnp : m * n = p) : (m = 1 ∧ n = p) ∨ (m = p ∧ n = 1) := by
  obtain (rfl | rfl) := Int.eq_one_or_eq_one_of_mul_prime hm hn hp hmnp
  · simp [← hmnp]
  simp [← hmnp]

lemma Int.square_not_prime (m : ℤ) (p : ℕ) (hmp : m^2 = p) : ¬ p.Prime := by
  have hp' : (m.natAbs)^2 = p := by
    zify; simp [← hmp]
  rw [← hp']
  exact Nat.Prime.not_prime_pow rfl.le

lemma Int.four_mul_not_prime (m : ℤ) (p : ℕ) (hmp : 4*m = p) : ¬ p.Prime := by
  lift m to ℕ using (by linarith)
  norm_cast at hmp
  rw [← hmp, Nat.prime_mul_iff]
  simp [(by decide : ¬ Nat.Prime 4)]


end Prime

section invo

variable {α : Type*}

/-- an involution is a function `f` with `f (f x) = x` for all `x`. -/
def IsInvolution (f : α → α) := ∀ a, f (f a) = a

open Classical in
lemma setOf_not_fixedPoint_even [Fintype α] (f : α → α) (hf : IsInvolution f) :
    Even {x | f x ≠ x}.ncard := by
  -- don't worry about this for now.
  sorry

lemma even_iff_ncard_fixedPoint_even [Finite α] (f : α → α) (hf : IsInvolution f) :
    Even {x | f x = x}.ncard ↔ Even (Nat.card α) := by
  sorry

end invo

section Triple

/-
The type of triples of nonnegative integers `x,y,z` with `x² + 4yz = p`.
These are what make Zagier's proof work. They are the
-/
@[ext] structure Triple (p : ℕ) where
  (x : ℤ)
  (hx : 0 ≤ x)
  (y : ℤ)
  (hy : 0 ≤ y)
  (z : ℤ)
  (hz : 0 ≤ z)
  (h_eq : x^2 + 4 * y * z = p)

/-- There are only finitely many such triples for a given `p`. Don't worry about the proof for now.-/
instance {p : ℕ} (hp : p.Prime) : Finite (Triple p) := sorry

def Triple.xpos (t : Triple p) (hp : p.Prime) : 0 < t.x := by
  refine t.hx.lt_of_ne ?_
  intro h0
  have hmul := t.h_eq
  simp only [← h0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add,
    mul_assoc] at hmul
  exact Int.four_mul_not_prime _ _ hmul hp

def Triple.ypos (t : Triple p) (hp : p.Prime) : 0 < t.y := by
  refine t.hy.lt_of_ne ?_
  intro h0
  have hmul := t.h_eq
  rw [← h0] at hmul
  rw [mul_zero] at hmul 
  rw [zero_mul] at hmul
  rw [add_zero] at hmul 
  apply Int.square_not_prime t.x
  exact hmul


def Triple.zpos (t : Triple p) (hp : p.Prime) : 0 < t.z := by
  refine t.hz.lt_of_ne ?_
  intro h0
  have hmul := t.h_eq
  rw [← h0] at hmul
  rw [mul_zero] at hmul 
  rw [add_zero] at hmul 
  apply Int.square_not_prime t.x p hmul
  exact hp
  

/-- Define the obvious involution which swaps the values of `y` and `z`. -/
def flipInv (p : ℕ) (t : Triple p) : Triple p where
  x := t.x
  hx := t.hx
  y := t.z
  hy := t.hz
  z := t.y
  hz := t.hy
  h_eq := by
    simp_rw [← t.h_eq]
    rw [mul_assoc]
    nth_rw 2 [mul_comm]
    rw [mul_assoc] 

/-- Show it is an involution. -/
theorem flipInv_involution (p : ℕ) : IsInvolution (flipInv p) := by
  unfold IsInvolution
  intro t  
  ext 
  · exact rfl
  · exact rfl
  exact rfl

/-
Before defining Zagier's weird involution, we define predicates corresponding to the case split.
This allows us to separate the computation from the logic a bit more easily.
-/

def TypeOne (t : Triple p) := t.x ≤ t.y - t.z

def TypeTwo (t : Triple p) := t.y - t.z < t.x ∧ t.x < 2 * t.y

def TypeThree (t : Triple p) := 2 * t.y ≤ t.x

lemma typeThree_of_not_typeOne_typeTwo (t : Triple p) (h1 : ¬ TypeOne t) (h2 : ¬ TypeTwo t) :
    TypeThree t := by
  rw [TypeOne, not_le] at h1
  rw [TypeTwo, not_and, not_lt] at h2
  unfold TypeThree
  exact h2 h1

lemma TypeTwo.not_typeOne {t : Triple p} (ht : TypeTwo t) : ¬ TypeOne t := by
  rw [TypeTwo] at ht
  rw [TypeOne, not_le]
  exact ht.1
  

lemma TypeThree.not_typeTwo {t : Triple p} (ht : TypeThree t) : ¬ TypeTwo t := by
  rw [TypeTwo,not_and] 
  rw [TypeThree] at ht
  intro _
  rw [not_lt]
  exact ht

lemma TypeThree.not_typeOne {t : Triple p} (ht : TypeThree t) (hp : p.Prime) : ¬ TypeOne t := by
  rw [TypeOne, not_le]
  rw [TypeThree] at ht
  have hmul := t.h_eq
  
  sorry
  --Toto Here 


@[simps] def A1 (t : Triple p) (ht : TypeOne t) : Triple p where
  x := t.x + 2 * t.z
  hx := by linarith [t.hx, t.hz]
  y := t.z
  hy := t.hz
  z := t.y - t.x - t.z
  hz := by unfold TypeOne at ht; linarith
  h_eq := by simp_rw [← t.h_eq]; ring

lemma A1_typeThree {t : Triple p} (ht : TypeOne t) : TypeThree (A1 t ht) := by
  unfold TypeThree
  unfold TypeOne at ht
  simp [A1, t.hx]

@[simps] def A2 (t : Triple p) (ht : TypeTwo t) : Triple p where
  x := sorry
  hx := by sorry
  y := sorry
  hy := by sorry
  z := sorry
  hz := sorry
  h_eq := sorry

lemma A2_typeTwo (hp : p.Prime) {t : Triple p} (ht : TypeTwo t) : TypeTwo (A2 t ht) := by
  sorry

@[simps] def A3 (t : Triple p) (ht : TypeThree t) : Triple p where
  x := sorry
  hx := sorry
  y := sorry
  hy := sorry
  z := sorry
  hz := sorry
  h_eq := sorry

lemma A3_typeOne {t : Triple p} (ht : TypeThree t) : TypeOne (A3 t ht) := by
  sorry

/- The actual definition of `otherInv`. Its value at `t` is `A_i t`, where `t` has type `i`. -/
open Classical in
noncomputable def otherInv (p : ℕ) (t : Triple p) : Triple p :=
  if h1 : TypeOne t then A1 t h1
  else if h2 : TypeTwo t then A2 t h2
  else A3 t (typeThree_of_not_typeOne_typeTwo t h1 h2)

lemma otherInv_apply_typeOne {t : Triple p} (h1 : TypeOne t) : otherInv p t = A1 t h1 := by
  simp [otherInv, h1]

lemma otherInv_apply_typeTwo {t : Triple p} (h2 : TypeTwo t) : otherInv p t = A2 t h2 := by
  simp [otherInv, h2.not_typeOne, h2]

lemma otherInv_apply_typeThree (hp : p.Prime) {t : Triple p} (h3 : TypeThree t) :
    otherInv p t = A3 t h3 := by
  simp [otherInv, h3.not_typeOne hp, h3.not_typeTwo]

lemma otherInv_inv (hp : p.Prime) : IsInvolution (otherInv p) := by
  sorry

def otherInvFixedPt {k : ℕ} (hpk : p = 4 * k+1) : Triple p where
  x := 1
  hx := zero_le_one
  y := 1
  hy := zero_le_one
  z := k
  hz := by simp
  h_eq := by linarith

lemma otherInvFixedPt.typeTwo (hp : p.Prime) (hpk : p = 4 * k+1) :
    TypeTwo (otherInvFixedPt hpk) := by
  sorry

lemma otherInv_fixed_iff {k : ℕ} (hp : p.Prime) (hpk : p = 4 * k+1) (t : Triple p) :
    otherInv p t = t ↔ t = otherInvFixedPt hpk := by
  sorry

lemma exists_fixedPoint (hp : p.Prime) (hpk : p = 4 * k + 1) (f : Triple p → Triple p)
    (hf : IsInvolution f) : ∃ t, f t = t := by
  sorry

lemma exists_sum_squares (hp : p.Prime) (hpk : p = 4 * k + 1) : ∃ (a b : ℤ), p = a^2 + b^2 := by
  sorry


end Triple
