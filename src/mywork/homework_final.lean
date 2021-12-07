import tactic
import tactic.ring
open_locale big_operators

open finset
/-
Read, understand (collaborating if necessary) the material
in chapter 17 of Jeremy Avigad's *Logic and Proof.* It's here:
https://leanprover.github.io/logic_and_proof/the_natural_numbers_and_induction.html
-/

/-
The following problems are listed in the Problems section of 
the chapter. 

#1. Solve probem #1, first sentence only.
∀P(P(0) ∧ ∀n (P(n) → P(n+1) → ∀n P(n)))


#2. Solve at least one of #2 and #3. Give
    detailed but informal proofs. 
#2
base case 
the statement is true for n = 0
0^2 = 0(1+n)(1+2*0)/6 = 0

Assume statement is true for n = k
0^2 + 1^2 + 2^2 ... k^2 = k(k+1)(1+2k)/6

Prove statement is true for n = k + 1
0^2 + 1^2 + 2^2 ... (k+1)^2 = (k+1)(2+k)(3+2k)/6

rw 0^2 + 1^2 + 2^2 ... (k+1)^2 as
(0^2 + 1^2 + 2^2 ...k^2) + (k+1)^2 = 
k(k+1)(1+2k)/6 + (k+1)^2 =               --inductive step
k(k+1)(1+2k)+6(k+1)^2/6 =
(k+1)(k(1+2k)+6(k+1))/6 =
(k+1)(2k^2+7k+6)/6 =
(k+1)(2+k)(3+2k)/6

Therfore, by induction, for every n, 0^2 + 1^2 + 2^2 + ... n^2 = 16n(1+n)(1+2n) 
-/

/-
To test out of the final exam ...

#1: Give a formal proof for #2 or #3.
#2: Formal or detailed informal proofs 10-13
#3 (Extra Credit): #5 or #9

NOT FINALIZED. ADVISORY. 
-/
--2
example (n : ℕ) : (∑ i in range (n + 1), i^2 : ℚ) = n*(1 + n)*(1 + 2*n)/6 :=
begin
    induction n with n' ih,
    simp,
    rw sum_range_succ,
    rw ih,
    simp,
    ring,
end

--10
example : ∀ (n : ℕ), nat.mul 1 n = n :=
begin
    assume n,
    induction n with n' ih,
    exact rfl,
    simp [nat.mul],
end

--11
example : ∀ ( m n k : ℕ), m * (n + k) = m*n + m*k :=
begin
    assume m n k,
    induction m with m' ih,
    ring,
    rw nat.succ_eq_add_one,
    ring,
    
end

--12
example : ∀ ( m n k : ℕ), m * (n * k) = (m * n) * k :=
begin
    assume m n k,
    induction m with m' ih,
    ring,
    rw nat.succ_eq_add_one,
    ring,
end

--13
example : ∀ ( m n : ℕ), m * n = n * m :=
begin
    assume m n,
    induction m with m' ih,
    ring,
    rw nat.succ_eq_add_one,
    ring,
end