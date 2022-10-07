/-
Copyright 2022 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Authors: Moritz Firsching
-/
import tactic
import data.set.basic
import data.fintype.card
import ring_theory.integral_domain
import ring_theory.subring.basic
import data.polynomial.ring_division
import algebra.group.conj
import linear_algebra.finite_dimensional
import linear_algebra.basis
import data.polynomial.basic
import ring_theory.polynomial.cyclotomic.basic

open finset subring polynomial
open_locale big_operators nat polynomial
/-!
# Every finite division ring is a field

This is a TODO in `ring_theory.integral_domain`.
## TODO
  - statement
    - proof
      - Roots of unity
-/


--Define cyclotomic polynomials and check their basic properties

--We use a recursive definition, see here: https://exlean.org/well-founded-recursion/
noncomputable def phi_rec : Π  (n : ℕ) (h : Π (d : ℕ), d < n → ℤ[X]), ℤ[X]
| 0 _ := 0
| 1 _ := X + 1
| (n + 1) h := div_by_monic (X ^ (n + 1) - 1 )
    (∏ i in (Icc 1 n), if h_i : i< n + 1 then h i h_i else 1)


noncomputable def phi := well_founded.fix nat.lt_wf phi_rec

example (r n: ℕ) : (r ∈ range n) → r < n := mem_range.mp

lemma phi_div (n : ℕ) (h : n ≠ 0): phi n ∣ X ^ n - 1 :=
begin
  cases n,
    exact absurd (eq.refl 0) h,
  set m := n.succ,
  dsimp only [has_dvd.dvd],
    use (∏ i in Icc 1 n, phi i),

end

lemma phi_div_2 (n : ℕ) (k : ℕ) (h₂ : k ∣ n) (h₃ : k ≠ n) :
  (phi n) * (X ^ k - 1) ∣ (X ^ n - 1)  :=
begin
  sorry,
end


section wedderburn

variables {R : Type*}  [decidable_eq R] [division_ring R]


noncomputable theorem wedderburn (h: fintype R): is_field R :=
begin
  let Z := center R,
  haveI : fintype R := h,



  obtain ⟨n, h⟩ := vector_space.card_fintype Z R,


  set q := fintype.card Z,


  --conjugacy classes with more than one element
  let S := {A : conj_classes Rˣ | fintype.card A.carrier > 1}.to_finset,
  let n_k : ( conj_classes Rˣ) → ℕ := λ A, fintype.card
    (set.centralizer ({(quotient.out' (A : conj_classes Rˣ))} : set Rˣ)),

  --class  formula
  suffices : q ^ n - 1 = q - 1  + ∑ A in S, (q ^ n - 1) / (q ^ (fintype.card A.carrier) - 1), by

  { have n_k_dvd : ∀ A : S, (n_k A ∣ n) := sorry,

    have div₁ : (phi n).eval q ∣ q ^ n - 1, by
    { sorry, },

    have : (phi n).eval q ∣ ∑ A in S, (q ^ n - 1) / (q ^ (fintype.card A.carrier) - 1), by
    { apply dvd_sum,
      intros A h_A,
      apply int.dvd_div_of_mul_dvd,
      let k := n_k A,
      have :=eval_dvd (phi_div_2 n (n_k A) (n_k_dvd ⟨A, h_A⟩) sorry),
      convert this, sorry, sorry, sorry,},


  have : cyclotomic



  },
  --proof of class  formula


  sorry,
end

#check polynomial.eval
end wedderburn
