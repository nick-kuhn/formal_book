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

Authors: Moritz Firsching, Nikolas Kuhn
-/
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Polynomial.Basic
import Mathlib.Order.LocallyFinite


open ZMod Finset
open Polynomial (X)
open BigOperators

/-!
# The law of quadratic reciprocity

## Outline
  - Legendre symbol
  - Euler's criterion
  - First proof
    - Lemma of Gauss
    - proof
  - Second proof
    - A.
    - B.
    - First expression -- TO DO
    - Second expression -- TO DO
    - The multiplicative group of a finite field is cyclic
    - proof
-/

section
namespace book
namespace quadratic_reciprocity




/- Throughout this section, `p` is an odd prime. -/
variable (p : ℕ) (h_p : p ≠ 2) [Fact (Nat.Prime p)]


def legendre_sym (a : ℤ) : ℤ :=
  ite ( (a : ZMod p) = 0) 0 $
    ite (∃ b : ZMod p, a = b ^ (2 : ℤ)) 1 (-1)

/--
Fermat's little theorem: If `a` is nonzero modulo the odd prime `p`, then `a ^ (p - 1) = -1`
modulo `p`.
-/
lemma fermat_little (a : ℤ): (a ≠ (0 : ZMod p)) → a ^ (p - 1) = (-1 : ZMod p) := by
  let units_finset := (Finset.univ : Finset (ZMod p)).erase 0
  let image_finset := (units_finset).image (fun x : ZMod p => (a : ZMod p) * x)
  have : units_finset = image_finset := by sorry
  sorry


theorem euler_criterion (a : ℤ) :
  a ≠ (0 : ZMod p) → (legendre_sym p a : ZMod p) = a ^ ((p - 1) / 2) := by
  sorry

lemma product_rule (a b : ℤ) :
  legendre_sym p (a * b) = (legendre_sym p a) * (legendre_sym p b) := by
  sorry

/-!
### First proof
For the statement, see `theorem quadratic_reciprocity_1`.
-/

-- Maybe define the function `r i` = "reduce p i" explicitly ?
--TODO : This should probably be broken down a little bit first
lemma lemma_of_Gauss (p : ℕ) [Fact (Nat.Prime p)] (a : ℤ) (h_a : a ≠ (0 : ZMod p))
  ( r : ℤ → ℤ ) (h_r : (∀ i, (- (p: ℤ) - 1)/2 ≤ r i ∧ r i ≤ ((p : ℤ) - 1)/2))
  ( H : ∀ i, (r i : ℤ) = (a * i : ZMod p) ) :
   -- TODO: check why this is needed after porting to lean4
   have : LocallyFiniteOrder ℤ := by sorry
   legendre_sym p a =
   Finset.card ((Icc (1 : ℤ) (((p : ℤ)-1)/2)).image r ∩ (Icc (-((p: ℤ) - 1)/2) (-1))) := by
  sorry

theorem quadratic_reciprocity_1 (p q : ℕ) (hp : p ≠ 2) (hq : q ≠ 2)
  [Fact (Nat.Prime p)] [Fact (Nat.Prime q)] :
  (legendre_sym p q) * (legendre_sym q p) = -1 ^ ((p-1) / 2 * (q - 1) / 2 ) :=
  sorry

/-!
### Second Proof
TODO:
    - A.
    - B.
    - First expression
    - Second expression
    - The multiplicative group of a finite field is cyclic
-/

/- The group of units of a finite field is cyclic, i.e. has a multiplicative generator-/
lemma mult_cyclic (K : Type _) [Field K] [Fintype K] : ∃ ζ : Kˣ, ∀ α : Kˣ, ∃ k : ℤ, α = ζ ^ k := by
  sorry


lemma fact_A (p q : ℕ) (hp : p ≠ 2) (hq : q ≠ 2) [Fact (Nat.Prime p)] [Fact (Nat.Prime q)]
  (h_pq : p ≠ q) (K : Type _) [Field K] [Fintype K] (H : Fintype.card K = q ^ (p - 1)) :
  ∀ a b : K, (a + b) ^ q = a ^ q + b ^ q :=
  sorry

/-
For any element `ζ` of multiplicative order `p` in a field `K`, we have a polynomial
decomposition`X^p - 1 = (X - ζ) * (X - ζ ^ 2) * ... * (X - ζ ^ p)`.
-/
lemma fact_B (p : ℕ) [Fact (Prime p)] (K : Type _) [Field K] (ζ : Kˣ) (h_1 : ζ ^ p = 1)
  (h_2 : ζ ≠ 1) :
  X  ^ (p - 1) - 1  = ∏ i in Icc 1 p, (X - (Polynomial.C (ζ : K)) ^ i) := by
  sorry

theorem quadratic_reciprocity_2 (p q : ℕ) (hp : p ≠ 2) (hq : q ≠ 2)
  [Fact (Nat.Prime p)] [Fact (Nat.Prime q)] :
  (legendre_sym p q) * (legendre_sym q p) = -1 ^ ((p-1) / 2 * (q - 1) / 2 ) := by
  sorry


end quadratic_reciprocity
end book
end --section
