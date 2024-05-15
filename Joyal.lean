-- This module serves as the root of the `Joyal` library.
-- Import modules here that should be built as part of the library.
import «Joyal».Basic
import Mathlib.Order.Birkhoff
import Mathlib.Order.Heyting.Hom
#check Lattice
#check HeytingAlgebra
#check HeytingHom

def DownSet (P : Type)[PartialOrder P] : Type :=
{ A : Set P // ∀ a ∈ A , ∀ b : P , b ≤ a → b ∈ A }

instance (P : Type)[PartialOrder P] :
HeytingAlgebra (DownSet P) where
  sup := sorry
  le := sorry
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry
  le_sup_left := sorry
  le_sup_right := sorry
  sup_le := sorry
  inf := sorry
  inf_le_left := sorry
  inf_le_right := sorry
  le_inf := sorry
  top := sorry
  le_top := sorry
  himp := sorry
  le_himp_iff := sorry
  bot := sorry
  bot_le := sorry
  compl := sorry
  himp_bot := sorry


theorem joyal_rep :
∀ (A : Type)[HeytingAlgebra A],
∃ P : Type, ∃ po : PartialOrder P,
∃ j : HeytingHom A (DownSet P),
Function.Injective j
:= sorry

/- I'm going to need Birkhoff's Prime Ideal Theorem for Distributive Lattices. -/

/- Lemma. Let H be a Heyting algebra.
For any a ∈ H \ {1}, there exists a homomorphism x : H → 2
such that x(a) = 0.

Proof. By Zorn’s lemma, let I be a maximal element of
the set of proper ideals of A which contain a.
Define x(b) = 0 iff b ∈ I.
Clearly, x(a) = 0; we need to check that x is a homomorphism.
The equalities x(0) = 0 and x(b ∨ b′) = x(b) ∨ x(b′)
are easy to check from the defining properties of an ideal.
To see that x(¬b) = ¬x(b) for any b ∈ A,
the crucial observation is that if b ̸∈ I and ¬b ̸∈ I,
then it is possible to enlarge I by adding b to it
and generating an ideal I′,
and I′ will still be proper because ¬b ̸∈ I.
By maximality of I this is impossible.
We thus get that, for any b ∈ A, one of b and ¬b must be in I,
and they can never be both in I,
since that would give 1 = b ∨ ¬b in I,
again contradicting that I is proper.
It now follows from the definitions that x(¬b) = ¬x(b).
-/
