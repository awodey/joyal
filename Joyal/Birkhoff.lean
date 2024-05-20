import Mathlib.Order.Heyting.Hom
import Mathlib.Order.Category.BddDistLat
import Mathlib.Order.PrimeIdeal

/- import Mathlib.Order.PrimeSeparator -/

#check PrimeIdeal
#check HeytingAlgebra

/-
Add a lemma that bdd lattice homomorphisms D → Bool correspond to prime ideals/filters.
-/

def {A : type} [BddDistLat A]{B : type} [BddDistLat B] {h: BoundedLatticeHom A B}:
Ikernel h := { x : A | h x = ⊥ }

def {A : type} [BddDistLat A]{B : type} [BddDistLat B] {h: BoundedLatticeHom A B}:
Fkernel h := { x : A | h x = ⊤ }


theorem kernel_is_prime_ideal (D: BddDistLat):
∀ (h: BoundedLatticeHom D Bool), IsPrimeIdeal Ikernel := sorry

theorem prime_ideal_is_kernel (D: BddDistLat):
∀ (I : PrimeIdeal) ∃ (h: BoundedLatticeHom D Bool), IsPrimeIdeal (kernel h)

/- Birkhoff's Prime Ideal Theorem for Distributive Lattices:
Theorem. Let D be a bounded distributive lattice.
For any d ∈ D, if d ≠ ⊥, then there is a lattice homomorphism h : D → 2
such that h(d) = ⊤.
-/

theorem birkhoff_pit :
∀ (D : BddDistLat),
∀ (d : D), d ≠ ⊥ →
∃ (h : BoundedLatticeHom D Bool), h d = ⊤.
:= sorry

/- see
DistribLattice.prime_ideal_of_disjoint_filter_ideal
in
mathlib4/Mathlib/Order/PrimeSeparator.lean
-/

/- Proof.
It suffices to find a prime ideal M not containing d.
We use Zorn’s Lemma: a poset in which every chain
has an upper bound has a maximal element.
Consider the poset Idl\d of “ideals I without d”, d ̸∈ I,
ordered by inclusion.
The union of any chain I0 ⊆ I1 ⊆ ... in Idl\d
is clearly also in Idl\d,
so we have (at least one) maximal element M ∈ Idl\d.
We claim that M ⊆ D is prime.
To that end, take a,b ∈ D with a∧b ∈ M.
If a,b/∈M, let M[a] = {n ≤ m ∨ a | m ∈ M},
this is the ideal join of M and ↓(a), and similarly for M[b].
Since M is maximal among ideals without d, we therefore have
d∈M[a] and d∈M[b].
Thus let d ≤ m ∨ a and d ≤ m′ ∨ b
for some m,m′ ∈ M.
Then d ∨ m′ ≤ m ∨ m′ ∨ a and d ∨ m ≤ m ∨ m′ ∨ b,
so taking meets on both sides gives
(d ∨ m′) ∧ (d ∨ m)
≤ (m ∨ m′ ∨ a) ∧ (m ∨ m′ ∨ b)
= (m ∨ m′) ∨ (a ∧ b).
Since the righthand side is in the ideal M, so is the left.
But then d ≤ d ∨ (m ∧ m′) is also
in M, contrary to our assumption that M ∈ Idl\d.
-/
