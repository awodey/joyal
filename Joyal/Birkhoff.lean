import Mathlib.Order.Birkhoff
import Mathlib.Order.Heyting.Hom
import Mathlib.Order.Category.BddDistLat

/- We need Birkhoff's Prime Ideal Theorem for Distributive Lattices:

Theorem. Let D be a distributive lattice.
For any d ∈ D \ {1}, there exists a homomorphism x : D → 2
such that x(d) = 0.
-/

theorem birkhoff_pit :
∀ (D : BddDistLat),
∀ (d : D), d ≠ ⊤ →
∃ (x : BoundedLatticeHom D Bool), x d = ⊥
:= sorry

/- Proof. It suffices to prove it for the case I = (0).
We shall use Zorn’s Lemma: a poset in which every chain
has an upper bound has maximal elements.
Consider the poset I\x of “ideals I without x”, x ̸∈ I,
ordered by inclusion.
The union of any chain I0 ⊆ I1 ⊆ ... in I\x
is clearly also in I\x,
so we have (at least one) maximal element M ∈ I\x.
We claim that M ⊆ D is prime.
To that end, take a,b∈D with a∧b ∈ M.
If a,b/∈M, let M[a]={n≤m∨a|m∈M},
the ideal join of M and ↓(a), and similarly for M[b].
Since M is maximal without x, we therefore have
x∈M[a] and x∈M[b].
Thus let x ≤ m ∨ a and x ≤ m′ ∨ b
for some m,m′ ∈ M.
Then x∨m′ ≤ m ∨ m′ ∨ a and x∨m ≤ m ∨ m′ ∨ b,
so taking meets on both sides gives
(x∨m′)∧(x∨m)≤(m∨m′ ∨a)∧(m∨m′ ∨b)=(m∨m′)∨(a∧b).
Since the righthand side is in the ideal M,
so is the left. But then x ≤ x∨(m∧m′) is also
in M, contrary to our assumption that M ∈ I\x.
-/
