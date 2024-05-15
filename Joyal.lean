-- This module serves as the root of the `Joyal` library.
-- Import modules here that should be built as part of the library.
import «Joyal».Basic
import Mathlib.Order.Birkhoff
import Mathlib.Order.Heyting.Hom
import Mathlib.Order.Category.BddDistLat
#check Lattice
#check HeytingAlgebra
#check HeytingHom
#check DistribLattice
#check BoundedLatticeHom

def DownSet (P : Type)[PartialOrder P] : Type :=
{ A : Set P // ∀ a ∈ A , ∀ b ≤ a , b ∈ A }

instance (P : Type)[PartialOrder P] : LE (DownSet P)
  where le s t := s.1 ∪ t.1 = t.1

theorem union_down (P : Type)[PartialOrder P] {s t : DownSet P} :
   ∀ a ∈ s.1 ∪ t.1 , ∀ b ≤ a , b ∈ s.1 ∪ t.1 := by
     intro x x2 b b2
     cases x2
     case inl h =>
      have h2 : b ∈ s.1 := by
        apply s.2 x
        apply h
        apply b2
      apply Or.inl h2
     case inr h =>
      have h3 : b ∈ t.1 := by
        apply t.2 x
        apply h
        apply b2
      apply Or.inr h3

instance (P : Type)[PartialOrder P] : HeytingAlgebra (DownSet P)
  where
  sup s t :=  ⟨s.1 ∪ t.1 , union_down P⟩
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

def conserv {A : Type}[HeytingAlgebra A] {B : Type}[HeytingAlgebra B]
  (h : HeytingHom A B) : Prop := ∀ a : A , h a = ⊤ → a = ⊤

theorem joyal_rep :
∀ (A : Type)[HeytingAlgebra A],
∃ (P : Type), ∃ (po : PartialOrder P),
∃ (j : HeytingHom A (DownSet P)),
conserv j := sorry

/- proof:
Let Jop = DLat(H,2) be the poset of prime filters
in H, and consider the transposed evaluation map,
η : H −→ Down(DLat(H, 2)op) ∼= 2DLat(H,2)
given by
η(p)={F|p∈F prime}∼={f:H→2|f(p)=1}.
Clearly η(0) = ∅ and η(1) = DLat(H, 2),
and similarly for the other meets and joins,
so η is a lattice homomorphism.
Moreover, if p ̸= q ∈ H then we have that η(p) ̸= η(q),
by the Prime Ideal Theorem.
Thus it only remains to show that
η(p ⇒ q) = η(p)⇒η(q).
Unwinding the definitions, this means that,
for all f ∈ DLat(H, 2),
f(p⇒q)=1 iff forall g≥f, g(p)=1 implies g(q)=1.
Equivalently, for all prime filters F ⊆ H,
p⇒q∈F iff for all prime G⊇F, p∈G implies q∈G.
Now if p ⇒ q ∈ F, then for all (prime) filters G ⊇ F,
also p ⇒ q ∈ G, and so p ∈ G implies q ∈ G,
since (p ⇒ q) ∧ p ≤ q.
Conversely, suppose p⇒q /∈F,
and we seek a prime filter G⊇F with p∈G but q ̸∈ G.
Consider the filter
F [p] = {x ∧ p ≤ h ∈ H | x ∈ F } ,
which is the join of F and ↑(p) in the poset of filters.
If q ∈ F[p], then x∧p ≤ q for some x∈F,
whence x≤p⇒q, and so p⇒q∈F,
contrary to assumption;
thus q̸∈F[p].
By the Prime Ideal Theorem again
(applied to the distributive lattice Hop)
there is a prime filter G ⊇ F[p] with q ̸∈ G.
-/

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
