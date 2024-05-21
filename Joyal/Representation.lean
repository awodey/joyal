import Mathlib.Order.Birkhoff
import Mathlib.Order.Heyting.Hom
import Mathlib.Order.Category.BddDistLat
import Mathlib.Order.Zorn
import Mathlib.Order.CompleteBooleanAlgebra

set_option autoImplicit false

theorem joyal_rep :
∀ (A : Type)[HeytingAlgebra A],
∃ (P : Type), ∃ (po : PartialOrder P),
∃ (j : HeytingHom A (LowerSet P)),
conserv j := sorry

/- proof:
Let J = DLat(H,2)^op be the poset of prime filters
in H, and consider the transposed evaluation map,
η : H −→ Down(DLat(H,2)op) ∼= Pos(DLat(H,2), 2)
given by
η(p)={F|p∈F prime}∼={f:H→2|f(p)=1}.
Clearly η(0) = ∅ and η(1) = DLat(H, 2),
and similarly for the other meets and joins,
so η is a lattice homomorphism.
Moreover, if p ̸= q ∈ H then we have that η(p) ̸= η(q),
by the Prime Ideal Theorem.

Thus it only remains to show that
η(p ⇒ q) = η(p)⇒η(q) as LowerSets in Spec(H)

Unwinding the definitions, this means that,
for all f ∈ DLat(H, 2),
            = PrimeIdeals(H)
            = PrimeFilters(H)
p⇒q ∈ F iff for all prime filters G ⊇ F,
p ∈ G implies q ∈ G,
by the definition of => in Spec(H).

Now if p ⇒ q ∈ F, then for all (prime) filters G ⊇ F,
also p ⇒ q ∈ G, and so p ∈ G implies q ∈ G,
since (p ⇒ q) ∧ p ≤ q.

Conversely, suppose p ⇒ q not ∈ F.
We seek a prime filter G ⊇ F with p ∈ G but not q ∈ G.

Consider the filter

F[p] = { h ∈ H | x ∧ p ≤ h for some x ∈ F } ,

F[p] is the join of F and ↑(p) in the poset of filters.
Clearly p ∈ F[p].
We claim that q is not ∈ F[p].
For if q ∈ F[p], then x ∧ p ≤ q for some x ∈ F,
whence x ≤ p ⇒ q, and so p ⇒ q ∈ F, contrary to assumption.

Applying the following Prime Filter Lemma, there is a prime filter G ⊇ F[p], with p ∈ G and not q ∈ G.

Prime Filter Lemma. Let F be a filter with p ∈ F but not q ∈ F. Then there is a prime filter G ⊇ F with p ∈ G but not q ∈ G.

Pf: Apply the Prime Ideal Theorem to the distributive lattice H^op, in which prime ideals are exactly prime filters in H.
-/
