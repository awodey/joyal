import Mathlib.Order.Birkhoff
import Mathlib.Order.Heyting.Hom
import Mathlib.Order.Category.BddDistLat
import Mathlib.Order.Zorn
import Mathlib.Order.CompleteBooleanAlgebra

set_option autoImplicit false

instance (P : Type) [PartialOrder P] : HImp (LowerSet P) where
  himp A B := sSup { X | X ⊓ A ≤ B }

instance (P : Type) [PartialOrder P] : GeneralizedHeytingAlgebra (LowerSet P)
  where
  le_himp_iff := by
    intro A B C
    apply Iff.intro
    · intro AleB
      trans (B ⇨ C) ⊓ B
      · exact inf_le_inf_right B AleB
      · rw [inf_comm]
        apply le_trans (Order.Frame.inf_sSup_le_iSup_inf B { X | X ⊓ B ≤ C })
        simp [sSup_le, inf_comm]
    · intro
      apply le_sSup
      assumption

instance (P : Type) [PartialOrder P] : OrderBot (LowerSet P) where
  bot_le := by simp

instance (P : Type) [PartialOrder P] : HasCompl (LowerSet P) where
  compl A :=  A ⇨ ⊥

instance (P : Type) [PartialOrder P] : HeytingAlgebra (LowerSet P) where
  himp_bot := by simp [compl]

def conserv {A : Type}[HeytingAlgebra A] {B : Type}[HeytingAlgebra B]
  (h : HeytingHom A B) : Prop := ∀ a : A , h a = ⊤ → a = ⊤

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
thus q/∈F[p].
By the Prime Ideal Theorem again
(applied to the distributive lattice H^op)
there is a prime filter G ⊇ F[p] with q ̸∈ G.
-/
