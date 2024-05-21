import Mathlib.Order.Heyting.Hom
import Mathlib.Order.Category.BddDistLat
import Mathlib.Order.PrimeIdeal
import Mathlib.Order.PrimeSeparator

#check DistribLattice

set_option autoImplicit false

open Order Ideal Set Classical

/-
show first that bdd lattice homomorphisms D → Bool correspond to prime ideals/filters.
-/

variable {A : Type*} [DistribLattice A] [BoundedOrder A]
variable {B : Type*} [DistribLattice B] [BoundedOrder B]

def ikernel (h : A → B) := { x : A | h x = ⊥ }

@[simp] theorem mem_ikernel (h : A → B) (a : A) : a ∈ ikernel h ↔ h a = ⊥ := .rfl

def Ikernel (h : BoundedLatticeHom A B) : Order.Ideal A where
  carrier := ikernel h
  lower' := by
    simp [ikernel]
    intro a b b_le_a a_in_ker
    apply eq_bot_mono _ a_in_ker
    apply OrderHomClass.mono ; assumption
  nonempty' := ⟨⊥, map_bot h⟩
  directed' := fun x hx y hy => by
    dsimp [ikernel] at *
    use (x ⊔ y) ; simp [hx, hy]

@[simp] theorem mem_Ikernel (h : BoundedLatticeHom A B) (a : A) : a ∈ Ikernel h ↔ h a = ⊥ := .rfl

instance instIsPrimeIkernel (h : BoundedLatticeHom A Bool) : Order.Ideal.IsPrime (Ikernel h) := by
  have: Order.Ideal.IsProper (Ikernel h) := by
    apply Order.Ideal.isProper_of_not_mem (p := ⊤)
    intro (H : h ⊤ = ⊥)
    rw [map_top] at H
    exact (Bool.eq_not_self ⊤).mp H
  apply Order.Ideal.IsPrime.of_mem_or_mem
  intro x y
  simp
  cases (h x) <;> simp

theorem prime_ideal_is_kernel (I : Ideal A):
IsPrime I -> ∃ (h : A → Bool), I = ikernel h := by
  intros Ip
  have h : BoundedLatticeHom A Bool := {
    toFun := fun x : A => if x ∈ I then false else true
    map_sup' := sorry
    map_inf' := sorry
    map_top' := sorry
    map_bot' := sorry
  }
  have h' : I = ikernel h := sorry
  exact ⟨h , h'⟩



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
