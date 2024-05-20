import Mathlib.Order.Lattice
import Mathlib.Order.Category.BddDistLat
import Mathlib.Order.PrimeIdeal
import Mathlib.Order.Category.BddLat
import Mathlib.Order.Category.DistLat
import Mathlib.Order.Heyting.Hom
/- import Mathlib.Order.PrimeSeparator -/

/-
Add a lemma that bdd lattice homomorphisms D → Bool correspond to prime ideals/filters.
-/

set_option autoImplicit false

@[reducible]
def Spec (E : Type*) [DistribLattice E] [BoundedOrder E] := BoundedLatticeHom E Bool

-- variable {D : Type*} [DistribLattice D] [BoundedOrder D]
variable {D : Type*} [HeytingAlgebra D]

instance: Preorder (Spec D) where
  le h g := ∀ x, g x ≤ h x
  le_refl h x := le_refl (h x)
  le_trans h g l hg gl x := ge_trans (hg x) (gl x)

instance: PartialOrder (Spec D) where
  le_antisymm h g hg gh := by
    apply BoundedLatticeHom.ext
    intro x
    apply le_antisymm (gh x) (hg x)

def η (x : D) : LowerSet (Spec D)  :=
  ⟨{h | h x = ⊤},
   (by
    intro h g h_le_g hx
    apply top_le_iff.mp
    trans h x
    · apply top_le_iff.mpr hx
    · apply h_le_g
    done
    )⟩

def η.supHom : SupHom D (LowerSet (Spec D)) where
  toFun := η
  map_sup' x y := by
    apply LowerSet.ext
    apply Set.ext
    intro h
    simp [η]

lemma η.bot : η (⊥ : D) = ⊥ := by
  apply LowerSet.ext
  apply Set.ext
  simp [η]

lemma η.top : η (⊤ : D) = ⊤ := by
  apply LowerSet.ext
  apply Set.ext
  simp [η]

def η.infHom : InfHom D (LowerSet (Spec D)) where
  toFun := η
  map_inf' x y := by
    apply LowerSet.ext
    apply Set.ext
    intro h
    simp [η]

instance (P : Type*) [PartialOrder P] : HImp (LowerSet P) where
  himp A B := sSup { X | X ⊓ A ≤ B }

instance (P : Type*) [PartialOrder P] : GeneralizedHeytingAlgebra (LowerSet P)
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

instance (P : Type*) [PartialOrder P] : OrderBot (LowerSet P) where
  bot_le := by simp

instance (P : Type*) [PartialOrder P] : HasCompl (LowerSet P) where
  compl A :=  A ⇨ ⊥

instance (P : Type*) [PartialOrder P] : HeytingAlgebra (LowerSet P) where
  himp_bot := by simp [compl]
