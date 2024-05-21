import Mathlib.Order.Lattice
import Mathlib.Order.Category.BddDistLat
import Mathlib.Order.PrimeIdeal
import Mathlib.Order.Category.BddLat
import Mathlib.Order.Category.DistLat
import Mathlib.Order.Heyting.Hom
import Mathlib.Order.PrimeSeparator

import Joyal.Birkhoff

/- import Mathlib.Order.PrimeSeparator -/

/-
Add a lemma that bdd lattice homomorphisms D → Bool correspond to prime ideals/filters.
-/

set_option autoImplicit false

-- Lower sets form a Heyting algebra

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


-- The spectrum of a bounded distributive lattice

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

-- The embedding of a bounded distributive lattice into the lower sets of the spectrum

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

@[simp]
def η.mem (x : D) (h : Spec D) : h ∈ η x ↔ h x = ⊤ := by
  simp [η]

def η.supHom : SupHom D (LowerSet (Spec D)) where
  toFun := η
  map_sup' x y := by
    apply LowerSet.ext
    apply Set.ext
    intro h
    simp [η]

-- lemma η.bot : η (⊥ : D) = ⊥ := by
--   apply LowerSet.ext
--   apply Set.ext
--   simp [η]

-- lemma η.top : η (⊤ : D) = ⊤ := by
--   apply LowerSet.ext
--   apply Set.ext
--   simp [η]

def η.latticeHom : LatticeHom D (LowerSet (Spec D)) where
  toFun := η
  map_sup' := η.supHom.map_sup'
  map_inf' x y := by
    apply LowerSet.ext
    apply Set.ext
    intro h
    simp [η]


/- use
theorem DistribLattice.prime_ideal_of_disjoint_filter_ideal {α : Type u_1}  [DistribLattice α]  [BoundedOrder α] {F : Order.PFilter α}  {I : Order.Ideal α}  (hFI : Disjoint ↑F ↑I) :
∃ (J : Order.Ideal α), J.IsPrime ∧ I ≤ J ∧ Disjoint ↑F ↑J

in mathlib4/Mathlib/Order/PrimeSeparator.lean
to show the following variation needed below
-/


lemma Spec.pit (F : Set D) (x : D) :
  Order.IsPFilter F → x ∉ F →  ∃ (g : Spec D), g x = ⊥ ∧ ∀ y ∈ F, g y = ⊤ := by
  intro Fpf xnF
  have dFx : Disjoint F (Order.Ideal.principal x) := sorry
  apply DistribLattice.prime_ideal_of_disjoint_filter_ideal dFx

  /-
  get (J : Order.Ideal α), J.IsPrime ∧ I ≤ J ∧ Disjoint ↑F ↑J
  take the χ of J to get g : Spec D with g x = ⊥ , etc.
  No duality needed!
  -/





/- Birkhoff's Prime Ideal Theorem for Distributive Lattices:
Theorem. Let D be a bounded distributive lattice.
For any d ∈ D, if d ≠ ⊥, then there is a lattice homomorphism h : D → 2
such that h(d) = ⊤.
-/


lemma in_himp {f : Spec D} {p q : D} :
  f ∈ η p ⇨ η q → ∀ g, g ≤ f → g p = ⊤ → g q = ⊤ := by
  rintro ⟨_, ⟨L, rfl⟩, ⟨_, ⟨M, rfl⟩, fL⟩⟩ g gf gpT
  simp at M fL
  apply M
  simp [gpT]
  apply L.2 gf fL

def η.heytingHom : HeytingHom D (LowerSet (Spec D)) :=
  { η.latticeHom with
    map_himp' := by
      dsimp
      simp [η.latticeHom]
      intro p q
      apply LowerSet.ext ; apply Set.ext
      intro f ; simp
      apply Iff.intro
      · simp [himp]
        intro hpq
        use LowerSet.Iic f ; simp
        intro g
        simp
        intro g_le_f gp
        apply eq_top_iff.mpr
        trans g (p ⊓ (p ⇨ q))
        · simp only [map_inf, gp]
          simp
          rw [← hpq ]
          apply g_le_f
        · simp
          apply inf_le_right
      · intro hphq
        have cat := in_himp hphq
        rw [←Bool.not_eq_false]
        intro fpqF
        obtain ⟨_, ⟨L, rfl⟩, _, ⟨Lηpηq, rfl⟩, fL⟩ := hphq
        simp at Lηpηq fL
        set Fp := {x : D | ∃ y : D, f y = ⊤ ∧ y ⊓ p ≤ x}
        have filterFp : Order.IsPFilter Fp := {
          IsLowerSet := by
            rintro x y y_le_q ⟨z, fzT, zpx⟩
            use z, fzT
            apply le_trans y_le_q zpx
          Nonempty := by
            use ⊥, ⊤, f.map_top'
            simp
          Directed := by
            rintro x ⟨x', fx'T, x'px⟩ y ⟨y', fy'T, y'py⟩
            use x ⊔ y
            simp [Fp]
            use x' ⊓ y'
            simp [fx'T, fy'T]
            constructor
            · trans x' ⊓ p
              · apply inf_le_inf_right
                apply inf_le_left
              · assumption
            · trans y' ⊓ p
              · apply inf_le_inf_right
                apply inf_le_right
              · assumption
        }

        have qFp : q ∉ Fp := by
          rintro ⟨y, fyT, ypq⟩
          rw [OrderHomClass.mono f (le_himp_iff.2 ypq) fyT] at fpqF
          cases fpqF
        obtain ⟨g, gqB, G⟩ :=  Spec.pit Fp q filterFp qFp
        have g_le_f : g ≤ f := by
          intro x fxT
          apply G
          use x, fxT
          simp
        rw [cat g g_le_f (G p ⟨⊤, by simp⟩)] at gqB
        cases gqB

    map_bot' := by
      dsimp
      apply LowerSet.ext
      apply Set.ext
      simp [η.latticeHom, η]
  }
