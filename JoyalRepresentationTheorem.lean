import Mathlib.Order.Heyting.Hom
import Mathlib.Order.PrimeSeparator

section shouldBeInMathlib

/-! ## The Heyting algebra structure on the lower sets of a partial order. -/

instance (P : Type*) [PartialOrder P] : HImp (LowerSet P) where
  himp A B := sSup { X | X ⊓ A ≤ B }

instance (P : Type*) [PartialOrder P] : GeneralizedHeytingAlgebra (LowerSet P)
  where
  le_himp_iff := by
    intro A B C
    constructor
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

end shouldBeInMathlib

/-- The (bounded) lattice homormophism into Prop induced by a prime ideal. -/
def toBoundedLatticeHom {L : Type*} [Lattice L] [BoundedOrder L]
    (I : Order.Ideal L) [isPrime_I : Order.Ideal.IsPrime I] :
    BoundedLatticeHom L Prop where

  toFun x := x ∉ I

  map_sup' := by intros a b ; simp ;tauto

  map_inf' := by
    intros a b
    simp
    constructor
    · have: a ∈ I ∨ b ∈ I → a ⊓ b ∈ I := by
        rintro (aI | bI)
        · have ab_le_a: a ⊓ b ≤ a := by simp
          exact I.lower ab_le_a aI
        · have ab_le_b: a ⊓ b ≤ b := by simp
          exact I.lower ab_le_b bI
      tauto
    · have := @Order.Ideal.IsPrime.mem_or_mem _ _ _ isPrime_I a b
      tauto

  map_top' := by
    simp
    apply isPrime_I.top_not_mem

  map_bot' := by simp

/-- The spectrum of a bounded lattice. -/
@[reducible]
def BoundedLatticeSpectrum (L : Type*) [Lattice L] [BoundedOrder L] := BoundedLatticeHom L Prop

variable {L : Type*} [Lattice L] [BoundedOrder L]

/-- The preorder on the spectrum of a bounded lattice. Note that it is
    *reverse* pointwise order on the homomorphisms. -/
instance: Preorder (BoundedLatticeSpectrum L) where
  le h g := ∀ x, g x ≤ h x
  le_refl h x := le_refl (h x)
  le_trans h g l hg gl x := ge_trans (hg x) (gl x)

/-- The partal order on the spectrum of a bounded lattice. Note that it
    is the *reverse* pointwise order on the homomorphisms. -/
instance: PartialOrder (BoundedLatticeSpectrum L) where
  le_antisymm h g hg gh := by
    apply BoundedLatticeHom.ext
    intro x
    apply le_antisymm (gh x) (hg x)

variable {D : Type*} [DistribLattice D] [BoundedOrder D]

/-- An auxiliary lemma specializing Birkhoff's prime ideal theorem. -/
lemma BoundedLatticeSpectrum.exists_of_filter (F : Order.PFilter D) (x : D) :
  x ∉ F →  ∃ (g : BoundedLatticeSpectrum D), ¬ (g x) ∧ ∀ y ∈ F, g y := by
  intro xnF
  have dFx : Disjoint (F : Set D) (Order.Ideal.principal x : Set D) := by
    intro S SF Sx y yS
    apply xnF
    apply F.mem_of_le (Sx yS) (SF yS)
  obtain ⟨J, ⟨PrimeJ, xJ, DFJ⟩⟩ := DistribLattice.prime_ideal_of_disjoint_filter_ideal dFx
  use toBoundedLatticeHom J
  simp at xJ
  simp [disjoint_iff, Set.eq_empty_iff_forall_not_mem] at DFJ
  simp [toBoundedLatticeHom, xJ]
  assumption

/-- The embedding of a bounded distributive lattice into the lower sets of the spectrum. -/
def joyalRepresentation (x : L) : LowerSet (BoundedLatticeSpectrum L)  :=
  ⟨{h | h x},
   (by
    intro h g h_le_g hx
    apply h_le_g ; assumption
    )⟩

/-- The representation is a lattice homomorphism. -/
def joyalRepresentation.latticeHom : LatticeHom L (LowerSet (BoundedLatticeSpectrum L)) where

  toFun := joyalRepresentation

  map_sup' x y := by
    apply LowerSet.ext
    apply Set.ext
    intro h
    simp [joyalRepresentation]

  map_inf' x y := by
    apply LowerSet.ext
    apply Set.ext
    intro h
    simp [joyalRepresentation]

lemma joyalRepresentation.embedding {x y : D} : joyalRepresentation x ≤ joyalRepresentation y → x ≤ y := by
  intro jxy
  by_contra x_nle_y
  obtain ⟨g, gqB, gT⟩ :=
    BoundedLatticeSpectrum.exists_of_filter (Order.PFilter.principal x) y x_nle_y
  simp at gT
  have gyT := @jxy g (by simp ; exact gT x le_rfl)
  simp [gqB, joyalRepresentation] at gyT


/-- Joyal representation is injective. -/
theorem joyalRepresentation.injective : Function.Injective (joyalRepresentation (L := D)) := by
  intro x y jxy
  apply le_antisymm <;> (apply joyalRepresentation.embedding ; simp [jxy])

/-- Joyal represenation qua an order embedding. -/
def joyalRepresentation.orderEmbedding : D ↪o LowerSet (BoundedLatticeSpectrum D) where
  toFun := joyalRepresentation
  inj' := joyalRepresentation.injective
  map_rel_iff' := ⟨joyalRepresentation.embedding,
                   (OrderHomClass.mono joyalRepresentation.latticeHom ·)⟩

/-- Joyal representation is a Heyting algebra homomorphism. -/
def joyalRepresentation.heytingHom {H : Type*} [HeytingAlgebra H] :
  HeytingHom H (LowerSet (BoundedLatticeSpectrum H)) :=
  { joyalRepresentation.latticeHom with

    map_himp' := by
      dsimp
      simp [joyalRepresentation.latticeHom]
      intro p q
      apply LowerSet.ext ; apply Set.ext
      intro f ; simp
      constructor
      · simp [himp]
        intro fpq
        use LowerSet.Iic f ; simp
        intro g
        simp [joyalRepresentation]
        intro g_le_f gp
        suffices g_p_pq : (g (p ⊓ (p ⇨ q))) by
          simp [map_inf, gp] at g_p_pq
          assumption
        simp only [map_inf, gp] ; simp
        apply g_le_f ; assumption
      · intro fjp_le_fjq
        by_contra not_f_pq
        obtain ⟨_, ⟨L, rfl⟩, _, ⟨Lpq, rfl⟩, fL⟩ := fjp_le_fjq
        simp at Lpq fL
        set Fp := {x : H | ∃ y : H, f y ∧ y ⊓ p ≤ x}
        let FpP : Order.PFilter H := ⟨{
          carrier := Fp
          lower' := by
            rintro x y y_le_q ⟨z, fz, zpx⟩
            use z, fz
            apply le_trans y_le_q zpx
          nonempty' := by
            use ⊥
            use ⊤
            simp [f.map_top']
            apply le_top
          directed' := by
            rintro x ⟨x', fx'T, x'px⟩ y ⟨y', fy'T, y'py⟩
            use x ⊔ y
            simp [Fp]
            use x' ⊓ y'
            simp [fx'T, fy'T, OrderDual.instSup]
            constructor
            · trans x' ⊓ p
              · apply inf_le_inf_right
                apply inf_le_left
              · assumption
            · trans y' ⊓ p
              · apply inf_le_inf_right
                apply inf_le_right
              · assumption
        }⟩
        have qFp : q ∉ Fp := by
          rintro ⟨r, fr, rp_q⟩
          apply not_f_pq
          apply (OrderHomClass.mono f (le_himp_iff.2 rp_q)) fr
        obtain ⟨g, gqB, gT : ∀ y ∈ Fp, g y⟩ := BoundedLatticeSpectrum.exists_of_filter FpP q qFp
        apply gqB ; apply Lpq
        have g_le_f : g ≤ f := by
          intro x fxT
          apply gT
          use x, fxT
          simp
        constructor
        · apply L.2 g_le_f fL
        · exact gT p ⟨⊤, by simp⟩

    map_bot' := by
      dsimp
      apply LowerSet.ext
      apply Set.ext
      simp [joyalRepresentation.latticeHom, joyalRepresentation]
  }
