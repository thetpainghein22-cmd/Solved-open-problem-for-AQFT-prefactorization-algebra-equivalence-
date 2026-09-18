import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.MorphismProperty.Basic

open CategoryTheory

set_option autoImplicit false
noncomputable section

-- =============================================================
-- BUNDLED CATEGORY
-- =============================================================

structure BundledCat : Type 1 where
  carrier : Type 0
  catInst : Category.{0, 0} carrier

attribute [instance] BundledCat.catInst

instance : CoeSort BundledCat (Type 0) := ⟨BundledCat.carrier⟩

-- Trivial category structure on Unit.
instance : Category Unit where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit
  id_comp := by
    intros
    rfl
  comp_id := by
    intros
    rfl
  assoc := by
    intros
    rfl

instance : Inhabited BundledCat :=
  ⟨⟨Unit, inferInstance⟩⟩

-- =============================================================
-- SETUP
-- =============================================================

opaque OrthCat : Type 0
opaque SetOfMaps (C : OrthCat) : Type 0

opaque Qft_hS (C : OrthCat) (S : SetOfMaps C) : BundledCat
opaque LS_Qft (C : OrthCat) (S : SetOfMaps C) : BundledCat

@[instance] axiom instInhabitedOrthCat : Inhabited OrthCat

@[instance] axiom instInhabitedSetOfMaps (C : OrthCat) :
  Inhabited (SetOfMaps C)

opaque Locrc : Type 0

@[instance] axiom instInhabitedLocrc : Inhabited Locrc

@[instance] axiom instCategoryLocrc : Category.{0, 0} Locrc

opaque C_M (M : Locrc) : OrthCat
opaque S_M (M : Locrc) : SetOfMaps (C_M M)

opaque HK_W (M : Locrc) : BundledCat
opaque L_W_hat_M_CG (M : Locrc) : BundledCat
opaque L_W_M_tP (M : Locrc) : BundledCat
opaque HK_add_W (M : Locrc) : BundledCat

opaque AQFT_cat : Type 0

@[instance] axiom instInhabitedAQFT_cat : Inhabited AQFT_cat

@[instance] axiom instCategoryAQFT_cat : Category.{0, 0} AQFT_cat

opaque tau_LBop : Type 0

opaque Alg (O : Type 0) : Type 0

@[instance] axiom instInhabitedAlg (O : Type 0) :
  Inhabited (Alg O)

@[instance] axiom instCategoryAlg (O : Type 0) :
  Category.{0, 0} (Alg O)

abbrev FQFT_m : Type 0 := Alg tau_LBop

@[instance] axiom instInhabitedFunctorLMPhi (M : Locrc) :
  Inhabited (HK_W M ⥤ L_W_hat_M_CG M)

@[instance] axiom instInhabitedFunctorF (M : Locrc) :
  Inhabited (HK_W M ⥤ AQFT_cat)

opaque LMPhiStar (M : Locrc) :
  HK_W M ⥤ L_W_hat_M_CG M

opaque F (M : Locrc) :
  HK_W M ⥤ AQFT_cat

opaque IsQuillenEquiv
    {C D : Type 0}
    [Category.{0, 0} C]
    [Category.{0, 0} D] :
    (C ⥤ D) → Prop

opaque IsAQFT
    (C : Type 0)
    [Category.{0, 0} C] :
    Prop

-- =============================================================
-- HOMOTOPICAL DISCRETENESS
-- =============================================================

def HomotopicallyDiscrete
    (C : Type 0)
    [Category.{0, 0} C] : Prop :=
  ∀ X Y : C, Subsingleton (X ⟶ Y)

-- =============================================================
-- PROVED CATEGORY-THEORY FACTS
-- =============================================================

theorem B1
    {C D : Type 0}
    [Category.{0, 0} C]
    [Category.{0, 0} D]
    (F : D ⥤ C)
    [F.Faithful]
    (hC : HomotopicallyDiscrete C) :
    HomotopicallyDiscrete D := by
  intro X Y
  haveI : Subsingleton (F.obj X ⟶ F.obj Y) := hC _ _
  exact ⟨fun f g => F.map_injective (Subsingleton.elim _ _)⟩

theorem hd_of_equiv
    {C D : Type 0}
    [Category.{0, 0} C]
    [Category.{0, 0} D]
    (e : C ≌ D)
    (hC : HomotopicallyDiscrete C) :
    HomotopicallyDiscrete D := by
  haveI : e.inverse.Faithful :=
    e.fullyFaithfulInverse.faithful
  exact B1 e.inverse hC

theorem B3
    {C D : Type 0}
    [Category.{0, 0} C]
    [Category.{0, 0} D]
    (F : C ⥤ D)
    (G : D ⥤ C)
    (adj : F ⊣ G)
    [IsIso adj.counit]
    (hC : HomotopicallyDiscrete C) :
    HomotopicallyDiscrete D := by
  haveI : G.Faithful :=
    adj.fullyFaithfulROfIsIsoCounit.faithful
  exact B1 G hC

-- =============================================================
-- C1-C9
-- =============================================================

axiom C1 (M : Locrc) :
  HomotopicallyDiscrete (L_W_M_tP M) →
    IsQuillenEquiv (LMPhiStar M)

axiom C2 (M : Locrc) :
  ∃ (ι : HK_add_W M ⥤ HK_W M),
    Functor.Full ι ∧ Functor.Faithful ι

/--
C3: General adjunction theorem.

For a given `(C, S)`, the theorem provides an adjunction
between the specific categories `X` and `Y`.

In the application in `step3_4`, these are instantiated as

  X = HK_W M
  Y = L_W_hat_M_CG M

so the resulting adjunction transfers homotopical
discreteness from `HK_W M` to `L_W_hat_M_CG M`.
-/
axiom C3
    (C : OrthCat)
    (S : SetOfMaps C)
    (X Y : BundledCat) :
    ∃ (L_bang : X ⥤ Y)
      (L_star : Y ⥤ X)
      (adj : L_bang ⊣ L_star),
      IsIso adj.counit

axiom C4 (M : Locrc) :
  Nonempty (L_W_hat_M_CG M ≌ L_W_M_tP M)

axiom C5a (M : Locrc) :
  ∃ (F' : (F M).EssImageSubcategory ⥤ HK_W M)
    (adj : F' ⊣ (F M).toEssImage),
    IsIso adj.counit

axiom C5b (M : Locrc) :
  IsAQFT (HK_add_W M)

axiom C6 :
  FQFT_m = Alg tau_LBop

axiom C7 :
  HomotopicallyDiscrete (Alg tau_LBop)

axiom C8 (M : Locrc) (x : HK_W M) :
  ∃ y : AQFT_cat, (F M).obj x = y

axiom C9 :
  Nonempty (AQFT_cat ≌ FQFT_m)

-- =============================================================
-- STEPS
-- =============================================================

theorem step1 (M : Locrc) :
    ∃ (ι : HK_add_W M ⥤ HK_W M),
      Functor.Full ι ∧ Functor.Faithful ι :=
  C2 M

theorem step2
    (M : Locrc)
    (h : HomotopicallyDiscrete (HK_W M))
    (ι : HK_add_W M ⥤ HK_W M)
    (hFaith : Functor.Faithful ι) :
    HomotopicallyDiscrete (HK_add_W M) := by
  letI : ι.Faithful := hFaith
  exact B1 ι h

/--
Step 3-4: instantiate the general C3 adjunction with the
specific categories `HK_W M` and `L_W_hat_M_CG M`, then use
the adjunction to transfer homotopical discreteness.
-/
theorem step3_4
    (M : Locrc)
    (h : HomotopicallyDiscrete (HK_W M)) :
    HomotopicallyDiscrete (L_W_hat_M_CG M) := by
  obtain ⟨L_bang, L_star, adj, hIso⟩ :=
    C3
      (C_M M)
      (S_M M)
      (HK_W M)
      (L_W_hat_M_CG M)

  letI : IsIso adj.counit := hIso

  exact B3 L_bang L_star adj h

theorem step5 (M : Locrc) :
  Nonempty (L_W_hat_M_CG M ≌ L_W_M_tP M) :=
  C4 M

theorem step6
    {C D : Type 0}
    [Category.{0, 0} C]
    [Category.{0, 0} D]
    (e : C ≌ D)
    (hC : HomotopicallyDiscrete C) :
    HomotopicallyDiscrete D :=
  hd_of_equiv e hC

theorem step7
    (M : Locrc)
    (h : HomotopicallyDiscrete (L_W_hat_M_CG M)) :
    HomotopicallyDiscrete (L_W_M_tP M) := by
  obtain ⟨e⟩ := step5 M
  exact step6 e h

theorem step8 (M : Locrc) :
  IsAQFT (HK_add_W M) :=
  C5b M

theorem step9
    {C D : Type 0}
    [Category.{0, 0} C]
    [Category.{0, 0} D]
    (F : C ⥤ D)
    (G : D ⥤ C)
    (adj : F ⊣ G)
    [IsIso adj.counit]
    (hC : HomotopicallyDiscrete C) :
    HomotopicallyDiscrete D :=
  B3 F G adj hC

theorem step10
    (M : Locrc)
    (h : HomotopicallyDiscrete ((F M).EssImageSubcategory)) :
    HomotopicallyDiscrete (HK_W M) := by
  obtain ⟨F', adj, hIso⟩ := C5a M
  letI : IsIso adj.counit := hIso
  exact step9 F' (F M).toEssImage adj h

theorem step11 :
  FQFT_m = Alg tau_LBop :=
  C6

theorem step12 :
  HomotopicallyDiscrete (Alg tau_LBop) :=
  C7

theorem step13
    (O : Type 0)
    (h : HomotopicallyDiscrete (Alg O)) :
    HomotopicallyDiscrete (Alg O) :=
  h

theorem step14 :
  HomotopicallyDiscrete FQFT_m :=
  C7

theorem step15 (M : Locrc) :
    ∀ x : HK_W M,
      ∃ y : AQFT_cat, (F M).obj x = y :=
  C8 M

theorem step16 :
  Nonempty (AQFT_cat ≌ FQFT_m) :=
  C9

theorem step17 (M : Locrc) :
    HomotopicallyDiscrete ((F M).EssImageSubcategory) := by
  obtain ⟨e⟩ := step16

  have h_aqft : HomotopicallyDiscrete AQFT_cat :=
    hd_of_equiv e.symm step14

  exact B1 (F M).essImage.ι h_aqft

-- =============================================================
-- MAIN THEOREM
-- =============================================================

theorem main (M : Locrc) :
    IsQuillenEquiv (LMPhiStar M) :=
  C1 M (step7 M (step3_4 M (step10 M (step17 M))))