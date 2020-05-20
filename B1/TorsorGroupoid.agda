{-# OPTIONS --cubical #-}

module ELib.B1.TorsorGroupoid where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc)
open import Cubical.HITs.SetTruncation
open import Cubical.Data.Sigma
open import Cubical.Structures.Group
open import ELib.B1.Torsor
open import ELib.UsefulLemmas

module BTorsor {ℓ : Level} {Ggrp : Group {ℓ}} where
  module G = GroupLemmas Ggrp
  _⨀_ = G.op
  inv = G.inv
  B : Type (ℓ-suc ℓ)
  B = Σ[ r ∈ (RAction Ggrp) ] ∥ principalTorsor Ggrp ≡ r ∥

  actionLaw : (T : B) → fst (fst T) → ⟨ Ggrp ⟩ → fst (fst T)
  actionLaw T x g = fst (snd (fst T)) x g
  syntax actionLaw T x g = x ⋆⟨ T ⟩ g

  T⟨_⟩ : B → Type ℓ
  T⟨ X ⟩ = fst (fst X) 

  isTorsorBElement : (x : B) → isTorsor Ggrp (fst x)
  isTorsorBElement (r , p) = recPropTrunc (isPropIsTorsor Ggrp r) (λ p → transport (cong (isTorsor Ggrp) p) (isTorsorPrincipalTorsor Ggrp)) p

  isSetBElement : (x : B) → isSet (fst (fst x))
  isSetBElement x = fst (snd (isTorsorBElement x))

  caracB≡ : (X Y : B) → (X ≡ Y) ≃ (Σ[ f ∈ T⟨ X ⟩ ≃ T⟨ Y ⟩ ] ((x : _) (g : _) → equivFun f (x ⋆⟨ X ⟩ g) ≡ equivFun f x ⋆⟨ Y ⟩ g))
  caracB≡ X Y =
    X ≡ Y
      ≃⟨ isoToEquiv (iso (cong fst) (ΣProp≡ λ _ → propTruncIsProp) (λ _ → refl)
         (λ p → cong ΣPathP (ΣProp≡ (λ _ → isOfHLevelPathP 1 (λ i → propTruncIsProp) _ _) refl))) ⟩
    fst X ≡ fst Y
      ≃⟨ TorsorEquality.torsorEqualityEquiv Ggrp (fst X) (fst Y) (isTorsorBElement X) (isTorsorBElement Y) ⟩
    _ ■

  --caracB≡Morph : (X Y Z : B) → (X ≡ Y

  isGroupoidB : isGroupoid B
  isGroupoidB X Y =
    isOfHLevelRespectEquiv 2 (invEquiv (caracB≡ X Y))
    (isSetΣ (isOfHLevel≃ 2 (isSetBElement X) (isSetBElement Y)) λ _ → isProp→isSet (isPropΠ λ _ → isPropΠ λ _ → isSetBElement Y _ _))

  ----------

  open TorsorLoopspace Ggrp
  
  PT : B
  PT = principalTorsor Ggrp , ∣ refl ∣

  PT' : Torsor
  PT' = principalTorsor Ggrp , isTorsorBElement PT

  -----
  inv-eq : ⟨ Ggrp ⟩ ≃ ⟨ Ggrp ⟩
  inv-eq = isoToEquiv (iso (λ g → inv g) (λ g → inv g) (λ g → G.invInvo g) λ g → G.invInvo g)

  inv-eq-isAntiMorphism : (g g' : ⟨ Ggrp ⟩) → equivFun inv-eq (g ⨀ g') ≡ equivFun inv-eq g' ⨀ equivFun inv-eq g
  inv-eq-isAntiMorphism g g' = sym (G.invUniqueL _ _ (
    (inv g' ⨀ inv g) ⨀ (g ⨀ g')   ≡⟨ G.assoc _ _ _ ⟩
    (inv g' ⨀ (inv g ⨀ (g ⨀ g'))) ≡⟨ cong (λ x → inv g' ⨀ x) (sym (G.assoc _ _ _) ∙ cong (λ y → y ⨀ g') (G.lCancel g) ∙ sym (G.lUnit g')) ⟩
    (inv g' ⨀ g')                   ≡⟨ G.lCancel g' ⟩
    G.id ∎)
   )

  -----
  preΩB : Type _
  preΩB = PT' T≃T PT'

  preΩB→G : preΩB → ⟨ Ggrp ⟩
  preΩB→G ((f , equiv) , β) = f G.id

  G→preΩB : ⟨ Ggrp ⟩ → preΩB
  G→preΩB g = isoToEquiv (iso (λ x → g ⨀ x) (λ x → inv g ⨀ x)
    (λ x → sym (G.lUnit x ∙ cong (λ y → y ⨀ x) (sym (G.rCancel g)) ∙ G.assoc _ _ _))
    (λ x → sym (G.lUnit x ∙ cong (λ y → y ⨀ x) (sym (G.lCancel g)) ∙ G.assoc _ _ _))) ,
    λ x h → (g ⨀ (x ⨀ h)) ≡⟨ sym (G.assoc _ _ _) ⟩ ((g ⨀ x) ⨀ h) ∎

  isAntiMorphism-G→preΩB : (g g' : ⟨ Ggrp ⟩) → G→preΩB (g ⨀ g') ≡ comp≃T {ℓ} {PT'} {PT'} {PT'} (G→preΩB g') (G→preΩB g)
  isAntiMorphism-G→preΩB g g' =
    ΣProp≡ (λ _ → isPropΠ λ _ → isPropΠ λ _ → isSetBElement PT _ _)
    (equivEq _ _ (funExt λ x → ((g ⨀ g') ⨀ x) ≡⟨ G.assoc _ _ _ ⟩ (g ⨀ ((g' ⨀ x))) ∎))

  private
    retr : retract G→preΩB preΩB→G
    retr g = sym (G.rUnit g)

    sec : section G→preΩB preΩB→G
    sec ((f , equiv) , β) =
      ΣProp≡ (λ _ → isPropΠ λ _ → isPropΠ λ _ → isSetBElement PT _ _)
      (equivEq _ _ (funExt λ x →
        (f G.id ⨀ x)
          ≡⟨ sym (β G.id x) ⟩
        f (G.id ⨀ x)
          ≡⟨ cong f (sym (G.lUnit x)) ⟩
        f x ∎))

  G≃preΩB : ⟨ Ggrp ⟩ ≃ preΩB
  G≃preΩB = isoToEquiv (iso G→preΩB preΩB→G sec retr)

  -----

  G≃ΩB : ⟨ Ggrp ⟩ ≃ (PT ≡ PT)
  G≃ΩB = compEquiv inv-eq (compEquiv G≃preΩB (invEquiv (caracB≡ PT PT)))
