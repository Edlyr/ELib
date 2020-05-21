{-# OPTIONS --cubical #-}

module ELib.B1.TorsorGroupoid where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc)
open import Cubical.HITs.SetTruncation
open import Cubical.Data.Sigma
open import Cubical.Structures.Group
open import ELib.B1.Torsor
open import ELib.Group.Morphism
open import ELib.UsefulLemmas

module BTorsor {ℓ : Level} {G : Group {ℓ}} where
  module Ggrp = GroupLemmas G
  _⨀_ = Ggrp.op
  inv = Ggrp.inv
  B : Type (ℓ-suc ℓ)
  B = Σ[ r ∈ (RAction G) ] ∥ principalTorsor G ≡ r ∥

  T⟨_⟩ : B → Type ℓ
  T⟨ X ⟩ = fst (fst X) 

  isTorsorBElement : (x : B) → isTorsor G (fst x)
  isTorsorBElement (r , p) = recPropTrunc (isPropIsTorsor G r) (λ p → transport (cong (isTorsor G) p) (isTorsorPrincipalTorsor G)) p

  isSetBElement : (x : B) → isSet (fst (fst x))
  isSetBElement x = fst (snd (isTorsorBElement x))
  
  actionLaw : (T : B) → fst (fst T) → ⟨ G ⟩ → fst (fst T)
  actionLaw T x g = fst (snd (fst T)) x g
  syntax actionLaw T x g = x ⋆⟨ T ⟩ g

  open TorsorLoopspace G
  
  caracB≡ : (X Y : B) → (X ≡ Y) ≃ ((fst X , isTorsorBElement X) T≃T ((fst Y , isTorsorBElement Y)))
  caracB≡ X Y =
    X ≡ Y
      ≃⟨ isoToEquiv (iso (cong fst) (ΣProp≡ λ _ → propTruncIsProp) (λ _ → refl)
         (λ p → cong ΣPathP (ΣProp≡ (λ _ → isOfHLevelPathP 1 (λ i → propTruncIsProp) _ _) refl))) ⟩
    fst X ≡ fst Y
      ≃⟨ TorsorEquality.torsorEqualityEquiv G (fst X) (fst Y) (isTorsorBElement X) (isTorsorBElement Y) ⟩
    _ ■

  private
    lemmaProp : {X Y : B} (f : T⟨ X ⟩ ≃ T⟨ Y ⟩) → isProp ((x : T⟨ X ⟩) → (g : ⟨ G ⟩) → fst f (x ⋆⟨ X ⟩ g) ≡ fst f x ⋆⟨ Y ⟩ g)
    lemmaProp {X} {Y} f = isPropΠ λ _ → isPropΠ λ _ → isSetBElement Y _ _

  isGroupoidB : isGroupoid B
  isGroupoidB X Y =
    isOfHLevelRespectEquiv 2 (invEquiv (caracB≡ X Y))
    (isSetΣ (isOfHLevel≃ 2 (isSetBElement X) (isSetBElement Y)) λ f → isProp→isSet (lemmaProp {X} {Y} f))

  
  PT : B
  PT = principalTorsor G , ∣ refl ∣

  PT' : Torsor
  PT' = principalTorsor G , isTorsorBElement PT

  open TorsorEquality G (fst PT') (fst PT') (snd PT') (snd PT')

  -- Intermediate groups that will be used in the characterisation of ΩB
  ΩB : Group {ℓ-suc ℓ}
  ΩB = Path B PT PT , _∙_ , (isGroupoidB PT PT , assoc) , refl , (λ p → sym (lUnit p)) , λ p → sym p , lCancel p

  G' : Group {ℓ}
  G' = DualGroup G

  intermediateMagma : Σ[ X ∈ Type ℓ ] (X → X → X)
  intermediateMagma = PT' T≃T PT' , comp≃T {T¹ = PT'} {T² = PT'} {T³ = PT'}

  m = equivFun (caracB≡ PT PT)
  caracB≡morphism : (p q : ⟨ ΩB ⟩) → m (p ∙ q) ≡ snd intermediateMagma (m p) (m q)
  caracB≡morphism p q = ΣProp≡ (λ f → lemmaProp {PT} {PT} f) (
    fst (m (p ∙ q))
      ≡⟨ torsorEqualityEquivFst (cong fst (p ∙ q)) ⟩ -- This line is technically "refl" but it has been abstracted out
    pathToEquiv (cong fst (cong fst (p ∙ q)))
      ≡⟨ cong pathToEquiv (cong (cong fst) (cong-∙ fst p q) ∙ cong-∙ fst (cong fst p) (cong fst q)) ⟩
    pathToEquiv (cong fst (cong fst p) ∙ cong fst (cong fst q))
      ≡⟨ pathToEquiv∙ _ _ ⟩
    compEquiv (pathToEquiv (cong fst (cong fst p))) (pathToEquiv (cong fst (cong fst q)))
      ≡⟨ sym (λ i → compEquiv (torsorEqualityEquivFst (cong fst p) i) (torsorEqualityEquivFst (cong fst q) i)) ⟩
    compEquiv (fst (m p)) (fst (m q)) ∎)

  preΩB : Group {_}
  preΩB = groupStructFromIso ΩB intermediateMagma (m , snd (caracB≡ PT PT)) caracB≡morphism

  -----
  {-inv-eq : ⟨ G ⟩ ≃ ⟨ G ⟩
  inv-eq = isoToEquiv (iso (λ g → inv g) (λ g → inv g) (λ g → Ggrp.invInvo g) λ g → Ggrp.invInvo g)

  inv-eq-isAntiMorphism : (g g' : ⟨ G ⟩) → equivFun inv-eq (g ⨀ g') ≡ equivFun inv-eq g' ⨀ equivFun inv-eq g
  inv-eq-isAntiMorphism g g' = sym (Ggrp.invUniqueL _ _ (
    (inv g' ⨀ inv g) ⨀ (g ⨀ g')   ≡⟨ Ggrp.assoc _ _ _ ⟩
    (inv g' ⨀ (inv g ⨀ (g ⨀ g'))) ≡⟨ cong (λ x → inv g' ⨀ x) (sym (Ggrp.assoc _ _ _) ∙ cong (λ y → y ⨀ g') (Ggrp.lCancel g) ∙ sym (Ggrp.lUnit g')) ⟩
    (inv g' ⨀ g')                   ≡⟨ Ggrp.lCancel g' ⟩
    Ggrp.id ∎)
   )-}

  -----

  preΩB→G' : ⟨ preΩB ⟩ → ⟨ G' ⟩
  preΩB→G' ((f , equiv) , β) = f Ggrp.id

  G'→preΩB : ⟨ G' ⟩ → ⟨ preΩB ⟩
  G'→preΩB g = isoToEquiv (iso (λ x → g ⨀ x) (λ x → inv g ⨀ x)
    (λ x → sym (Ggrp.lUnit x ∙ cong (λ y → y ⨀ x) (sym (Ggrp.rCancel g)) ∙ Ggrp.assoc _ _ _))
    (λ x → sym (Ggrp.lUnit x ∙ cong (λ y → y ⨀ x) (sym (Ggrp.lCancel g)) ∙ Ggrp.assoc _ _ _))) ,
    λ x h → (g ⨀ (x ⨀ h)) ≡⟨ sym (Ggrp.assoc _ _ _) ⟩ ((g ⨀ x) ⨀ h) ∎

  isMorphism-G'→preΩB : isMorphism G' preΩB G'→preΩB
  isMorphism-G'→preΩB g g' = ΣProp≡ (λ f → lemmaProp {PT} {PT} f) (equivEq _ _ (funExt λ x →
    ((g' ⨀ g) ⨀ x) ≡⟨ Ggrp.assoc g' g x ⟩ (g' ⨀ (g ⨀ x)) ∎))

  --isAntiMorphism-G→preΩB : (g g' : ⟨ G ⟩) → G→preΩB (g ⨀ g') ≡ comp≃T {ℓ} {PT'} {PT'} {PT'} (G→preΩB g') (G→preΩB g)
  --isAntiMorphism-G→preΩB g g' =
  --  ΣProp≡ (λ _ → isPropΠ λ _ → isPropΠ λ _ → isSetBElement PT _ _)
  --  (equivEq _ _ (funExt λ x → ((g ⨀ g') ⨀ x) ≡⟨ Ggrp.assoc _ _ _ ⟩ (g ⨀ ((g' ⨀ x))) ∎))

  private
    retr : retract G'→preΩB preΩB→G'
    retr g = sym (Ggrp.rUnit g)

    sec : section G'→preΩB preΩB→G'
    sec ((f , equiv) , β) =
      ΣProp≡ (λ _ → isPropΠ λ _ → isPropΠ λ _ → isSetBElement PT _ _)
      (equivEq _ _ (funExt λ x →
        (f Ggrp.id ⨀ x)
          ≡⟨ sym (β Ggrp.id x) ⟩
        f (Ggrp.id ⨀ x)
          ≡⟨ cong f (sym (Ggrp.lUnit x)) ⟩
        f x ∎))

  G'≃preΩB : GroupIso G' preΩB
  G'≃preΩB = (isoToEquiv (iso G'→preΩB preΩB→G' sec retr) , isMorphism-G'→preΩB)

  ΩB≃preΩB : GroupIso ΩB preΩB
  ΩB≃preΩB = caracB≡ PT PT , caracB≡morphism

  ΩB≃G : GroupIso ΩB G
  ΩB≃G = groupIsoComp ΩB preΩB G ΩB≃preΩB (groupIsoComp preΩB G' G (groupIsoInv G' preΩB G'≃preΩB) (groupIsoInv G G' (InvGroupIso G)))
