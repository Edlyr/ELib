{-# OPTIONS --cubical #-}

module ELib.Gerbe.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws

open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc)
open import Cubical.Structures.Group hiding (⟨_⟩)
open import Cubical.Structures.AbGroup renaming (⟨_⟩ to Ab⟨_⟩ ; AbGroup→Group to GRP)

private
  variable
    ℓ : Level

record IsGerbe (X : Type ℓ) : Type ℓ where
  constructor isgerbe
  field
    inhabited : ∥ X ∥
    grpd : isGroupoid X
    conn : (x y : X) → ∥ x ≡ y ∥
    comm : (x : X) → (p q : x ≡ x) → p ∙ q ≡ q ∙ p

record Gerbe : Type (ℓ-suc ℓ) where
  constructor gerbe
  field
    Carrier : Type ℓ
    isGerbe : IsGerbe Carrier

  open IsGerbe isGerbe public

⟨_⟩ : Gerbe → Type ℓ
⟨_⟩ = Gerbe.Carrier

isPropIsGerbe : {X : Type ℓ} → isProp (IsGerbe X)
isPropIsGerbe {X = X} g1 g2 i = isgerbe
  (propTruncIsProp g1.inhabited g2.inhabited i)
  (isPropIsGroupoid g1.grpd g2.grpd i)
  (isPropΠ2 (λ _ _ → propTruncIsProp) g1.conn g2.conn i)
  ((isPropΠ (λ x → isPropΠ2 λ p q → g1.grpd _ _ _ _)) g1.comm g2.comm i) where
  module g1 = IsGerbe g1
  module g2 = IsGerbe g2

gerbeEq : {G H : Gerbe {ℓ}} → (Gerbe.Carrier G ≡ Gerbe.Carrier H) → G ≡ H
gerbeEq {G = G} {H = H} p i = gerbe (p i) (grb i) where
  open Gerbe
  grb : PathP (λ i → IsGerbe (p i)) (isGerbe G) (isGerbe H)
  grb = toPathP (isPropIsGerbe _ _)

π : (G : Gerbe {ℓ}) (x : ⟨ G ⟩) → AbGroup {ℓ}
π G x = makeAbGroup (refl {x = x}) _∙_ sym (Gerbe.grpd G _ _) assoc (λ x → sym (rUnit x)) rCancel (Gerbe.comm G x)
