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
    ℓ ℓ' : Level

record IsGerbe (X : Type ℓ) : Type ℓ where
  no-eta-equality
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
module _ where
  open IsGerbe
  isPropIsGerbe : {X : Type ℓ} → isProp (IsGerbe X)
  inhabited (isPropIsGerbe g1 g2 i) = propTruncIsProp (inhabited g1) (inhabited g2) i
  grpd (isPropIsGerbe g1 g2 i) = isPropIsGroupoid (grpd g1) (grpd g2) i
  conn (isPropIsGerbe g1 g2 i) = isPropΠ2 (λ _ _ → propTruncIsProp) (conn g1) (conn g2) i
  comm (isPropIsGerbe g1 g2 i) = (isPropΠ (λ x → isPropΠ2 λ p q → grpd g1 _ _ _ _)) (comm g1) (comm g2) i
{-
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
-}
  open Gerbe
  gerbeEq : {G H : Gerbe {ℓ}} → (Gerbe.Carrier G ≡ Gerbe.Carrier H) → G ≡ H
  Carrier (gerbeEq p i) = p i
  isGerbe (gerbeEq {G = G} {H = H} p i) = grb i where
    grb : PathP (λ i → IsGerbe (p i)) (isGerbe G) (isGerbe H)
    grb = toPathP (isPropIsGerbe _ _)

π : (G : Gerbe {ℓ}) (x : ⟨ G ⟩) → AbGroup {ℓ}
π G x = makeAbGroup (refl {x = x}) _∙_ sym (Gerbe.grpd G _ _) assoc (λ x → sym (rUnit x)) rCancel (Gerbe.comm G x)


open import Cubical.Data.Sigma
GerbeProduct : Gerbe {ℓ} → Gerbe {ℓ'} → Gerbe
GerbeProduct G H = gerbe X (isgerbe inhabited grpd conn comm) where
  module G = Gerbe G
  module H = Gerbe H
  X = G.Carrier × H.Carrier
  abstract
    inhabited : ∥ X ∥
    inhabited = recPropTrunc propTruncIsProp (λ g → recPropTrunc propTruncIsProp (λ h → ∣ g , h ∣) H.inhabited) G.inhabited
    grpd : isGroupoid X
    grpd = isOfHLevel× 3 G.grpd H.grpd
    conn : (x x' : X) → ∥ x ≡ x' ∥
    conn (x , y) (x' , y') = recPropTrunc propTruncIsProp (λ px → recPropTrunc propTruncIsProp
      (λ py → ∣ ΣPathP (px , py) ∣) (H.conn y y')) (G.conn x x')

    comm : (x : X) (p q : x ≡ x) → p ∙ q ≡ q ∙ p
    comm x p q =
      p ∙ q ≡⟨ refl ⟩
      ΣPathP (cong fst (p ∙ q) , cong snd (p ∙ q)) ≡⟨ (λ i → ΣPathP (lemma-fst i , lemma-snd i)) ⟩
      ΣPathP (cong fst (q ∙ p) , cong snd (q ∙ p)) ≡⟨ refl ⟩
      q ∙ p ∎ where
      lemma-fst : cong fst (p ∙ q) ≡ cong fst (q ∙ p)
      lemma-fst = cong-∙ fst p q ∙ G.comm _ _ _ ∙ sym (cong-∙ fst q p)
      lemma-snd : cong snd (p ∙ q) ≡ cong snd (q ∙ p)
      lemma-snd = cong-∙ snd p q ∙ H.comm _ _ _ ∙ sym (cong-∙ snd q p)
