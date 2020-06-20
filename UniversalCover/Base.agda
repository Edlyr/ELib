{-# OPTIONS --cubical #-}
module ELib.UniversalCover.Base where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (∣_∣ to ∣_∣₋₁ ;rec to recPropTrunc ; elim to elimPropTrunc)
open import Cubical.HITs.SetTruncation renaming (rec to recSetTrunc ; elim to elimSetTrunc ; elim2 to elimSetTrunc2)
open import Cubical.HITs.Truncation
open import Cubical.Data.Sigma
--open import Cubical.Functions.FunExtEquiv
--open import Cubical.Functions.Embedding
open import ELib.Connectedness.Base
open import ELib.Connectedness.Properties
--open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.Nullification as Null hiding (rec; elim)
--open import Cubical.Data.NatMinusTwo
open import Cubical.Data.Nat
open import Cubical.Foundations.Equiv.HalfAdjoint

UniversalCover : ∀ {ℓ} → Pointed ℓ → Pointed ℓ
UniversalCover (A , a) = (Σ[ x ∈ A ] ∥ a ≡ x ∥₂) , (a , ∣ refl ∣₂)

UC = UniversalCover

_∙₂_ : ∀ {ℓ} {A : Type ℓ} {x y z : A} → ∥ x ≡ y ∥₂ → ∥ y ≡ z ∥₂ → ∥ x ≡ z ∥₂
p ∙₂ q = recSetTrunc setTruncIsSet (λ p → recSetTrunc setTruncIsSet (λ q → ∣ p ∙ q ∣₂) q) p

sym₂ : ∀ {ℓ} {A : Type ℓ} {x y : A} → ∥ x ≡ y ∥₂ → ∥ y ≡ x ∥₂
sym₂ p = recSetTrunc setTruncIsSet (λ q → ∣ sym q ∣₂) p

rUnit₂ : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : ∥ x ≡ y ∥₂) → p ≡ p ∙₂ ∣ refl ∣₂
rUnit₂ = elimSetTrunc {B = λ p → p ≡ p ∙₂ ∣ refl ∣₂}
  (λ _ → isProp→isSet (setTruncIsSet _ _)) (λ q → cong (∣_∣₂) (rUnit q))
lUnit₂ : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : ∥ x ≡ y ∥₂) → p ≡ ∣ refl ∣₂ ∙₂ p
lUnit₂ = elimSetTrunc {B = λ p → p ≡ (∣ refl ∣₂ ∙₂ p)}
  (λ _ → isProp→isSet (setTruncIsSet _ _)) (λ q → cong (∣_∣₂) (lUnit q))

pathEqualityInTrunc0 : ∀ {ℓ} {A : Type ℓ} (p q : A) → (∣ p ∣₂ ≡ ∣ q ∣₂) ≡ ∥ p ≡ q ∥
pathEqualityInTrunc0 {A = A} p q =
  (∣ p ∣₂ ≡ ∣ q ∣₂)
    ≡⟨ ua (congEquiv setTrunc≃Trunc2) ⟩
  Path (∥_∥_ A (2)) ∣ p ∣ ∣ q ∣
    ≡⟨ PathIdTrunc _ ⟩
  ∥_∥_ (p ≡ q) (1)
    ≡⟨ sym (propTrunc≡Trunc1) ⟩
  ∥ p ≡ q ∥ ∎

UCPath≃ : ∀ {ℓ} {A : Pointed ℓ} → (x y : fst (UniversalCover A)) →
  (x ≡ y) ≃ (Σ[ p ∈ (fst x ≡ fst y) ] snd x ∙₂ ∣ p ∣₂ ≡ snd y)
UCPath≃ {A = A} x y = compEquiv (invEquiv ΣPath≃PathΣ) (pathToEquiv (cong (λ r → Σ (fst x ≡ fst y) r) (funExt λ p → PathP≡Path _ _ _ ∙ cong (λ r → r ≡ snd y) λ i → (lemma p) i (snd x)))) where
  a = snd A
  lemma : (p : fst x ≡ fst y) → transport (λ i → ∥ a ≡ (p i) ∥₂) ≡ (λ α → α ∙₂ ∣ p ∣₂)
  lemma p = J (λ y p → transport (λ i → ∥ a ≡ (p i) ∥₂) ≡ (λ α → α ∙₂ ∣ p ∣₂))
    (funExt λ α → transportRefl α ∙ rUnit₂ _) p

isConnectedUniversalCover : ∀ {ℓ} → (A : Pointed ℓ) → isConnected (fst (UniversalCover A))
isConnectedUniversalCover A = snd (pointConnected→pointed×connected (snd (UniversalCover A) ,
  λ x → elimSetTrunc {B = λ p → ∥ snd (UniversalCover A) ≡ (fst x , p) ∥} (λ _ → isProp→isSet propTruncIsProp)
    (λ p → ∣ fst (invEquiv (UCPath≃ _ _)) (p , sym (lUnit₂ _)) ∣₋₁) (snd x)))

isSimplyConnectedUniversalCover : ∀ {ℓ} (A : Pointed ℓ) → isConnected(snd (UC A) ≡ snd (UC A))
isSimplyConnectedUniversalCover (A , a) = transport (cong isConnected (sym lemma))
  (snd (pointConnected→pointed×connected (isConnectedConnectedComponent _)))
  where
  lemma : (snd (UC (A , a)) ≡ snd (UC (A , a))) ≡ fst (connectedComponent ((a ≡ a) , refl))
  lemma = 
    ((a , ∣ refl ∣₂) ≡ (a , ∣ refl ∣₂))
      ≡⟨ ua (UCPath≃ (a , ∣ refl ∣₂) (a , ∣ refl ∣₂) ) ⟩
    (Σ[ p ∈ (a ≡ a) ] ∣ refl ∣₂ ∙₂ ∣ p ∣₂ ≡ ∣ refl ∣₂)
      ≡⟨ cong (λ x → Σ-syntax (a ≡ a) x) (funExt λ p → cong (λ y → y ≡ ∣ refl ∣₂) (sym (lUnit₂ ∣ p ∣₂))) ⟩
    (Σ[ p ∈ (a ≡ a) ] ∣ p ∣₂ ≡ ∣ refl ∣₂)
      ≡⟨ cong (λ x → Σ (a ≡ a) x ) (funExt λ p → pathEqualityInTrunc0 p refl) ⟩
    (Σ[ p ∈ (a ≡ a) ] ∥ p ≡ refl ∥) ∎

-- HLevel of the UniversalCover
{-
isOfHLevelUniversalCover : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ) → isOfHLevel n (fst A) → isOfHLevel n (fst (UniversalCover A))
isOfHLevelUniversalCover 0 A contrA = snd (UniversalCover A) , λ p → fst (invEquiv (UCPath≃ _ _)) (sym (snd contrA (snd A)) ∙ snd contrA (fst p) , {!!})
isOfHLevelUniversalCover 1 A propA x y = {!!}
isOfHLevelUniversalCover (suc (suc n)) A levelA x y = {!!}
-}
{-
isGrpd→is2typeUniversalCover : ∀ {ℓ} (A : Pointed ℓ) → isGroupoid (fst A) → is2Groupoid (fst (UC A))
isGrpd→is2typeUniversalCover (A , a) grpd x y =
  recPropTrunc isPropIsGroupoid (λ px →
  recPropTrunc isPropIsGroupoid (λ py → 
    transport (λ i → isGroupoid (px i ≡ py i))
     (transport (cong isGroupoid (ua Σ≡))
     (isGroupoidΣ {!!} {!!})
    )
  ) (conn (a , ∣ refl ∣₂) y))
  (conn (a , ∣ refl ∣₂) x) where
  conn = isConnectedUniversalCover (A , a)
-}
