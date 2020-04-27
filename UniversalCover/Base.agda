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
open import Cubical.Data.NatMinusTwo

UniversalCover : ∀ {ℓ} → Pointed ℓ → Pointed ℓ
UniversalCover (A , a) = (Σ[ x ∈ A ] ∥ a ≡ x ∥₀) , (a , ∣ refl ∣₀)

UC = UniversalCover

_∙₀_ : ∀ {ℓ} {A : Type ℓ} {x y z : A} → ∥ x ≡ y ∥₀ → ∥ y ≡ z ∥₀ → ∥ x ≡ z ∥₀
p ∙₀ q = recSetTrunc setTruncIsSet (λ p → recSetTrunc setTruncIsSet (λ q → ∣ p ∙ q ∣₀) q) p

sym₀ : ∀ {ℓ} {A : Type ℓ} {x y : A} → ∥ x ≡ y ∥₀ → ∥ y ≡ x ∥₀
sym₀ p = recSetTrunc setTruncIsSet (λ q → ∣ sym q ∣₀) p

rUnit₀ : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : ∥ x ≡ y ∥₀) → p ≡ p ∙₀ ∣ refl ∣₀
rUnit₀ = elimSetTrunc {B = λ p → p ≡ p ∙₀ ∣ refl ∣₀}
  (λ _ → isProp→isSet (setTruncIsSet _ _)) (λ q → cong (∣_∣₀) (rUnit q))
lUnit₀ : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : ∥ x ≡ y ∥₀) → p ≡ ∣ refl ∣₀ ∙₀ p
lUnit₀ = elimSetTrunc {B = λ p → p ≡ (∣ refl ∣₀ ∙₀ p)}
  (λ _ → isProp→isSet (setTruncIsSet _ _)) (λ q → cong (∣_∣₀) (lUnit q))

pathEqualityInTrunc0 : ∀ {ℓ} {A : Type ℓ} {x y : A} (p q : x ≡ y) → (∣ p ∣₀ ≡ ∣ q ∣₀) ≡ ∥ p ≡ q ∥
pathEqualityInTrunc0 {x = x} {y = y} p q =
  (∣ p ∣₀ ≡ ∣ q ∣₀)
    ≡⟨ ua (congEquiv setTrunc≃Trunc0) ⟩
  Path (∥_∥_ (x ≡ y) (-2+ 2)) ∣ p ∣ ∣ q ∣
    ≡⟨ PathIdTrunc _ ⟩
  ∥_∥_ (p ≡ q) (-2+ 1)
    ≡⟨ sym (propTrunc≡Trunc-1) ⟩
  ∥ p ≡ q ∥ ∎

UCPath≃ : ∀ {ℓ} {A : Pointed ℓ} → (x y : fst (UniversalCover A)) →
  (x ≡ y) ≃ (Σ[ p ∈ (fst x ≡ fst y) ] snd x ∙₀ ∣ p ∣₀ ≡ snd y)
UCPath≃ {A = A} x y = compEquiv (invEquiv Σ≡) (pathToEquiv (cong (λ r → Σ (fst x ≡ fst y) r) (funExt λ p → PathP≡Path _ _ _ ∙ cong (λ r → r ≡ snd y) λ i → (lemma p) i (snd x)))) where
  a = snd A
  lemma : (p : fst x ≡ fst y) → transport (λ i → ∥ a ≡ (p i) ∥₀) ≡ (λ α → α ∙₀ ∣ p ∣₀)
  lemma p = J (λ y p → transport (λ i → ∥ a ≡ (p i) ∥₀) ≡ (λ α → α ∙₀ ∣ p ∣₀))
    (funExt λ α → transportRefl α ∙ rUnit₀ _) p

isConnectedUniversalCover : ∀ {ℓ} → (A : Pointed ℓ) → isConnected (fst (UniversalCover A))
isConnectedUniversalCover A = snd (pointConnected→pointed×connected (snd (UniversalCover A) ,
  λ x → elimSetTrunc {B = λ p → ∥ snd (UniversalCover A) ≡ (fst x , p) ∥} (λ _ → isProp→isSet propTruncIsProp)
    (λ p → ∣ fst (invEquiv (UCPath≃ _ _)) (p , sym (lUnit₀ _)) ∣₋₁) (snd x)))

isSimplyConnectedUniversalCover : ∀ {ℓ} (A : Pointed ℓ) → isConnected(snd (UC A) ≡ snd (UC A))
isSimplyConnectedUniversalCover (A , a) = transport (cong isConnected (sym lemma))
  (snd (pointConnected→pointed×connected (isConnectedConnectedComponent _)))
  where
  lemma : (snd (UC (A , a)) ≡ snd (UC (A , a))) ≡ fst (connectedComponent ((a ≡ a) , refl))
  lemma = 
    ((a , ∣ refl ∣₀) ≡ (a , ∣ refl ∣₀))
      ≡⟨ ua (UCPath≃ (a , ∣ refl ∣₀) (a , ∣ refl ∣₀) ) ⟩
    (Σ[ p ∈ (a ≡ a) ] ∣ refl ∣₀ ∙₀ ∣ p ∣₀ ≡ ∣ refl ∣₀)
      ≡⟨ cong (λ x → Σ-syntax (a ≡ a) x) (funExt λ p → cong (λ y → y ≡ ∣ refl ∣₀) (sym (lUnit₀ ∣ p ∣₀))) ⟩
    (Σ[ p ∈ (a ≡ a) ] ∣ p ∣₀ ≡ ∣ refl ∣₀)
      ≡⟨ cong (λ x → Σ (a ≡ a) x ) (funExt λ p → pathEqualityInTrunc0 p refl) ⟩
    (Σ[ p ∈ (a ≡ a) ] ∥ p ≡ refl ∥) ∎
