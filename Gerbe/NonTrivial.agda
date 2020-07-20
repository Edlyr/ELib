{-# OPTIONS --cubical #-}

module ELib.Gerbe.NonTrivial where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc ; elim to elimPropTrunc)
open import Cubical.Structures.Group renaming (⟨_⟩ to Grp⟨_⟩)
open import Cubical.Structures.AbGroup renaming (⟨_⟩ to Ab⟨_⟩)
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding
open import Cubical.HITs.SetTruncation renaming (rec to recSetTrunc ; elim to elimSetTrunc)
open import Cubical.HITs.GroupoidTruncation renaming (rec to recGrpdTrunc ; elim to elimGrpdTrunc)

open import Cubical.HITs.S1 renaming (base to base₁)
open import Cubical.HITs.S2 renaming (base to base₂)
open import Cubical.HITs.S3 renaming (base to base₃)
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.Int
open import Cubical.Data.Empty
open import Cubical.Data.Unit

open import ELib.Gerbe.Base
open import ELib.Gerbe.Link
open import ELib.Gerbe.B2

is3ConnS³ : isContr (∥ S³ ∥₃)
is3ConnS³ = ∣ base₃ ∣₃ , elimGrpdTrunc (λ _ → isSet→isGroupoid (groupoidTruncIsGroupoid _ _)) lemma where
  lemma : (x : S³) → ∣ base₃ ∣₃ ≡ ∣ x ∣₃
  lemma base₃ = refl
  lemma (surf i j k) = subLemma i j k where
    subLemma : PathP (λ i → PathP (λ j → PathP (λ k → ∣ base₃ ∣₃ ≡ ∣ surf i j k ∣₃) refl refl) refl refl) refl refl
    subLemma = toPathP (isOfHLevelPathP' 2 (isSet→isGroupoid (groupoidTruncIsGroupoid _ _)) _ _ _ _ _ _)

is3ConnS² : isContr (∥ S² ∥₃)
is3ConnS² = ∣ base₂ ∣₃ , elimGrpdTrunc (λ _ → isSet→isGroupoid (groupoidTruncIsGroupoid _ _)) lemma where
  lemma : (x : S²) → ∣ base₂ ∣₃ ≡ ∣ x ∣₃
  lemma base₂ = refl
  lemma (surf i j) = subLemma i j where
    subLemma : PathP (λ i → PathP (λ j → ∣ base₂ ∣₃ ≡ ∣ surf i j ∣₃) refl refl) refl refl
    subLemma = toPathP (isOfHLevelPathP' 1 (groupoidTruncIsGroupoid _ _) _ _ _ _)

3connS² : (x : S²) → ∥ base₂ ≡ x ∥₂
3connS² base₂ = ∣ refl ∣₂
3connS² (surf i j) = lemma i j where
  lemma : SquareP (λ i j → ∥ base₂ ≡ surf i j ∥₂) (λ i → ∣ refl ∣₂) (λ i → ∣ refl ∣₂) (λ i → ∣ refl ∣₂) λ i → ∣ refl ∣₂
  lemma = isOfHLevel→isOfHLevelDep 2 {B = λ x → ∥ base₂ ≡ x ∥₂} (λ _ → setTruncIsSet) _ _ _ _ _

connS² : (x : S²) → ∥ base₂ ≡ x ∥
connS² x = recSetTrunc (isProp→isSet propTruncIsProp) ∣_∣ (3connS² x)

connS¹ : (x y : S¹) → ∥ x ≡ y ∥
connS¹ x y = recPropTrunc propTruncIsProp (λ px →
  recPropTrunc propTruncIsProp (λ py → ∣ sym px ∙ py ∣) (isConnectedS¹ y)) (isConnectedS¹ x)

notContrS¹ : isContr S¹ → ⊥
notContrS¹ p = lemma (isProp→isSet (isContr→isProp p) _ _ loop refl) where
  data 𝟚 : Type where
    N : 𝟚
    S : 𝟚

  N≠S : N ≡ S → ⊥
  N≠S p = transport (cong f p) tt where
    f : 𝟚 → Type
    f N = Unit
    f S = ⊥

  swap : 𝟚 → 𝟚
  swap N = S
  swap S = N

  sec : section swap swap
  sec N = refl
  sec S = refl

  swap≃ : 𝟚 ≃ 𝟚
  swap≃ = isoToEquiv (iso swap swap sec sec)

  f : S¹ → Type
  f base₁ = 𝟚
  f (loop i) = ua swap≃ i

  lemma : loop ≡ refl → ⊥
  lemma p = N≠S
      (N                        ≡⟨ sym (transportRefl N) ⟩
      transport refl N          ≡⟨ (λ i → transport (cong f (p (~ i))) N) ⟩
      transport (ua swap≃) N    ≡⟨ uaβ swap≃ N ⟩
      S ∎)

trunc× : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → ∥ A × B ∥₃ ≃ ∥ A ∥₃ × ∥ B ∥₃
trunc× {A = A} {B = B} = isoToEquiv (iso f g (λ (a , b) → sec' a b) retr) where
  f : ∥ A × B ∥₃ → ∥ A ∥₃ × ∥ B ∥₃
  f = recGrpdTrunc (isGroupoidΣ groupoidTruncIsGroupoid (λ _ → groupoidTruncIsGroupoid)) λ (a , b) → ∣ a ∣₃ , ∣ b ∣₃

  g : ∥ A ∥₃ × ∥ B ∥₃ → ∥ A × B ∥₃
  g (a , b) = recGrpdTrunc groupoidTruncIsGroupoid (λ a → recGrpdTrunc groupoidTruncIsGroupoid (λ b → ∣ a , b ∣₃) b) a

  sec' : (a : ∥ A ∥₃) (b : ∥ B ∥₃) → f (g (a , b)) ≡ (a , b)
  sec' = elimGrpdTrunc (λ _ → isGroupoidΠ λ _ → isSet→isGroupoid (isGroupoidΣ groupoidTruncIsGroupoid (λ _ → groupoidTruncIsGroupoid) _ _))
   λ a → elimGrpdTrunc (λ _ → isSet→isGroupoid (isGroupoidΣ groupoidTruncIsGroupoid (λ _ → groupoidTruncIsGroupoid) _ _))
   λ b → refl

  retr : retract f g
  retr = elimGrpdTrunc (λ _ → isSet→isGroupoid (groupoidTruncIsGroupoid _ _)) λ x → refl

contr× :  ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → isContr (A × B) → isContr A
contr× (c , p) = fst c , λ y → cong fst (p (y , snd c))

prop× :  ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → ∥ B ∥ → isProp (A × B) → isProp A
prop× b p = recPropTrunc isPropIsProp (λ b x y → cong fst (p (x , b) (y , b))) b

module _ (Hopf : S² → Type) (baseS : Hopf base₂ ≡ S¹) (total : Σ S² Hopf ≡ S³) where
  notTrivialHopf : ((x : S²) → Hopf x ≡ S¹) → ⊥
  notTrivialHopf c = notContrS¹ step4 where
    total' : Σ S² Hopf ≡ S¹ × S²
    total' = Σ-cong-snd c ∙ ua Σ-swap-≃

    step1 : isContr ∥ S¹ × S² ∥₃
    step1 = transport (cong (isContr ∘ ∥_∥₃) (sym total ∙ total')) is3ConnS³

    step2 : isContr (∥ S¹ ∥₃ × ∥ S² ∥₃)
    step2 = transport (cong isContr (ua trunc×)) step1

    step3 : isContr (∥ S¹ ∥₃)
    step3 = contr× step2

    step4 : isContr S¹
    step4 = transport (cong isContr (groupoidTruncIdempotent isGroupoidS¹)) step3

  groupℤ : AbGroup
  groupℤ = makeAbGroup ℤ.0g ℤ._+_ ℤ.-_ ℤ.is-set ℤ.assoc ℤ.rid ℤ.invr +-comm where
    module ℤ = Group intGroup

  gerbe-base : Gerbe
  gerbe-base = gerbe S¹ (isgerbe ∣ base₁ ∣ isGroupoidS¹ connS¹ comm) where
    comm : (x : S¹) (p q : x ≡ x) → p ∙ q ≡ q ∙ p
    comm x = recPropTrunc (isPropΠ2 λ _ _ → isGroupoidS¹ _ _ _ _)
      (λ p → transport (λ i → (r s : p i ≡ p i) → r ∙ s ≡ s ∙ r) comm-ΩS¹) (isConnectedS¹ x)

  link-base : Link gerbe-base groupℤ
  link-base = makeLink-pnt hom where
    hom : AbGroupEquiv (π gerbe-base base₁) groupℤ
    hom = groupequiv (isoToEquiv ΩS¹IsoInt) winding-hom

  lemma1 : (x : S²) → IsGerbe (Hopf x)
  lemma1 x = recPropTrunc isPropIsGerbe (λ p → transport (cong IsGerbe (sym baseS ∙ cong Hopf p)) (Gerbe.isGerbe gerbe-base)) (connS² x)

  lemma2 : (x : S²) → Link (gerbe (Hopf x) (lemma1 x)) groupℤ
  lemma2 x = recSetTrunc isSetLink (λ p → transport (cong (λ r → Link r groupℤ) (lemma p)) link-base) (3connS² x) where
    lemma : (base₂ ≡ x) → gerbe-base ≡ gerbe (Hopf x) (lemma1 x)
    lemma p = gerbeEq (sym baseS ∙ cong Hopf p)

  nonTrivialGerbe : S² → B² groupℤ
  nonTrivialGerbe x = b² (gerbe (Hopf x) (lemma1 x)) (lemma2 x)

  noGlobalSection : ((x : S²) → Hopf x) → ⊥
  noGlobalSection s = notTrivialHopf λ x → trivialHopf x ∙ baseS where
    trivialHopf : (x : S²) → Hopf x ≡ Hopf base₂
    trivialHopf x = cong B².Carrier lemma where
      open B²ΣTheory
      lemma : nonTrivialGerbe x ≡ nonTrivialGerbe base₂
      lemma = uaB² groupℤ (b²equiv (fst deloop) (deloop .snd .snd)) where
        deloop : deloopType (B².lnk (nonTrivialGerbe x)) (B².lnk (nonTrivialGerbe base₂)) (grouphom (λ x → x) (λ _ _ → refl)) (s x) (s base₂)
        deloop = deloopContr _ _ _ _ _ .fst
