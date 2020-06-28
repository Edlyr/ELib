{-# OPTIONS --cubical #-}

module ELib.B2.HIT where
open import Cubical.Foundations.Everything
open import Cubical.Homotopy.Connected
open import Cubical.Data.Sigma
open import Cubical.Structures.Group hiding (⟨_⟩)
open import Cubical.Structures.AbGroup
open import Cubical.HITs.PropositionalTruncation renaming (∥_∥ to ∥_∥₋₁ ; ∣_∣ to ∣_∣₋₁ ; rec to recPropTrunc)
open import Cubical.HITs.SetTruncation
open import Cubical.HITs.2GroupoidTruncation renaming (rec to 2recGroupoidTrunc)
open import Cubical.HITs.Truncation renaming (elim to elimHTrunc ; rec to recHTrunc)
open import Cubical.HITs.Nullification renaming (elim to elimNull ; ∣_∣ to ∣_∣ₙ)
open import ELib.UsefulLemmas
open import ELib.B1.Base

PointedConnectedGroupoid : (ℓ : Level) → Type (ℓ-suc ℓ)
PointedConnectedGroupoid ℓ = Σ[ X ∈ Type ℓ ] Σ[ a ∈ X ] ((x : X) → ∥ a ≡ x ∥₋₁) × isGroupoid X

PCG = PointedConnectedGroupoid

CubeP : {ℓ : Level} →
  (A : I → I → I → Type ℓ) →
  {a₀₀₀ : A i0 i0 i0} {a₀₀₁ : A i0 i0 i1} {a₀₀₋ : PathP (λ i → A i0 i0 i) a₀₀₀ a₀₀₁} →
  {a₀₁₀ : A i0 i1 i0} {a₀₁₁ : A i0 i1 i1} {a₀₁₋ : PathP (λ i → A i0 i1 i) a₀₁₀ a₀₁₁} →
  {a₀₋₀ : PathP (λ i → A i0 i i0) a₀₀₀ a₀₁₀} {a₀₋₁ : PathP (λ i → A i0 i i1) a₀₀₁ a₀₁₁} →
  (a₀₋₋ : SquareP (A i0) a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁) →
  {a₁₀₀ : A i1 i0 i0} {a₁₀₁ : A i1 i0 i1} {a₁₀₋ : PathP (λ i → A i1 i0 i) a₁₀₀ a₁₀₁}
  {a₁₁₀ : A i1 i1 i0} {a₁₁₁ : A i1 i1 i1} {a₁₁₋ : PathP (λ i → A i1 i1 i) a₁₁₀ a₁₁₁}
  {a₁₋₀ : PathP (λ i → A i1 i i0) a₁₀₀ a₁₁₀} {a₁₋₁ : PathP (λ i → A i1 i i1) a₁₀₁ a₁₁₁}
  (a₁₋₋ : SquareP (A i1) a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
  {a₋₀₀ : PathP (λ i → A i i0 i0) a₀₀₀ a₁₀₀} {a₋₀₁ : PathP (λ i → A i i0 i1) a₀₀₁ a₁₀₁}
  (a₋₀₋ : SquareP (λ i j → A i i0 j) a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
  {a₋₁₀ : PathP (λ i → A i i1 i0) a₀₁₀ a₁₁₀} {a₋₁₁ : PathP (λ i → A i i1 i1) a₀₁₁ a₁₁₁}
  (a₋₁₋ : SquareP (λ i j → A i i1 j) a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
  (a₋₋₀ : SquareP (λ i j → A i j i0) a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
  (a₋₋₁ : SquareP (λ i j → A i j i1) a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
  → Type ℓ
CubeP A a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ = PathP (λ i → SquareP (λ j k → A i j k) (a₋₀₋ i) (a₋₁₋ i) (a₋₋₀ i) (a₋₋₁ i)) a₀₋₋ a₁₋₋

module B² {ℓ : Level} (G : AbGroup {ℓ}) where
  module G = GroupLemmas (AbGroup→Group G)
  _⨀_ = G._+_
  data B² : Type ℓ where
    base : B²
    surf : ⟨ G ⟩ → refl {x = base} ≡ refl {x = base}
    conc : (g h : ⟨ G ⟩) → Square (surf g) (surf (g ⨀ h)) refl (surf h)
    2grpd : (p q : refl {x = base} ≡ refl {x = base}) (r s : p ≡ q) → r ≡ s

  recB² : ∀ {ℓ'} → {A : Type ℓ'} →
    (a : A) →
    (p : ⟨ G ⟩ → refl {x = a} ≡ refl {x = a}) →
    (concA : (g h : ⟨ G ⟩) → Square (p g) (p (g ⨀ h)) refl (p h))
    (2grpdA : (p q : refl {x = a} ≡ refl {x = a}) → (r s : p ≡ q) → r ≡ s) →
    B² → A
  recB² a pA concA 2grpdA base = a
  recB² a pA concA 2grpdA (surf g i j) = pA g i j
  recB² a pA concA 2grpdA (conc g h i j k) = concA g h i j k
  recB² a pA concA 2grpdA (2grpd p q r s i j k l) = 2grpdA (X p) (X q) (cong X r) (cong X s) i j k l where
    X = cong (cong (recB² a pA concA 2grpdA))

  elimB²grpd : ∀ {ℓ'} → {A : B² → Type ℓ'} →
    (grpd : (b : B²) → isGroupoid (A b))
    (a : A base) →
    (pA : (g : ⟨ G ⟩) → SquareP (λ i j → A (surf g i j)) {a₀₀ = a} {a₀₁ = a} (refl {x = a}) {a₁₀ = a} {a₁₁ = a} (refl {x = a}) (refl {x = a}) (refl {x = a}))
    (b : B²) → A b
  elimB²grpd grpd a pA base = a
  elimB²grpd grpd a pA (surf g i j) = pA g i j
  elimB²grpd {A = A} grpd a pA (conc g h i j k) = cube i j k where --isOfHLevel→isOfHLevelDep 3 grpd a a refl refl {!pA ?!} {!!} {!!} i j k where
    cube : CubeP (λ i j k → A (conc g h i j k)) (pA g) (pA (g ⨀ h)) (refl {x = refl {x = a}}) (pA h) (refl {x = refl {x = a}}) (refl {x = refl {x = a}})
    cube = toPathP (lemma1 _ _) where
      lemma1 : isProp (typeof (pA (g ⨀ h)))
      lemma1 = isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (grpd _) _ _) _ _
  elimB²grpd grpd a pA (2grpd p q r s i j k l) =
    isOfHLevel→isOfHLevelDep 4 (λ x → isOfHLevelSuc 3 (grpd x)) a a (refl {x = a}) (refl {x = a}) (X p) (X q) (cong X r) (cong X s) (2grpd p q r s) i j k l where
      X = cong (cong (elimB²grpd grpd a pA))

  elimB²set : ∀ {ℓ'} → {A : B² → Type ℓ'} →
    (set : (b : B²) → isSet (A b))
    (a : A base) →
    (b : B²) → A b
  elimB²set set a = elimB²grpd (λ b → isSet→isGroupoid (set b)) a
    (λ g → isOfHLevel→isOfHLevelDep 2 set a a (λ i → a) (λ i → a) (surf g))

  elimB²prop : ∀ {ℓ'} → {A : B² → Type ℓ'} → (prop : (b : B²) → isProp (A b)) (a : A base) → (b : B²) → A b
  elimB²prop prop a = elimB²set (λ b → isProp→isSet (prop b)) a
    
  isConnectedB² : (x : B²) → ∥ base ≡ x ∥₋₁
  isConnectedB² = elimB²prop (λ _ → propTruncIsProp) ∣ refl ∣₋₁

  isConnB² : isConnected 2 B²
  isConnB² = ∣ base ∣ₙ , elimHTrunc (λ x → isProp→isSet (lemma x)) (elimB²prop (λ b → lemma ∣ b ∣ₙ) refl) where
    lemma : (x : hLevelTrunc 2 B²) → isProp (∣ base ∣ₙ ≡ x)
    lemma = isOfHLevelTrunc 2 ∣ base ∣ₙ

  isSimplyConnB² : isConnected 3 B²
  isSimplyConnB² = ∣ base ∣ₙ , elimHTrunc (λ x → isSet→isGroupoid (lemma x)) (elimB²set (λ b → lemma ∣ b ∣ₙ) refl) where
    lemma : (x : hLevelTrunc 3 B²) → isSet (∣ base ∣ₙ ≡ x)
    lemma = isOfHLevelTrunc 3 ∣ base ∣ₙ


  ∣_∣_ : {ℓ : Level} {A : Type ℓ} → A → (n : _) → hLevelTrunc n A
  ∣ x ∣ n = ∣ x ∣ₙ

  isSimplyConnectedB² : (x y : B²) (p q : x ≡ y) → ∥ p ≡ q ∥₋₁
  isSimplyConnectedB² x y p q = recHTrunc propTruncIsProp (λ r → ∣ r ∣₋₁) (transport (PathIdTrunc _) lemma) where
    A = hLevelTrunc 2 (x ≡ y)
    A' = (∣ x ∣ 3) ≡ (∣ y ∣ 3)
    A'≡A : A' ≡ A
    A'≡A = PathIdTrunc _
    lemma : (∣ p ∣ 2) ≡ (∣ q ∣ 2)
    lemma = subLemma _ _ where
      set : isSet (hLevelTrunc 3 B²)
      set = isProp→isSet (isContr→isProp isSimplyConnB²)
      subLemma : isProp A
      subLemma = transport (cong isProp A'≡A) (set (∣ x ∣ 3) (∣ y ∣ 3))

  isGroupoidΩB² : isGroupoid (base ≡ base)
  isGroupoidΩB² p q = recPropTrunc isPropIsSet (λ r → recPropTrunc isPropIsSet (λ s →
    transport (cong isSet λ i → r i ≡ s i) 2grpd
    ) (isSimplyConnectedB² base base refl q)) (isSimplyConnectedB² base base refl p)

  ------------
  module BG = B (AbGroup→Group G)
  Code : B² → Type ℓ
  Code = recB²
    (BG.B)
    {!!}
    (λ g h → toPathP ({!!}))
    {!!}

  encode : (b : B²) → base ≡ b → Code b
  encode b p = transport (cong Code p) (BG.base)
  {-Code : B² → Type ℓ
  Code = recB²
    G.type
    {!!}
    (λ g h → toPathP (isOfHLevel≡ 2 G.set G.set refl _ _ _))
    λ p q r s → isProp→isSet (isOfHLevel≡ 2 G.set G.set refl refl) p q r s
  -}
 
module TestsSphere {ℓ : Level} where
  data S¹ : Type ℓ where
    base¹ : S¹
    loop : base¹ ≡ base¹
  data S² : Type ℓ where
    base² : S²
    surf : refl {x = base²} ≡ refl {x = base²}

  B² : Type ℓ
  B² = ∥ S² ∥₂

  prod : S¹ → S¹ → B²
  prod base¹ _ = ∣ base² ∣₂
  prod (loop i) base¹ = ∣ base² ∣₂
  prod (loop i) (loop j) = ∣ surf i j ∣₂

{-
module CupProduct {ℓ : Level} (G : AbGroup {ℓ}) where
  Ggrp : Group {ℓ}
  Ggrp = AbGroup→Group G
  module G = GroupLemmas Ggrp
  _⨀_ = G.op

  B¹ : Type ℓ
  B¹ = B.B Ggrp
  B² : Type ℓ
  B² = B².B² G

  P : B¹ → B¹ → B²
  P B.base _ = B².base
  P (B.path g i) B.base = B².base
  P (B.path g i) (B.path h j) = B².surf (g ⨀ h) i j
  P (B.path g i) (B.conc h h' j k) = {!!}
  P (B.path g i) (B.groupoid p q r s j k l) = {!!}
  P (B.conc g h i j) = {!!}
  P (B.groupoid p q r s i j k) = {!!}
  {-B.recB Ggrp
    (λ _ → B².base)
    (λ g → funExt {!!})
    {!!}
    {!!}
    {!!}-}
-}
