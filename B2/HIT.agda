{-# OPTIONS --cubical #-}

module ELib.B2.HIT where
open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Structures.Group
open import Cubical.Structures.AbGroup
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc)
open import ELib.UsefulLemmas
open import ELib.B1.Base

PointedConnectedGroupoid : (ℓ : Level) → Type (ℓ-suc ℓ)
PointedConnectedGroupoid ℓ = Σ[ X ∈ Type ℓ ] Σ[ a ∈ X ] ((x : X) → ∥ a ≡ x ∥) × isGroupoid X

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
  _⨀_ = G.op
  data B² : Type ℓ where
    base : B²
    path : G.type → refl {x = base} ≡ refl {x = base}
    conc : (g h : G.type) → Square (path g) (path (g ⨀ h)) refl (path h)
    2grpd : (p q : refl {x = base} ≡ refl {x = base}) (r s : p ≡ q) → r ≡ s

  recB² : ∀ {ℓ'} → {A : Type ℓ'} →
    (a : A) →
    (p : G.type → refl {x = a} ≡ refl {x = a}) →
    (concA : (g h : G.type) → Square (p g) (p (g ⨀ h)) refl (p h))
    (2grpdA : (p q : refl {x = a} ≡ refl {x = a}) → (r s : p ≡ q) → r ≡ s) →
    B² → A
  recB² a pA concA 2grpdA base = a
  recB² a pA concA 2grpdA (path g i j) = pA g i j
  recB² a pA concA 2grpdA (conc g h i j k) = concA g h i j k
  recB² a pA concA 2grpdA (2grpd p q r s i j k l) = 2grpdA (X p) (X q) (cong X r) (cong X s) i j k l where
    X = cong (cong (recB² a pA concA 2grpdA))

  elimB²grpd : ∀ {ℓ'} → {A : B² → Type ℓ'} →
    (grpd : (b : B²) → isGroupoid (A b))
    (a : A base) →
    (pA : (g : G.type) → SquareP (λ i j → A (path g i j)) {a₀₀ = a} {a₀₁ = a} (refl {x = a}) {a₁₀ = a} {a₁₁ = a} (refl {x = a}) (refl {x = a}) (refl {x = a}))
    (b : B²) → A b
  elimB²grpd grpd a pA base = a
  elimB²grpd grpd a pA (path g i j) = pA g i j
  elimB²grpd {A = A} grpd a pA (conc g h i j k) = cube i j k where --isOfHLevel→isOfHLevelDep 3 grpd a a refl refl {!pA ?!} {!!} {!!} i j k where
    cube : CubeP (λ i j k → A (conc g h i j k)) (pA g) (pA (g ⨀ h)) (refl {x = refl {x = a}}) (pA h) (refl {x = refl {x = a}}) (refl {x = refl {x = a}})
    cube = toPathP (lemma1 _ _) where
      lemma1 : isProp (typeof (pA (g ⨀ h)))
      lemma1 x y = isOfHLevelPathP' 1 lemma2 _ _ _ _ where
        lemma2 : (i : I) → isSet (PathP (λ j → A (path (g ⨀ h) i j)) a a)
        lemma2 i = isOfHLevelPathP' 2 (lemma3 i) _ _ where
          lemma3 : (i j : I) → isGroupoid (A (path (g ⨀ h) i j))
          lemma3 i j = grpd _
  elimB²grpd grpd a pA (2grpd p q r s i j k l) =
    isOfHLevel→isOfHLevelDep 4 (λ x → isOfHLevelSuc 3 (grpd x)) a a (refl {x = a}) (refl {x = a}) (X p) (X q) (cong X r) (cong X s) (2grpd p q r s) i j k l where
      X = cong (cong (elimB²grpd grpd a pA))

  elimB²set : ∀ {ℓ'} → {A : B² → Type ℓ'} →
    (set : (b : B²) → isSet (A b))
    (a : A base) →
    (b : B²) → A b
  elimB²set set a = elimB²grpd (λ b → isSet→isGroupoid (set b)) a
    (λ g → isOfHLevel→isOfHLevelDep 2 set a a (λ i → a) (λ i → a) (path g))

  elimB²prop : ∀ {ℓ'} → {A : B² → Type ℓ'} → (prop : (b : B²) → isProp (A b)) (a : A base) → (b : B²) → A b
  elimB²prop prop a = elimB²set (λ b → isProp→isSet (prop b)) a
    
  isConnectedB² : (x : B²) → ∥ base ≡ x ∥
  isConnectedB² = elimB²prop (λ _ → propTruncIsProp) ∣ refl ∣
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
  P (B.path g i) (B.path h j) = B².path (g ⨀ h) i j
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
