{-# OPTIONS --cubical #-}

module ELib.Gerbe.Link where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc ; elim to elimPropTrunc)
--open import Cubical.Homotopy.Loopspace
--open import Cubical.Structures.Group
open import Cubical.Structures.Group hiding (⟨_⟩)
open import Cubical.Structures.AbGroup renaming (⟨_⟩ to Ab⟨_⟩)
open import ELib.Group.Morphism
open import Cubical.Data.Sigma
--open import ELib.B1.MorphismDelooping
--open import ELib.UsefulLemmas
open import Cubical.Functions.Embedding
open import ELib.UsefulLemmas
open import ELib.Gerbe.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

linked-by-ab : (G : Gerbe {ℓ}) (A : AbGroup {ℓ'}) → Type (ℓ-max ℓ ℓ')
linked-by-ab {ℓ} {ℓ'} G Aab = Σ[ e ∈ ((x : ⟨ G ⟩) → GroupIso A (AbGroup→Group (π G x))) ]
  ((x y : ⟨ G ⟩) → compGroupIso A (H x) (H y) (e x) (s-iso x y) ≡ e y) where
  open S G
  A = AbGroup→Group Aab
  H : (x : _) → _
  H x = AbGroup→Group (π G x)

link-by-π : (G : Gerbe {ℓ}) (x : ⟨ G ⟩) → linked-by-ab G (π G x)
link-by-π G x = (λ y → s-iso x y) , λ y z →
  groupIsoEq (AbGroup→Group (π G x)) (AbGroup→Group (π G z)) _ _
  (equivEq _ _ (funExt λ t → recPropTrunc (gerbe-grpd G _ _ _ _) (λ py → recPropTrunc (gerbe-grpd G _ _ _ _) (λ pz →
    transport (λ i → s-fun (py i) (pz i) (s-fun x (py i) t) ≡ s-fun x (pz i) t)
      (! _)
  ) (gerbe-conn G x z)) (gerbe-conn G x y)))
  where
  open S G
  s-fun : (x : _) (y : _) → _
  s-fun x y = s x y .fst .fst
  ! : (t : _) → s-fun x x t ≡ t
  ! t = snd (s x x) refl t ∙ sym (rUnit _ ∙ lUnit _)

-------------------

module _ (G : Gerbe {ℓ}) (A : AbGroup {ℓ'}) (ℒ : linked-by-ab G A) where
  eA = fst ℒ
  condA = snd ℒ
  Agrp = AbGroup→Group A
  test : (B : AbGroup {ℓ'}) → linked-by-ab G B ≃ GroupIso (Agrp) (AbGroup→Group B)
  test B = isoToEquiv (iso f g sec retr) where
    Bgrp = AbGroup→Group B

    pre-f : (linked-by-ab G B) → (x : ⟨ G ⟩) → GroupIso Agrp Bgrp
    pre-f (eB , _) x = compGroupIso Agrp (AbGroup→Group (π G x)) Bgrp (eA x) (invGroupIso Bgrp (AbGroup→Group (π G x)) (eB x))
      
    f₀ : (l : linked-by-ab G B) → Σ[ i ∈ GroupIso Agrp Bgrp ] (((x : ⟨ G ⟩) (g : Ab⟨ A ⟩) → i .fst .fst g ≡ pre-f l x .fst .fst g ))
    f₀ (eB , condB) = isContrT .fst where
      pre-f₀ : (x : ⟨ G ⟩) → GroupIso Agrp Bgrp
      pre-f₀ = pre-f (eB , condB)
      
      T : Type _
      T = Σ[ i ∈ (GroupIso Agrp Bgrp) ] ((x : ⟨ G ⟩) (g : Ab⟨ A ⟩) → i .fst .fst g ≡ pre-f₀ x .fst .fst g )

      isContrT : isContr T
      isContrT = recPropTrunc isPropIsContr (λ x₀ → (pre-f₀ x₀ , λ x g → recPropTrunc (group-is-set Bgrp _ _)
        (λ p → cong (λ ok → pre-f₀ ok .fst .fst g) p) (gerbe-conn G x₀ x)) ,
        λ f → ΣProp≡ (λ x → isPropΠ λ x₁ → isPropΠ λ g → group-is-set Bgrp _ _)
        (groupIsoEq Agrp Bgrp _ _ (equivEq _ _ (funExt λ g → sym (snd f _ g))))) (gerbe-inhabited G)

    f : linked-by-ab G B → GroupIso Agrp Bgrp
    f x = fst (f₀ x)

    assocGroupComp : ∀ {ℓ ℓ' ℓ'' ℓ''' : Level} → (F : Group {ℓ}) (G : Group {ℓ'}) (H : Group {ℓ''}) (I : Group {ℓ'''})
      (f : GroupIso F G) (g : GroupIso G H) (h : GroupIso H I) →
      compGroupIso F G I f (compGroupIso G H I g h) ≡ compGroupIso F H I (compGroupIso F G H f g) h
    assocGroupComp F G H I f g h = groupIsoEq F I _ _ (equivEq _ _ refl)

    g : GroupIso Agrp Bgrp → linked-by-ab G B
    g i = eB , coherence where
      j = invGroupIso Agrp Bgrp i
  
      eB : (x : ⟨ G ⟩) → GroupIso Bgrp (AbGroup→Group (π G x))
      eB x = compGroupIso Bgrp Agrp (AbGroup→Group (π G x)) j (eA x)

      coherence : _
      coherence x y =
        sym (assocGroupComp Bgrp Agrp (AbGroup→Group (π G x)) (AbGroup→Group (π G y)) j (eA x) (S.s-iso G x y)) ∙
        cong (λ ok → compGroupIso Bgrp Agrp (AbGroup→Group (π G y)) j ok) (condA x y)

    abstract
      sec : section f g
      sec ((i , eq) , morph) = groupIsoEq Agrp Bgrp _ _ (equivEq _ _ (funExt λ a → recPropTrunc (group-is-set Bgrp _ _) (λ x →
        f (g ((i , eq) , morph)) .fst .fst a
          ≡⟨ snd (f₀ (g ((i , eq) , morph))) x a ⟩
        pre-f (g ((i , eq) , morph)) x .fst .fst a
          ≡⟨ refl ⟩
        i (invEq (fst (eA x)) (fst (eA x) .fst a))
          ≡⟨ cong i (secEq (fst (eA x)) a) ⟩
        i a ∎
        ) (gerbe-inhabited G)))
        
      invEquivCompEquiv : ∀ {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (e : A ≃ B) (f : B ≃ C) →
        invEquiv (compEquiv e f) ≡ compEquiv (invEquiv f) (invEquiv e)
      invEquivCompEquiv {A = A} e f = equivEq _ _ (funExt λ c → inj
        (_
          ≡⟨ retEq (compEquiv e f) c ⟩
        c
          ≡⟨ sym (retEq f c)  ⟩
        _
          ≡⟨ cong (f .fst) (sym (retEq e _)) ⟩
        _ ∎)
        ) where
        inj : {x y : A} → f .fst (e .fst x) ≡ f .fst (e .fst y) → x ≡ y
        inj {x} {y} = invEq (_ , (isEquiv→isEmbedding (compEquiv e f .snd) x y)) 

      retr : retract f g
      retr (eB , condB) =
        ΣProp≡ (λ e → isPropΠ2 λ x y → isSetGroupIso Bgrp (AbGroup→Group (π G y)) _ (e y))
        (funExt λ x → groupIsoEq Bgrp (AbGroup→Group (π G x)) _ _ (equivEq _ _ (funExt λ b →
          g (f (eB , condB)) .fst x .fst .fst b
            ≡⟨ refl ⟩
          eA x .fst .fst (invEq (fst (f (eB , condB))) b)
            ≡⟨ cong (λ U → eA x .fst .fst (invEq U b))
              (fst (f (eB , condB))
                ≡⟨ equivEq _ _ (funExt λ a → f₀ (eB , condB) .snd x a) ⟩
              fst (pre-f (eB , condB) x) ∎)
            ⟩
          eA x .fst .fst (invEq (fst (pre-f (eB , condB) x)) b)
            ≡⟨ refl ⟩
          compEquiv (invEquiv (compEquiv (fst (eA x)) (invEquiv (fst (eB x))))) (fst (eA x)) .fst b
            ≡⟨ cong (λ F → F .fst b) (
              compEquiv (invEquiv (compEquiv (fst (eA x)) (invEquiv (fst (eB x))))) (fst (eA x))
                ≡⟨ cong (λ F → compEquiv F (fst (eA x))) (invEquivCompEquiv (fst (eA x)) (invEquiv (fst (eB x)))) ⟩
              compEquiv (compEquiv (invEquiv (invEquiv (fst (eB x)))) (invEquiv (fst (eA x)))) (fst (eA x))
                ≡⟨ equivEq _ _ refl ⟩
              compEquiv (compEquiv (fst (eB x)) (invEquiv (fst (eA x)))) (fst (eA x))
                ≡⟨ equivEq _ _ refl ⟩
              compEquiv (fst (eB x)) (compEquiv (invEquiv (fst (eA x))) (fst (eA x)))
                ≡⟨ cong (compEquiv (fst (eB x))) (equivEq (compEquiv (invEquiv (fst (eA x))) (fst (eA x))) (idEquiv _) (funExt (retEq (fst (eA x))))) ⟩
              compEquiv (fst (eB x)) (idEquiv _)
                ≡⟨ equivEq _ _ refl ⟩
              fst (eB x) ∎)
            ⟩
          eB x .fst .fst b ∎
        )))
  
AbGroup-ua : (G G' : AbGroup {ℓ}) → GroupIso (AbGroup→Group G) (AbGroup→Group G') ≃ (G ≡ G')
AbGroup-ua = AbGroupPath

Π : (G : Gerbe {ℓ}) → Σ[ A ∈ AbGroup {ℓ} ] (linked-by-ab G A)
Π {ℓ} G = fst contr where
  type = Σ[ A ∈ AbGroup {ℓ} ] (linked-by-ab G A)
  type2 = λ (A : type) → Σ[ B ∈ AbGroup {ℓ} ] (GroupIso (AbGroup→Group (fst A)) (AbGroup→Group B))
  type3 = λ (A : type) → Σ[ B ∈ AbGroup {ℓ} ] (fst A ≡ B)
  
  type≃type2 : (A : type) → type ≃ type2 A
  type≃type2 (A , l) = congΣEquiv λ B → test G A l B
  
  type2≃type3 : (A : type) → type2 A ≃ type3 A
  type2≃type3 A = congΣEquiv λ B → AbGroup-ua (fst A) B

  isContr-type3 : (A : type) → isContr (type3 A)
  isContr-type3 A = (fst A , refl) , λ B → ΣPathP (snd B , λ i j → snd B (i ∧ j))

  contr : isContr type
  contr = recPropTrunc isPropIsContr
    (λ x₀ → isOfHLevelRespectEquiv 0 (invEquiv (
      compEquiv (type≃type2 (π G x₀ , link-by-π G x₀)) (type2≃type3 (π G x₀ , link-by-π G x₀))))
      (isContr-type3 (π G x₀ , link-by-π G x₀))
    )
    (fst (snd G))

B² : (AbGroup {ℓ}) → Type (ℓ-suc ℓ)
B² {ℓ} A = Σ[ G ∈ Gerbe {ℓ} ] (linked-by-ab G A)

module tests (A : AbGroup {ℓ}) (G : B² A) where
  B2 = B² A
  carac : (G G' : B2) → (G ≡ G') ≃ (Σ (fst G ≡ fst G') (λ p → PathP (λ i → linked-by-ab (p i) A) (snd G) (snd G')))
  carac G G' = invEquiv Σ≃

  ΣProp≡P : {ℓ ℓ' : Level} {A A' : Type ℓ} {B : A → Type ℓ'} {B' : A' → Type ℓ'}
    (p : A ≡ A') (q : PathP (λ i → p i → Type ℓ') B B') → (x : Σ A B) (y : Σ A' B') →
    PathP (λ i → Σ (p i) (q i)) x y → PathP (λ i → p i) (fst x) (fst y)
  ΣProp≡P p q x y s = λ i → fst (s i)
  
  ΣProp≡P2 : {ℓ ℓ' : Level} {A A' : Type ℓ} {B : A → Type ℓ'} {B' : A' → Type ℓ'}
    (p : A ≡ A') (q : PathP (λ i → p i → Type ℓ') B B') → (x : Σ A B) (y : Σ A' B') →
    ((i : I) (α : p i) → isProp (q i α)) →
    PathP (λ i → p i) (fst x) (fst y) → PathP (λ i → Σ (p i) (q i)) x y 
  ΣProp≡P2 p q x y prop s = λ i → (s i) , prop i (s i)
    (transp (λ j → q (i ∧ j) (s (i ∧ j))) (~ i) (snd x))
    (transp (λ j → q (i ∨ ~ j) (s (i ∨ ~ j))) i (snd y)) i

  ΣProp≃P : {ℓ ℓ' : Level} {A A' : Type ℓ} {B : A → Type ℓ'} {B' : A' → Type ℓ'}
    (p : A ≡ A') (q : PathP (λ i → p i → Type ℓ') B B') → (x : Σ A B) (y : Σ A' B') →
    ((i : I) (α : p i) → isProp (q i α)) →
    PathP (λ i → p i) (fst x) (fst y) ≃ PathP (λ i → Σ (p i) (q i)) x y
  ΣProp≃P {B' = B'} p q x y prop = isoToEquiv
    (iso
      (ΣProp≡P2 p q x y prop)
      (ΣProp≡P p q x y)
      (λ r i j → fst (r j) , right r i j )
      (λ r → refl)
    ) where
      right : (r : _) → (λ i → prop i (fst (r i))
        (transp (λ j → q (i ∧ j) (fst (r (i ∧ j)))) (~ i) (snd x))
        (transp (λ j → q (i ∨ ~ j) (fst (r (i ∨ ~ j)))) i (snd y)) i) ≡ λ i → snd (r i)
      right r = lemma _ _ where
        lemma : isProp (PathP (λ i → q i (fst (r i))) (snd x) (snd y))
        lemma = transport (cong isProp (sym (PathP≡Path _ _ _))) (isProp→isSet (prop i1 (fst y)) _ _)

  carac2 : (G G' : B2) →
    (Σ (fst G ≡ fst G') λ p → PathP (λ i → linked-by-ab (p i) A) (snd G) (snd G'))
      ≃
    (Σ (fst G ≡ fst G') λ p → PathP (λ i → (x : ⟨ p i ⟩) → GroupIso (AbGroup→Group A) (AbGroup→Group (π (p i) x))) (G .snd .fst) (G' .snd .fst))
  carac2 G G' = congΣEquiv λ p → invEquiv (ΣProp≃P _ _ _ _ λ i α → isPropΠ2 λ x y → isSetGroupIso (AbGroup→Group A) (AbGroup→Group (π (p i) y)) _ _ )

  --link-iso : (G G' : B2) → Type _
  --link-iso (G , e , _) (G' , f , _) = Σ[ p ∈ (⟨ G ⟩ ≃ ⟨ G' ⟩) ] ((x : ⟨ G ⟩) →  {!!} ≡ f (fst p x))
