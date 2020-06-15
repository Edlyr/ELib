{-# OPTIONS --cubical #-}

module ELib.Gerbe.Link where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc ; elim to elimPropTrunc)
open import Cubical.Structures.Group hiding (⟨_⟩)
open import Cubical.Structures.AbGroup renaming (⟨_⟩ to Ab⟨_⟩)
open import ELib.Group.Morphism
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import ELib.UsefulLemmas
open import ELib.Gerbe.Base
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

private
  variable
    ℓ ℓ' ℓ'' : Level
    
GRP = AbGroup→Group

linked-by-ab : (G : Gerbe {ℓ}) (A : AbGroup {ℓ'}) → Type (ℓ-max ℓ ℓ')
linked-by-ab {ℓ} {ℓ'} G Aab = Σ[ e ∈ ((x : ⟨ G ⟩) → GroupIso A (AbGroup→Group (π G x))) ]
  ((x y : ⟨ G ⟩) → compGroupIso A (H x) (H y) (e x) (s-iso x y) ≡ e y) where
  open S G
  A = AbGroup→Group Aab
  H : (x : _) → _
  H x = AbGroup→Group (π G x)

linkStructure : (A : AbGroup {ℓ'}) → Type ℓ → Type _
linkStructure {ℓ} A = add-to-structure isGerbe (λ X gerbe → linked-by-ab (X , gerbe) A)

B² : {ℓ : Level} → (A : AbGroup {ℓ'}) → Type _
B² {ℓ} A = TypeWithStr ℓ (linkStructure A)

linkHom : ∀ {ℓ ℓ'} → (A : AbGroup {ℓ}) → StrHom {ℓ = ℓ'} (linkStructure A) _
linkHom A (X₁ , gerbe₁ , l₁ , _) (X₂ , gerbe₂ , l₂ , _) f =
  (x : X₁) → cong f ∘ (l₁ x .fst .fst) ≡ l₂ (f x) .fst .fst

linkIso : ∀ {ℓ ℓ'} → (A : AbGroup {ℓ}) → StrIso {ℓ = ℓ'} (linkStructure A) _
linkIso A = StrHom→StrIso (linkHom A)

abstract
  linkSNS-≡ : (A : AbGroup {ℓ}) → SNS-≡ {ℓ₁ = ℓ'} (linkStructure A) (linkIso A)
  linkSNS-≡ A {X} (gerbe₁ , l₁) (gerbe₂ , l₂) = transport path (test gerbe₂ l₁' l₂) where
    p : gerbe₁ ≡ gerbe₂
    p = isPropIsGerbe X _ _
    l₁' : _
    l₁' = transp (λ i → linked-by-ab (X , p i) A) i0 l₁
  
    ok : (gerbe : isGerbe X) (l : linked-by-ab (X , gerbe) A) → linkStructure A X
    ok gerbe l = (gerbe , l)
    
    wesh : ok gerbe₁ l₁ ≡ ok gerbe₂ l₁'
    wesh i = ok (p i) (transp (λ j → linked-by-ab (X , p (i ∧ j)) A) (~ i) l₁)
    
    path :
      ((linkIso A (X , gerbe₂ , l₁') (X , gerbe₂ , l₂) (idEquiv X)) ≃ (ok gerbe₂ l₁' ≡ ok gerbe₂ l₂)) ≡
      ((linkIso A (X , gerbe₁ , l₁ ) (X , gerbe₂ , l₂) (idEquiv X)) ≃ (ok gerbe₁ l₁ ≡ ok gerbe₂ l₂))
    path i = (linkIso A (X , wesh (~ i)) (X , gerbe₂ , l₂) (idEquiv X)) ≃ (wesh (~ i) ≡ ok gerbe₂ l₂)
  
    π₁ : (x : X) → Group
    π₁ x = GRP (π (X , gerbe₁) x)
  
    test : (gerbe : isGerbe X) (l₁ l₂ : linked-by-ab (X , gerbe) A) →
      linkIso A (X , gerbe , l₁) (X , gerbe , l₂) (idEquiv X) ≃ (ok gerbe l₁ ≡ ok gerbe l₂)
    test gerbe l₁ l₂ = isoToEquiv (iso Iso→≡ ≡→Iso sec retr) where
      Iso→≡  : linkIso A (X , gerbe , l₁) (X , gerbe , l₂) (idEquiv X) → ok gerbe l₁ ≡ ok gerbe l₂
      Iso→≡ link-iso = ΣPathP (refl , ΣProp≡
        (λ _ → isPropΠ2 λ _ y → isSetGroupIso (GRP A) (π₁ y) _ _)
        (funExt λ x → groupIsoEq (GRP A) (π₁ x) _ _ (equivEq _ _ (link-iso x)))
       )
  
      ≡→Iso : ok gerbe l₁ ≡ ok gerbe l₂ → linkIso A (X , gerbe , l₁) (X , gerbe , l₂) (idEquiv X)
      ≡→Iso p x i = snd (p i) .fst x .fst .fst
  
      isSetLinkStructure : isSet (linkStructure A X)
      isSetLinkStructure =
        isSetΣ (isProp→isSet (isPropIsGerbe X)) λ gerbe →
        isSetΣ
          (isSetΠ λ x → isSetGroupIso (GRP A) (π₁ x))
          λ f → isSetΠ2 λ y z → isProp→isSet (isSetGroupIso (GRP A) (π₁ z) _ _)
  
      sec : section Iso→≡ ≡→Iso
      sec p = isSetLinkStructure _ _ _ _
  
      isPropLinkIso : isProp (linkIso A (X , gerbe , l₁) (X , gerbe , l₂) (idEquiv X))
      isPropLinkIso = isPropΠ λ x → isSetΠ (λ g → gerbe-grpd (X , gerbe) _ _) _ _
  
      retr : retract Iso→≡ ≡→Iso
      retr link-iso = isPropLinkIso _ _

  linkSNS : (A : AbGroup {ℓ}) → SNS {ℓ₁ = ℓ'} (linkStructure A) (linkIso A)
  linkSNS A = SNS-≡→SNS-PathP (linkIso A) (linkSNS-≡ A)

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


open import ELib.ConcreteGroup.Base
open import ELib.ConcreteGroup.DeloopMorph

module _ (A : AbGroup {ℓ'}) (G : B² {ℓ'} {ℓ} A) where
  X = fst G
  gerbe : Gerbe
  gerbe = (fst G , fst (snd G))
  link = snd (snd G)
  l = fst (link)
  equiv1 : Σ (fst G ≃ fst G) (λ f → (x : X) → cong (fst f) ∘ l x .fst .fst ≡ l (fst f x) .fst .fst) ≃ (G ≡ G)
  equiv1 = SIP (linkSNS A) G G

  equiv2 : (f : fst G ≃ fst G) → ((x : X) → cong (fst f) ∘ l x .fst .fst ≡ l (fst f x) .fst .fst) ≃ ∥ idEquiv X ≡ f ∥
  equiv2 f = isoToEquiv (iso fun→ fun← sec retr) where
    fun← : ∥ idEquiv X ≡ f ∥ → ((x : X) → cong (fst f) ∘ l x .fst .fst ≡ l (fst f x) .fst .fst)
    fun← = recPropTrunc (isPropΠ λ x → isSetΠ (λ g → gerbe-grpd gerbe _ _) _ _)
      λ p x → transport (λ i → cong (fst (p i)) ∘ l x .fst .fst ≡ l (fst (p i) x) .fst .fst) refl

    fun→ : ((x : X) → cong (fst f) ∘ l x .fst .fst ≡ l (fst f x) .fst .fst) → ∥ idEquiv X ≡ f ∥
    fun→ prop =
      recPropTrunc propTruncIsProp (λ x₀ → recPropTrunc propTruncIsProp (λ p₀ → ∣ lemma x₀ p₀ ∣)
      (gerbe-conn gerbe x₀ (fst f x₀))) (gerbe-inhabited gerbe)
      where
      s : (x y : X) → _
      s x y = S.s-iso gerbe x y .fst .fst
      sf : (x : X) → _
      sf x = S.s-iso gerbe x (fst f x) .fst .fst

      cong-f : (x : X) → (x ≡ x) → ((fst f x) ≡ (fst f x))
      cong-f x = cong (fst f)

      carac-cong-f : (x : X) → cong-f x ≡ sf x
      carac-cong-f x = invEquiv (_ , isEquiv→isEmbedding (isEquivPreComp (l x .fst)) (cong-f x) (sf x)) .fst (pre-carac2 x) where
        pre-carac1 : (x : X) → sf x ∘ (l x .fst .fst) ≡ l (fst f x) .fst .fst
        pre-carac1 x = cong fst (cong fst (snd link x (fst f x)))
        pre-carac2 : (x : X) → (cong-f x) ∘ (l x .fst .fst) ≡ sf x ∘ (l x .fst .fst)
        pre-carac2 x = (prop x) ∙ sym (pre-carac1 x)

      lemma : (x₀ : ⟨ gerbe ⟩) (p₀ : x₀ ≡ fst f x₀) → idEquiv X ≡ f
      lemma x₀ p₀ = equivEq _ _ (funExt id≡f) where
        CG : ConcreteGroup _
        CG = conc-group X (struct-conc-group x₀ (gerbe-conn gerbe x₀) (gerbe-grpd gerbe x₀ x₀))
        morph-id : GroupHom (abs CG) (abs CG)
        morph-id = (λ x → x) , λ x y → refl

        f-is-deloop : (x : X) → delooping CG CG morph-id x
        f-is-deloop x = fst f x , (λ q → p₀ ∙ cong (fst f) q) , λ ω α →
          p₀ ∙ cong (fst f) (ω ∙ α)
            ≡⟨ cong (p₀ ∙_) (cong-∙ (fst f) _ _) ⟩
          p₀ ∙ cong-f x₀ ω ∙ cong (fst f) α
            ≡⟨ cong (λ r → p₀ ∙ r ∙ cong (fst f) α) (λ i → carac-cong-f x₀ i ω) ⟩
          p₀ ∙ sf x₀ ω ∙ cong (fst f) α
            ≡⟨ assoc _ _ _ ⟩
          (p₀ ∙ sf x₀ ω) ∙ cong (fst f) α
            ≡⟨ cong (λ r → (p₀ ∙ r) ∙ cong (fst f) α) (S.s gerbe x₀ (fst f x₀) .snd p₀ ω) ⟩
          (p₀ ∙ sym p₀ ∙ ω ∙ p₀) ∙ cong (fst f) α
            ≡⟨ cong (_∙ cong (fst f) α) (compPathl-cancel p₀ (ω ∙ p₀)) ⟩
          (ω ∙ p₀) ∙ cong (fst f) α
            ≡⟨ sym (assoc _ _ _) ⟩
          ω ∙ p₀ ∙ cong (fst f) α ∎
        id-is-deloop : (x : X) → delooping CG CG morph-id x
        id-is-deloop x = x , (λ p → p) , λ _ _ → refl

        id≡f : (x : X) → x ≡ fst f x
        id≡f x = cong fst (isContr→isProp (deloopingContr CG CG morph-id x) (id-is-deloop x) (f-is-deloop x))

    sec : section fun→ fun←
    sec _ = propTruncIsProp _ _

    retr : retract fun→ fun←
    retr _ = isPropΠ (λ _ → isSetΠ (λ _ → gerbe-grpd gerbe _ _) _ _) _ _

  ZG : Type ℓ'
  ZG = Σ[ f ∈ X ≃ X ] ∥ idEquiv X ≡ f ∥

  B²Path≃ZG : (G ≡ G) ≃ ZG
  B²Path≃ZG = compEquiv (invEquiv equiv1) (congΣEquiv equiv2)
  
  

-------------------
{-
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
-}
