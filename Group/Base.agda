{-# OPTIONS --cubical #-}

module ELib.Group.Base where

open import Cubical.Foundations.Prelude hiding (comp)

record GroupStruct {ℓ} (A : Type ℓ) : Type ℓ where
  constructor struct-group
  field
    set : isSet A
    id : A
    inv : A → A
    comp : A → A → A
    lUnit : (a : A) → a ≡ comp id a
    lCancel : (a : A) → comp (inv a) a ≡ id
    assoc : (a b c : A) → comp (comp a b) c ≡ comp a (comp b c)

  --private
  _⨀_ = comp
  
  simplL : (a : A) {b c : A} → a ⨀ b ≡ a ⨀ c → b ≡ c
  simplL a {b} {c} p = lUnit b ∙ cong (λ x → comp x b) (sym (lCancel a)) ∙ assoc _ _ _ ∙ cong (λ x → inv a ⨀ x) p ∙ (sym (assoc _ _ _)) ∙ cong (λ x → x ⨀ c) (lCancel a) ∙ sym (lUnit c)
  
  rCancel : (a : A) → a ⨀ (inv a) ≡ id
  rCancel a =
    a ⨀ inv a
      ≡⟨ lUnit _ ∙ cong (λ x → x ⨀ (a ⨀ inv a)) (sym (lCancel (inv a))) ⟩
    (inv (inv a) ⨀ inv a) ⨀ (a ⨀ inv a)
      ≡⟨ assoc _ _ _ ∙ cong (λ x → inv (inv a) ⨀ x) (sym (assoc _ _ _)) ⟩
    inv (inv a) ⨀ ((inv a ⨀ a) ⨀ inv a)
      ≡⟨ cong (λ x → inv (inv a) ⨀ x) (cong (λ x → x ⨀ inv a) (lCancel a) ∙ sym (lUnit (inv a))) ⟩
    inv (inv a) ⨀ (inv a)
      ≡⟨ lCancel (inv a) ⟩
    id ∎

  invInvo : (a : A) → inv (inv a) ≡ a
  invInvo a = simplL (inv a) (rCancel _ ∙ sym (lCancel _))

  rUnit : (a : A) → a ≡ a ⨀ id
  rUnit a = lUnit a ∙ cong (λ x → x ⨀ a) (sym (lCancel (inv a))) ∙ assoc _ _ _ ∙ λ i → (invInvo a i) ⨀ (lCancel a i)

  simplR : {a b : A} (c : A) → a ⨀ c ≡ b ⨀ c → a ≡ b
  simplR {a} {b} c p = rUnit a ∙ (cong (λ x → a ⨀ x) (sym (rCancel c))) ∙ sym (assoc _ _ _) ∙ cong (λ x → x ⨀ (inv c)) p ∙ assoc _ _ _ ∙ cong (λ x → b ⨀ x) (rCancel c) ∙ sym (rUnit b)

  invId : inv id ≡ id
  invId = simplL id (rCancel id ∙ lUnit id)

  idUniqueL : (e x : A) → e ⨀ x ≡ x → e ≡ id
  idUniqueL e x p = simplR x (p ∙ lUnit _)

  idUniqueR : (x e : A) → x ⨀ e ≡ x → e ≡ id
  idUniqueR x e p = simplL x (p ∙ rUnit _)

  invUniqueL : (g h : A) → g ⨀ h ≡ id → g ≡ inv h
  invUniqueL g h p = simplR h (p ∙ sym (lCancel h))

  invUniqueR : (g h : A) → g ⨀ h ≡ id → h ≡ inv g
  invUniqueR g h p = simplL g (p ∙ sym (rCancel g))

  diff : A → A → A
  diff a b = a ⨀ (inv b)

record Group ℓ : Type (ℓ-suc ℓ) where
  constructor group
  field
    type : Type ℓ
    struct : GroupStruct type

  open GroupStruct struct public

--open import Cubical.Foundations.Everything

isMorphism : {ℓ ℓ' : Level} (G : Group ℓ) (H : Group ℓ') → (Group.type G → Group.type H) → Type (ℓ-max ℓ ℓ')
isMorphism G H f = (x y : Group.type G) → f (Group.comp G x y) ≡ Group.comp H (f x) (f y)

Hom : {ℓ ℓ' : Level} (G : Group ℓ) (H : Group ℓ') → Type (ℓ-max ℓ ℓ')
Hom G H = Σ[ f ∈ (Group.type G → Group.type H) ] isMorphism G H f

homId : {ℓ ℓ' : Level} (G : Group ℓ) (H : Group ℓ') (f : Hom G H) → (fst f (Group.id G)) ≡ Group.id H
homId Ggrp Hgrp (f , morph) = H.simplL (f G.id) (
  f G.id H.⨀ f G.id
    ≡⟨ sym (morph G.id G.id) ⟩
  f (G.id G.⨀ G.id)
    ≡⟨ cong f (sym (G.lUnit _))  ⟩
  f G.id
    ≡⟨ H.rUnit _ ⟩
  f G.id H.⨀ H.id ∎) where
  module G = Group Ggrp
  module H = Group Hgrp

homInv : {ℓ ℓ' : Level} (G : Group ℓ) (H : Group ℓ')
  (f : Hom G H) (x : Group.type G) → fst f (Group.inv G x) ≡ Group.inv H (fst f x)
homInv Ggrp Hgrp f x = H.invUniqueL _ _ (sym (snd f (G.inv x) x) ∙ cong (fst f) (G.lCancel x) ∙ homId Ggrp Hgrp f ) where
  module G = Group Ggrp
  module H = Group Hgrp


------------------
open import Cubical.Homotopy.Loopspace
open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Sigma
open import ELib.UsefulLemmas

module B {ℓ : Level} (G : Group ℓ) where
  module Ggrp = Group G
  data B : Type ℓ where
    base : B
    path : Ggrp.type → base ≡ base
    id : path Ggrp.id ≡ refl
    conc : (g h : Ggrp.type) → path g ∙ path h ≡ path (Group.comp G g h)
    groupoid : (p q : base ≡ base) (r s : p ≡ q) → r ≡ s


  elimBprop : (P : B → Type ℓ) → ((b : B) → isProp (P b)) → P base → (b : B) → P b
  elimBprop P Pprop pnt base = pnt
  elimBprop P Pprop pnt (path g i) = toPathP {A = λ i → P (path g i)} {x = pnt} {y = pnt} (Pprop base _ _) i
  elimBprop P Pprop pnt (id i j) = isOfHLevel→isOfHLevelDep 2 {B = P} (λ b → isProp→isSet (Pprop b)) pnt pnt
    (toPathP {A = λ i → P (path (Ggrp.id) i)} (Pprop base _ _))
    refl id i j
  elimBprop P Pprop pnt (conc g h i j) = isOfHLevel→isOfHLevelDep 2 {B = P} (λ b → isProp→isSet (Pprop b)) pnt pnt
    (transport {!λ i → PathP (λ j → (cong-∙ P (path g) (path h) (~ i)) j) pnt pnt!}
    (compPathP (cong (elimBprop P Pprop pnt) (path g)) (cong (elimBprop P Pprop pnt) (path h)))) (cong (elimBprop P Pprop pnt) (path (Ggrp.comp g h))) (conc g h) i j
  --elimBprop P Pprop pnt (conc g h i j) = isOfHLevel→isOfHLevelDep 2 {B = P} ((λ b → isProp→isSet (Pprop b))) pnt pnt
  --  ({!!}) ((toPathP {A = λ i → P (path (Ggrp.comp g h) i)} (Pprop base _ _))) (conc g h) i j
  elimBprop P Pprop pnt (groupoid p q r s i j k) = isOfHLevel→isOfHLevelDep 3 {B = P} (λ b → isSet→isGroupoid (isProp→isSet (Pprop b)))
    pnt pnt
    (cong (elimBprop P Pprop pnt) p) (cong (elimBprop P Pprop pnt) q)
    (cong (cong (elimBprop P Pprop pnt)) r) (cong (cong (elimBprop P Pprop pnt)) s)
    (groupoid p q r s) i j k

  {-set : (b : B) → isSet ∥ b ≡ base ∥
  set b = isProp→isSet propTruncIsProp
  isConnectedB : (b : B) → ∥ b ≡ base ∥
  isConnectedB base = ∣ refl ∣
  isConnectedB (path g i) = toPathP {A = λ i → ∥ path g i ≡ base ∥} {x = ∣ refl ∣} {y = ∣ refl ∣} (propTruncIsProp _ _) i
  --isConnectedB (path g i) = toPathP {A = λ i → ∥ path g i ≡ base ∥} {x = ∣ refl ∣} {y = ∣ refl ∣} (squash _ _) i
  --isConnectedB (id i j) = test i j where --set (id i j) {!!} {!refl!} {!!} {!!} j i where
  --  wesh : PathP (λ i → ∥ path Ggrp.id i ≡ base ∥) ∣ refl ∣ ∣ refl ∣
  --  wesh = toPathP {A = λ i → ∥ path Ggrp.id i ≡ base ∥} {x = ∣ refl ∣} {y = ∣ refl ∣} (squash _ _)
  --  test : PathP (λ i → PathP (λ j → ∥ id i j ≡ base ∥) ∣ refl ∣ ∣ refl ∣) wesh refl
  --  test = toPathP (set base _ _ (transport (λ i → PathP (λ j → ∥ id i j ≡ base ∥) ∣ refl ∣ ∣ refl ∣) wesh) _)
  --isConnectedB (conc g h i j) = {!!}
  --isConnectedB (groupoid p q r s i j k) = {!!}-}

  G→ΩBG : Group.type G → fst (Ω (B , base))
  G→ΩBG g = path g

  private
    _⨀_ = Ggrp.comp
    inv = Ggrp.inv
    codeBase : Type ℓ
    codeBase = Ggrp.type
    codePath : Ggrp.type → codeBase ≡ codeBase
    codePath g =
      isoToPath (iso (λ x → x ⨀ g ) (λ x → x ⨀ inv g)
        (λ x → Ggrp.assoc _ _ _ ∙ cong (λ y → x ⨀ y) (Ggrp.lCancel g) ∙ sym (Ggrp.rUnit x))
        (λ x → Ggrp.assoc _ _ _ ∙ cong (λ y → x ⨀ y) (Ggrp.rCancel g) ∙ sym (Ggrp.rUnit x)))
    codeId : codePath Ggrp.id ≡ refl
    codeId = cong ua (equivEq _ _ (funExt λ x → sym (Ggrp.rUnit x))) ∙ uaIdEquiv
    codeConc : (g h : codeBase) → codePath g ∙ codePath h ≡ codePath (Ggrp.comp g h)
    codeConc g h = sym (uaCompEquiv _ _) ∙ cong ua (equivEq _ _ (funExt λ x → Ggrp.assoc _ _ _))
    codeGroupoid : (p q : codeBase ≡ codeBase) (r s : p ≡ q) → r ≡ s
    codeGroupoid = isOfHLevel≡ 2 Ggrp.set Ggrp.set
  code : B → Type ℓ
  code base = codeBase
  code (path g i) = codePath g i
  code (id i j) = codeId i j
  code (conc g h i j) = codeConc g h i j
  code (groupoid p q r s i j k) = codeGroupoid (cong code p) (cong code q) (cong (cong code) r) (cong (cong code) s) i j k

  encode : (b : B) → base ≡ b → code b
  encode b p = transport (cong code p) Ggrp.id

  transport→ : ∀ {ℓ} (A : Type ℓ) (B C : A → Type ℓ) (a a' : A) (p : a ≡ a') (f : B a → C a) →
    transport (λ i → B (p i) → C (p i)) f ≡ λ x → transport (λ i → C (p i)) (f (transport (λ i → B (p (~ i))) x))
  transport→ A B C a a' p = J
    (λ a' p → (f : B a → C a) → transport (λ i → B (p i) → C (p i)) f ≡ λ x → transport (λ i → C (p i)) (f (transport (λ i → B (p (~ i))) x)))
    (λ f → transportRefl f ∙ funExt λ x → sym (transportRefl _ ∙ cong f (transportRefl _)))
    p
  transport≡p : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : y ≡ z) (q : x ≡ y) → transport (λ i → x ≡ (p i)) q ≡ q ∙ p
  transport≡p {ℓ} {A} {x} p q = J (λ C p → transport (λ i → x ≡ (p i)) q ≡ q ∙ p) (transportRefl q ∙ rUnit q) p

  transport≡pathToEquiv : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) → transport p ≡ fst (pathToEquiv p)
  transport≡pathToEquiv p = funExt λ x → refl

  {-decode : (b : B) → code b → base ≡ b
  decode base = path
  decode (path g i) = test i where
    test : PathP (λ i → code (path g i) → base ≡ path g i) path path
    test = toPathP (
      (transport (λ i → code (path g i) → (base ≡ path g i)) path)
        ≡⟨ transport→ B code (λ x → base ≡ x) base base (path g) path ⟩
      ((λ x → transport (λ i → base ≡ path g i) (path (transport (λ i → code (path g (~ i))) x))))
        ≡⟨ (funExt λ x → transport≡p (path g) (path (transport (λ i₁ → code (path g (~ i₁))) x)) ∙
          cong (λ y → path (y ⨀ Ggrp.inv g) ∙ path g) (transportRefl _) ∙
          conc _ _ ∙ cong path (Ggrp.assoc _ _ _ ∙ cong (λ y → x ⨀ y) (Ggrp.lCancel g) ∙ (sym (Ggrp.rUnit x))) ) ⟩
      path ∎)
  decode (id i j) = {!!} where
    test : (b : B) → isSet (code b → base ≡ b)
    test b = isSetΠ λ _ → {!!}
  decode (conc g h i j) = {!!}
  decode (groupoid p q r s i j k) = {!!}-}

  ΩBG→G : fst (Ω (B , base)) → Ggrp.type
  ΩBG→G = encode base


------------------
--open import Cubical.Foundations.Everything

--G-Setᵃᵇˢ : ∀ {ℓ} → Group ℓ → Type (ℓ-suc ℓ)
--G-Setᵃᵇˢ {ℓ} Ggrp = Σ[ χ ∈ (hSet ℓ) ] Hom Ggrp {!!}
