module common where

infixr 5 _∷_
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

[_] : {A : Set} → A → List A
[ x ] = x ∷ []

infixr 4 _++_
_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

rev-app : {A : Set} → List A → List A → List A
rev-app [] ys = ys
rev-app (x ∷ xs) ys = rev-app xs (x ∷ ys)

rev : {A : Set} → List A → List A
rev xs = rev-app xs []

infix 20 _≡_
data _≡_ {A : Set} : A → A → Set where
 refl : {x : A} → x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

cong : {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

cong2 : {A B C : Set} {x x' : A} {y y' : B} (f : A → B → C) → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong2 f refl refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

subst : {A : Set} (P : A → Set) {x y : A} → P x → x ≡ y → P y
subst P px refl = px

subst2 : {A B : Set} (P : A → B → Set) {x x' : A} {y y' : B} → P x y → x ≡ x' → y ≡ y' → P x' y'
subst2 P pxy refl refl = pxy

++-neutral-r : {A : Set} (xs : List A) → (xs ++ []) ≡ xs
++-neutral-r [] = refl
++-neutral-r (x ∷ xs) = cong (x ∷_) (++-neutral-r xs)

++-assoc : {A : Set} (xs ys zs : List A) → ((xs ++ ys) ++ zs) ≡ (xs ++ ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : {x : A} {xs : List A} (px : P x) (pxs : All P xs) → All P (x ∷ xs)

data Nat : Set where
  Z : Nat
  S : Nat → Nat

infix 20 _<_
data _<_ : Nat → Nat → Set where
  Z<S : {n : Nat} → Z < S n
  S<S : {n m : Nat} → n < m → S n < S m

<-unique : {n m : Nat} → (p q : n < m) → p ≡ q
<-unique Z<S Z<S = refl
<-unique (S<S p) (S<S q) = cong S<S (<-unique p q)

<-unique' : {n m : Nat} → {p q : n < m} → p ≡ q
<-unique' {n} {m} {p} {q} = <-unique {n} {m} p q

Sn<Sm→n<m : {n m : Nat} → S n < S m → n < m
Sn<Sm→n<m (S<S n<m) = n<m

n<Sn : {n : Nat} → n < S n
n<Sn {Z} = Z<S
n<Sn {S n} = S<S n<Sn

n<m→n<Sm : {n m : Nat} → n < m → n < S m
n<m→n<Sm Z<S = Z<S
n<m→n<Sm (S<S n<m) = S<S (n<m→n<Sm n<m)

Sn<m→n<m : {n m : Nat} → S n < m → n < m
Sn<m→n<m (S<S n<pred-m) = n<m→n<Sm n<pred-m

<-trans : {n m k : Nat} → n < m → m < k → n < k
<-trans Z<S (S<S m<k) = Z<S
<-trans (S<S n<m) (S<S m<k) = S<S (<-trans n<m m<k)

infix 20 _≤_
_≤_ : Nat → Nat → Set
n ≤ m = n < S m

n≤n : {n : Nat} → n ≤ n
n≤n = n<Sn

n<m→n≤m : {n m : Nat} → n < m → n ≤ m
n<m→n≤m Z<S = Z<S
n<m→n≤m (S<S n<m) = S<S (n<m→n≤m n<m)

pred : Nat → Nat
pred Z = Z
pred (S n) = n

infixl 20 _+_
_+_ : Nat → Nat → Nat
Z + m = m
(S n) + m = S (n + m)

+-neutral-r : {n : Nat} → (n + Z) ≡ n
+-neutral-r {Z} = refl
+-neutral-r {S n} = cong S +-neutral-r

+-suc-shift : {n m : Nat} → (n + S m) ≡ S (n + m)
+-suc-shift {Z} = refl
+-suc-shift {S n} = cong S +-suc-shift

add-monotone : {n m : Nat} → n < S (m + n)
add-monotone {n} {Z} = n<Sn
add-monotone {n} {S m} = n<m→n<Sm add-monotone


infixl 20 _-_
_-_ : Nat → Nat → Nat
Z - m = Z
S n - Z = S n
S n - S m = n - m

n-n=Z : {n : Nat} → (n - n) ≡ Z
n-n=Z {Z} = refl
n-n=Z {S n} = n-n=Z {n}

minus-Z-l : {n : Nat} → (Z - n) ≡ Z
minus-Z-l = refl

minus-Z-r : {n : Nat} → (n - Z) ≡ n
minus-Z-r {Z} = refl
minus-Z-r {S n} = refl

Sn-n=SZ : {n : Nat} → (S n - n) ≡ S Z
Sn-n=SZ {Z} = refl
Sn-n=SZ {S n} = Sn-n=SZ {n}

minus-S : (n m : Nat) → (n - S m) ≡ pred (n - m)
minus-S Z Z = refl
minus-S Z (S m) = refl
minus-S (S n) Z = minus-Z-r
minus-S (S n) (S m) = minus-S n m

minus-monotone : {n m k : Nat} → n < m → (n - k) < m
minus-monotone {n} {m} {k} Z<S = Z<S
minus-monotone {n} {m} {Z} (S<S n<m) = S<S n<m
minus-monotone {S n} {S m} {S k} (S<S n<m) = minus-monotone (n<m→n<Sm n<m)

minus-shift-suc-l : {m n : Nat} → m < n → (S n - m) ≡ S (n - m)
minus-shift-suc-l {Z} {S n} Z<S = refl
minus-shift-suc-l {S m} {S n} (S<S m<n) = minus-shift-suc-l m<n

minus-shift-suc-r : {m n : Nat} → m < n → (n - m) ≡ S (n - m - S Z)
minus-shift-suc-r Z<S = cong S (sym (minus-Z-r))
minus-shift-suc-r (S<S m<n) = minus-shift-suc-r m<n

mirror : Nat → Nat → Nat
mirror N i = N - S Z - i

mirror-le : {N i : Nat} → i < N → (mirror N i) < N
mirror-le {(S Z)} Z<S = subst (_< S Z) n<Sn refl
mirror-le {(S (S N))} Z<S = subst (_< S (S N)) n<Sn refl
mirror-le {(S (S N))} {S i} (S<S i<N) =
  let n-i<ssn : (N - i) < S (S N)
      n-i<ssn = minus-monotone {N} {S (S N)} {i} (n<m→n<Sm n<Sn)
   in n-i<ssn

postulate mirror-involutive : (N i : Nat) → i < N → (mirror N (mirror N i)) ≡ i
 
length : {A : Set} → List A → Nat
length [] = Z
length (_ ∷ xs) = S (length xs)

++-length : {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ (length xs + length ys)
++-length [] ys = refl
++-length (x ∷ xs) ys = cong S (++-length xs ys)

infix 4 _∈_
_∈_ : {A : Set} → A → List A → Set
_∈_ x = Any (x ≡_)

∈-++-l : {A : Set} {z : A} {xs ys : List A} → z ∈ xs → z ∈ (xs ++ ys)
∈-++-l (here refl) = here refl
∈-++-l (there z∈xs) = there (∈-++-l z∈xs)

∈-++-r : {A : Set} {z : A} {xs ys : List A} → z ∈ ys → z ∈ (xs ++ ys)
∈-++-r {xs = []} z∈ys = z∈ys
∈-++-r {xs = x ∷ xs} z∈ys = there (∈-++-r z∈ys)

rev-app-app : {A : Set} (xs ys zs : List A) → (rev-app xs (ys ++ zs)) ≡ ((rev-app xs ys) ++ zs)
rev-app-app [] ys zs = refl
rev-app-app (x ∷ xs) ys zs = rev-app-app xs (x ∷ ys) zs

∈-rev-app : {A : Set} {x : A} {xs ys : List A} → x ∈ xs → x ∈ rev-app xs ys
∈-rev-app {A} {z} {z ∷ []} (here refl) = here refl
∈-rev-app {A} {z} {z ∷ x ∷ xs} {ys} (here refl) with sym (rev-app-app xs (x ∷ []) (z ∷ ys))
... | eq = subst (z ∈_ ) (∈-++-r (here refl)) eq
∈-rev-app {A} {z} {x ∷ xs} (there mem) = ∈-rev-app mem

∈-rev : {A : Set} {x : A} {xs : List A} → x ∈ xs → x ∈ rev xs
∈-rev = ∈-rev-app

rev-rev-lemma : {A : Set} (xs ys zs : List A) → (rev-app (rev-app xs ys) zs) ≡ ((rev-app ys xs) ++ zs)
rev-rev-lemma [] ys zs = rev-app-app ys [] zs
rev-rev-lemma (x ∷ xs) ys zs = rev-rev-lemma xs (x ∷ ys) zs

rev-involutive : {A : Set} (xs : List A) → rev (rev xs) ≡ xs
rev-involutive xs = trans (rev-rev-lemma xs [] []) (++-neutral-r xs)

rev-app-length : {A : Set} {xs ys : List A} → length (rev-app xs ys) ≡ (length xs + length ys)
rev-app-length {A} {[]} = refl
rev-app-length {A} {x ∷ xs} {ys} = let IH = rev-app-length {xs = xs} {x ∷ ys}
                                    in trans IH +-suc-shift

rev-length : {A : Set} {xs : List A} → length (rev xs) ≡ length xs
rev-length {A} {xs} = let len-xs+[] = rev-app-length {A} {xs} {[]}
                       in trans len-xs+[] +-neutral-r

All-∈ : {A : Set} {P : A → Set} {x : A} {xs : List A} → All P xs → x ∈ xs → P x
All-∈ (px ∷ _) (here refl) = px
All-∈ (_ ∷ all) (there mem) = All-∈ all mem

infix 4 _⊆_
_⊆_ : {A : Set} → List A → List A → Set
_⊆_ {A} xs ys = {z : A} → z ∈ xs → z ∈ ys

∷-subset : {A : Set} {z : A} {xs ys : List A} → xs ⊆ ys → z ∷ xs ⊆ z ∷ ys
∷-subset {A} {z} xs⊆ys (here eq) = here eq
∷-subset {A} {z} xs⊆ys (there mem) = there (xs⊆ys mem)

data Empty : Set where

record Unit : Set where
  constructor unit

infix 4 ¬_
¬_ : Set → Set
¬ A = A → Empty

infix 20 _≢_
_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

absurd : {A : Set} → Empty → A
absurd ()

record _⇔_ (A B : Set) : Set where
  field
    ⇒ : A → B
    ⇐ : B → A

map : {A B : Set} (f : A → B) (xs : List A) → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

map-length : {A B : Set} {f : A → B} {xs : List A} → length (map f xs) ≡ length xs
map-length {xs = []} = refl
map-length {xs = x ∷ xs} = cong S map-length

∈-map : {A B : Set} {f : A → B} {z : A} {xs : List A} → z ∈ xs → f z ∈ map f xs
∈-map (here refl) = here refl
∈-map (there z∈xs) = there (∈-map z∈xs)

∘-map : {A B C : Set} (f : A → B) (g : B → C) {xs : List A} → map (λ x → g (f x)) xs ≡ map g ((map f) xs)
∘-map f g {[]} = refl
∘-map f g {x ∷ xs} = cong ((g (f x)) ∷_) (∘-map f g)

map-ext : {A B : Set} (f g : A → B) (f=g : (x : A) → f x ≡ g x)
        → {xs : List A} → map f xs ≡ map g xs
map-ext f g f=g {[]} = refl
map-ext f g f=g {x ∷ xs} = cong2 _∷_ (f=g x) (map-ext f g f=g {xs})

map-id : {A : Set} {xs : List A} → map (λ x → x) xs ≡ xs
map-id {xs = []} = refl
map-id {xs = x ∷ xs} = cong (x ∷_) map-id

infixr 15 _⊎_
data _⊎_ (A B : Set) : Set where
  left  : (x : A) → A ⊎ B
  right : (y : B) → A ⊎ B

record Σ {A : Set} (B : A → Set) : Set where
  constructor ⟨_,_⟩
  field
    fst : A
    snd : B fst

infixr 15 _×_
_×_ : Set → Set → Set
A × B = Σ (λ (_ : A) → B)

data Maybe (A : Set) : Set where
  Just : (a : A) → Maybe A
  Nothing : Maybe A

fmap : {A B : Set} (f : A → B) → Maybe A → Maybe B
fmap f (Just a) = Just (f a)
fmap f Nothing = Nothing

IsJust : {A : Set} → Maybe A → Set
IsJust (Just _) = Unit
IsJust Nothing = Empty

fromJust : {A : Set} → (m : Maybe A) → IsJust m → A
fromJust (Just x) _ = x

fromJust-just : {A : Set} {m : Maybe A} {x : A}
              → m ≡ Just x
              → (isj : IsJust m)
              → fromJust m isj ≡ x
fromJust-just refl isj = refl


_!_ : {A : Set} → List A → Nat → Maybe A
[] ! n = Nothing
(x ∷ xs) ! Z = Just x
(x ∷ xs) ! S n = xs ! n

valid-index : {A : Set} {xs : List A} {n : Nat} (n<N : n < (length xs)) → IsJust (xs ! n)
valid-index {xs = x ∷ xs} {Z} n<N = unit
valid-index {xs = x ∷ xs} {S N} (S<S n<N) = valid-index n<N

mem→idx : {A : Set} {x : A} {xs : List A} → x ∈ xs → Σ (λ n → (xs ! n) ≡ Just x)
mem→idx (here refl) = ⟨ Z , refl ⟩
mem→idx {A} {x} {y ∷ xs} (there x∈xs) = let ⟨ idx , eq ⟩ = mem→idx x∈xs in ⟨ S idx , eq ⟩

idx→mem : {A : Set} {x : A} {xs : List A} → Σ (λ n → (xs ! n) ≡ Just x) → x ∈ xs
idx→mem {xs = x ∷ _} ⟨ Z , refl ⟩ = here refl
idx→mem {xs = x ∷ xs} ⟨ S idx , eq ⟩ = there (idx→mem ⟨ idx , eq ⟩)

data Bool : Set where
  True  : Bool
  False : Bool

Fin : Nat → Set
Fin N = Σ λ n → n < N

enum-desc : {N : Nat} (n : Nat) → n < N → List (Fin N)
enum-desc Z Z<S = [ ⟨ Z , Z<S ⟩ ]
enum-desc (S n) Sn<N = ⟨ S n , Sn<N ⟩ ∷ enum-desc n (Sn<m→n<m Sn<N)

enum-desc-len : {N : Nat} (n : Nat) (n<N : n < N) → length (enum-desc n n<N) ≡ S n
enum-desc-len Z Z<S = refl
enum-desc-len (S n) Sn<N = let IH = enum-desc-len n (Sn<m→n<m Sn<N) in cong S IH

enum-desc-idx : {N : Nat}
              → (n : Nat) → (n<N : n < N)
              → (i : Nat) → (i≤n : i ≤ n)
              → ((enum-desc n n<N) ! i) ≡ Just ⟨ n - i , minus-monotone n<N ⟩
enum-desc-idx Z Z<S Z i≤n = refl
enum-desc-idx Z Z<S (S i) (S<S ())
enum-desc-idx (S n) (S<S n<N) Z i≤n = refl
enum-desc-idx (S n) (S<S n<N) (S i) (S<S i≤n) = let n<ₐN = n<m→n<Sm n<N in enum-desc-idx n n<ₐN i i≤n

enumerate : (N : Nat) → List (Fin N)
enumerate Z = []
enumerate N@(S M) = enum-desc M n<Sn

enumerate-index : (N i : Nat) (i<N : i < N) → (enumerate N ! i) ≡ Just ⟨ mirror N i , mirror-le i<N ⟩
enumerate-index (S Z) Z Z<S = refl
enumerate-index (S Z) (S i) (S<S ())
enumerate-index (S (S N)) Z Z<S = refl
enumerate-index (S (S N)) (S i) (S<S i<N) =
  let n<SSn : N < S (S N)
      n<SSn = n<m→n<Sm n<Sn
      idx : (enum-desc N n<SSn ! i) ≡ Just ⟨ N - i , minus-monotone n<SSn ⟩
      idx = enum-desc-idx N n<SSn i i<N
   in idx
    

postulate enumerate-exhaustive : (N i : Nat) (i<N : i < N) → ⟨ i , i<N ⟩ ∈ enumerate N
