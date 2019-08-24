inc : forall (n : Nat). Nat
inc = \n. natElim ((\n. Nat) : forall (n : Nat). Type) (Suc Zero) ((\k n. Suc n) : forall (k : Nat) (n : Nat). Nat) n

dec : forall (n : Nat). Nat
dec = \n. natElim ((\n. Nat) : forall (n : Nat). Type) Zero ((\k n. k) : forall (k : Nat) (n : Nat). Nat) n

plus : forall (n : Nat) (m : Nat). Nat
plus = \n m. natElim ((\n. Nat) : forall (n : Nat). Type) n ((\k n. Suc n) : forall (k : Nat) (n : Nat). Nat) m

minus : forall (n : Nat) (m : Nat). Nat
minus = \n m. natElim ((\n. Nat) : forall (n : Nat). Type) n ((\k n. dec n) : forall (k : Nat) (n : Nat). Nat) m

uncurry : forall (a : Type) (b : Type) (c : Type) (f : forall (x : a) (y : b). c) (p : a*b). c
uncurry = \a b c f p. prodElim a b c f p

curry : forall (a : Type) (b : Type) (c : Type) (f : forall (p : a*b). c) (x : a) (y : b). c
curry = \a b c f x y. f (x*y)

length : forall (a : Type) (l : List a). Nat
length = \a l. listElim a ((\l. Nat) : forall (l : List a). Type) l Zero ((\x xs acc. Suc acc) : forall (x : a) (xs : List a) (acc : Nat). Nat)

head : forall (a : Type) (default : a) (l : List a). a
head = \a def l. listElim a ((\l. a) : forall (l : List a). Type) l def ((\x xs acc. x) : forall (x : a) (xs : List a) (acc : a). a)

tail : forall (a : Type) (l : List a). List a
tail = \a l. listElim a ((\l. List a) : forall (l : List a). Type) l ([] : List a) ((\x xs acc. xs) : forall (x : a) (xs : List a) (acc : List a). List a)

map : forall (a : Type) (b : Type) (f : forall (x : a). b) (l : List a). List b
map = \a b f l. listElim a ((\l. List b) : forall (l : List a). Type) l ([] : List b) ((\x xs acc. (f x)::acc) : forall (x : a) (xs : List a) (acc : List b). List b)

foldr : forall (a : Type) (b : Type) (f : forall (x : a) (acc : b). b) (e : b) (l : List a). b
foldr = \a b f e l. listElim a ((\l. b) : forall (l : List a). Type) l e ((\x xs acc. f x acc) : forall (x : a) (xs : List a) (acc : b). b)

sum : forall (l : List Nat). Nat
sum = \l. foldr Nat Nat ((\x acc. plus x acc) : forall (x : Nat) (acc : Nat). Nat) Zero l

eqsymm : forall (a : Type) (x : a) (y : a) (eq : I a x y). I a y x
eqsymm = \a x y eq. eqElim a (\x y eq. I a y x) (\x. Refl x) x y eq

eqtrans : forall (a : Type) (x : a) (y : a) (z : a) (xeqy : I a x y) (yeqz : I a y z). I a x z
eqtrans = \a x y z xeqy. eqElim a (\x y xeqy. forall (z : a) (eq : I a y z). I a x z) ((\x z xeqz. xeqz) : forall (x : a) (z : a) (xeqz : I a x z). I a x z) x y xeqy z

exists : forall (a : Type) (b : forall (x : a). Type) (x : a) (p : b x). a*(b x)
exists = \a b x p. x*p

not : forall (a : Type). Type
not = \a. forall (x : a). Void

leibniz : forall (a : Type) (b : Type) (f : forall (x : a). b) (x : a) (y : a) (eq : I a x y). I b (f x) (f y)
leibniz = \a b f x y eq. eqElim a (\x y xeqy. I b (f x) (f y)) (\x. Refl (f x)) x y eq

-- apply : forall (a : Type) (b : Type) (p : I Type a b) (x : a). b
-- apply = \a b p x. eqElim Type (\a b eq. forall (x : a). b) ((\t x. x) : forall (t : a) (x : t). t) a b p x

withZero : forall (a : Type). forall (x : a). a*Nat
withZero = \a x. x*Zero

finToNat : forall (n : Nat) (f : Fin n). Nat
finToNat = \n f. finElim (\x y. Nat) (\x. Zero) (\x y rec. Suc rec) n f

main : Nat
main = finToNat (Suc Zero) (FZero Zero)
