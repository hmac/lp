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

a : Type
a = T|Nat

-- returns True if the node is null - i.e. an empty constructor
-- this is polymorphic and works for trees and lists
-- it expects the a in your W a b type to be T|t for some arbitrary t.
isnull : forall (t : Type). forall (x : T|t). Bool
isnull = \t. sumElim T t Bool (\x. True) (\z. False)

b : forall (x : a). Type
b = \x. ((I Bool (isnull Nat x) True)*Void)|((I Bool (isnull Nat x) False)*Bool)

bb : forall (x : a). Type
bb = \x. ((I Bool (isnull Nat x) True)*Void)|Void

foo : W a bb
foo = sup ((Left Unit) : a) ((sumElim ((I Bool True True)*Void) Void (W a bb) (prodElim (I Bool True True) Void (W a bb) (\triv void. absurd (W a bb) void)) (\void. absurd (W a bb) void)) : forall (x : ((I Bool True True)*Void)|Void). (W a bb))

leafHasNoLeftPredecessor : forall (x : (I Bool True True)*Void). W a b
leafHasNoLeftPredecessor = \x. prodElim (I Bool True True) Void (W a b) (\triv void. absurd (W a b) void) x

leafHasNoRightPredecessor : forall (x : (I Bool True False)*Bool). W a b
leafHasNoRightPredecessor = \x. prodElim (I Bool True False) Bool (W a b) (\trueEqFalse branch. absurd (W a b) (boolAxiom trueEqFalse)) x

treeLeaf : W a b
treeLeaf = sup ((Left Unit) : a) ((\x. sumElim ((I Bool True True)*Void) ((I Bool True False)*Bool) (W a b) leafHasNoLeftPredecessor leafHasNoRightPredecessor x) : (forall (x : b (Left Unit)). W a b))

--   0
--  / \
-- x   x
treeNode : W a b
treeNode = sup ((Right Zero) : a) ((\x. treeLeaf) : forall (x : b (Right Zero)). W a b)

falseNotEqTrue : forall (nope : I Bool False True). Void
falseNotEqTrue = \nope. boolAxiom (eqsymm Bool False True nope)

nodeHasPredecessors : forall (x : (I Bool False True)*Void). W a b
nodeHasPredecessors = \x. prodElim (I Bool False True) Void (W a b) (\nope void. absurd (W a b) void) x

tree2Branching : forall (bbb : Bool). W a b
tree2Branching = \branch. boolElim (\x. W a b) treeLeaf treeNode branch

tree2Predecessors : forall (right : (I Bool False False)*Bool). W a b
tree2Predecessors = \right. prodElim (I Bool False False) Bool (W a b) (\feqf branch. tree2Branching branch) right

--   0
--  / \
-- x   0
--    / \
--   x   x
tree2 : W a b
tree2 = sup ((Right Zero) : a) ((\x. sumElim ((I Bool False True)*Void) ((I Bool False False)*Bool) (W a b) nodeHasPredecessors tree2Predecessors x) : forall (x : b (Right Zero)). W a b)

--     0
--    / \
--   /   \
--  0     0
-- / \   / \
-- x  x x   x

tree3Branching : forall (bbb : Bool). W a b
tree3Branching = \branch. boolElim (\x. W a b) treeNode treeNode branch

tree3Predecessors : forall (right : (I Bool False False)*Bool). W a b
tree3Predecessors = \right. prodElim (I Bool False False) Bool (W a b) (\feqf branch. tree3Branching branch) right

tree3 : W a b
tree3 = sup ((Right Zero) : a) ((\x. sumElim ((I Bool False True)*Void) ((I Bool False False)*Bool) (W a b) nodeHasPredecessors tree3Predecessors x) : forall (x : b (Right Zero)). W a b)



-- let's try to make a list of bools, then

lA : Type
lA = T|Bool

lNil : forall (x : lA). Type
lNil = \x. (I Bool (isnull Bool x) True)*Void

lCons : forall (x : lA). Type
lCons = \x. (I Bool (isnull Bool x) False)*T

lB : forall (x : lA). Type
lB = \x. (lNil x)|(lCons x)

nilListBoolHasNoPredecessors : forall (x : (I Bool True True)*Void). W lA lB
nilListBoolHasNoPredecessors = \x. prodElim (I Bool True True) Void (W lA lB) (\triv void. absurd (W lA lB) void) x

nilListIsNotCons : forall (x : (I Bool True False)*T). W lA lB
nilListIsNotCons = \x. prodElim (I Bool True False) T (W lA lB) (\nope unit. absurd (W lA lB) (boolAxiom nope)) x

emptyListBoolRec : forall (x : lB (Left Unit)). W lA lB
emptyListBoolRec = \x. sumElim (lNil (Left Unit)) (lCons (Left Unit)) (W lA lB) nilListBoolHasNoPredecessors nilListIsNotCons x

elimFalseTrueProd : forall (a : Type). forall (x : (I Bool False True)*a). Void
elimFalseTrueProd = \a x. prodElim (I Bool False True) a Void (\falseEqTrue whatev. falseNotEqTrue falseEqTrue) x

-- Nil
emptyListOfBools : W lA lB
emptyListOfBools = sup ((Left Unit) : lA) emptyListBoolRec

consIsNotNil : forall (v : Bool) (y : lNil (Right v)). W lA lB
consIsNotNil = \v y. absurd (W lA lB) (elimFalseTrueProd Void y)

-- Cons 
singletonListRec : forall (v : Bool) (x : lB (Right v)). W lA lB
singletonListRec = \v x. sumElim (lNil (Right v)) (lCons (Right v)) (W lA lB) (consIsNotNil v) (\z. emptyListOfBools) x

singletonList : W lA lB
singletonList = sup ((Right True) : lA) (singletonListRec True)

trueFalseListRec : forall (x : lB (Right True)). W lA lB
trueFalseListRec = \x. sumElim (lNil (Right True)) (lCons (Right True)) (W lA lB) (consIsNotNil True) (\z. singletonListRec False (Right z)) x

trueFalseList : W lA lB
trueFalseList = sup ((Right True) : lA) trueFalseListRec

testRec : Nat
testRec = Rec (\x. Nat) tree3 (\t f rec. sumElim T Nat Nat (\x. Zero) (\x. Suc x) t)

main : Nat
main = testRec
