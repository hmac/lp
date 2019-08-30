b : Type
b = T

main : T
main = boolElim (\x. b) Unit Unit True
