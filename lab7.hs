{-# OPTIONS_GHC -Wall -Wextra -Wno-unused-do-bind -Wno-name-shadowing #-}
{-# LANGUAGE TemplateHaskell #-}

import Data.List (uncons)

import Test.QuickCheck ( quickCheckAll, NonNegative(NonNegative) )

data LambdaTerm = Var String | Lam String LambdaTerm | App LambdaTerm LambdaTerm
    deriving Show

-- union of two sets represented as lists
union2 :: (Eq a) => [a] -> [a] -> [a]
union2 x y = x ++ [z | z <- y, notElem z x]

-- variables of a lambda term
var :: LambdaTerm -> [String]
var term = case term of
    Var v -> [v]
    Lam x t -> [x] `union2` var t
    App t1 t2 -> var t1 `union2` var t2

-- free variables of a lambda term
fv :: LambdaTerm -> [String]
fv term = case term of
    Var v -> [v]
    Lam x t -> filter (/= x) $ fv t
    App t1 t2 -> fv t1 `union2` fv t2

-- an endless reservoir of variables
freshvarlist :: [String]
freshvarlist = map ("x" ++) (map show [(0 :: Integer)..])

-- fresh variable for a term
freshforterm :: LambdaTerm -> String
freshforterm t = case filter (\freshVar -> not $ freshVar `elem` (var t)) freshvarlist of
    x:_ -> x
    [] -> error "This can't happen because terms don't have infinite variables."

-- the substitution operation for lambda terms
subst :: LambdaTerm -> String -> LambdaTerm -> LambdaTerm
subst term x n = case term of
    Var x_ | x_ == x -> n
    Var _ -> term
    Lam x_ _ | x_ == x -> term
    Lam y t | not $ y `elem` fv n -> Lam y $ subst' t
    Lam y t -> Lam z $ subst' (subst t y (Var z))
        where z = freshforterm t
    App t1 t2 -> App (subst' t1) (subst' t2)
    where subst' t = subst t x n

test_subst :: LambdaTerm
test_subst = subst (Lam "x" (App (Var "y") (Var "x"))) "y" (Var "x")

-- beta reduction in one step
beta1 :: LambdaTerm -> [LambdaTerm]
beta1 term = case term of
    Var _ -> []
    Lam arg body -> map (Lam arg) $ beta1 body
    App (Lam param body) arg -> [subst body param arg]
    App t1 t2 -> map (`App` t2) (beta1 t1) ++ map (t1 `App`) (beta1 t2)

-- checks whether a term is in normal form
nf :: LambdaTerm -> Bool
nf = null . beta1

data TermTree = TermTree LambdaTerm [TermTree]
    deriving Show

-- the beta-reduction tree of a lambda term
reductree :: LambdaTerm -> TermTree
reductree t = TermTree t $ map reductree $ beta1 t

-- depth-first traversal of all the nodes in a term tree
df_all :: TermTree -> [LambdaTerm]
df_all (TermTree term tree) = term : concatMap df_all tree

-- just the leaves
df_leaves :: TermTree -> [LambdaTerm]
df_leaves tree = case tree of
    (TermTree term []) -> [term]
    (TermTree _ children) -> concatMap df_leaves children

-- the left-most outer-most reduction of a term
reduce :: LambdaTerm -> LambdaTerm
reduce term = case beta1 term of
    [] -> term
    leftmost_outermost : _ -> reduce leftmost_outermost

term1 :: LambdaTerm
term1 = App (App (Lam "x" (Lam "y" (App (Var "x") (Var "y")))) (Var "z")) (Var "w")
term2 :: LambdaTerm
term2 = App (Lam "x" (App (Lam "y" (Var "x")) (Var "z"))) (Var "w")

test_beta1 :: [LambdaTerm]
test_beta1 = df_leaves (reductree term1)
test_beta2 :: [LambdaTerm]
test_beta2 = df_leaves (reductree term2)

-- a branch of given length in a tree
branch :: Int -> TermTree -> Maybe [LambdaTerm]
branch len term = fmap fst $ uncons $ branch' len term
    where
        branch' :: Int -> TermTree -> [[LambdaTerm]]
        branch' len (TermTree term children) = case len of
            0 -> [[]]
            1 -> [[term]]
            _ -> map (term :) $ concatMap (branch' (len - 1)) children

testbranch1 :: Maybe [LambdaTerm]
testbranch1 = branch 2 (reductree term1)
                                
testbranch2 :: Maybe [LambdaTerm]
testbranch2 = branch 3 (reductree term1)

term_o :: LambdaTerm
term_o = Lam "x" (App (Var "x") (Var "x"))
term_O :: LambdaTerm
term_O = App term_o term_o

testO :: LambdaTerm
testO = reduce term_O -- should not terminate

term_b :: LambdaTerm
term_b = App (App (Lam "x" (Lam "y" (Var "y"))) term_O) (Var "z")

testb :: LambdaTerm
testb = reduce term_b -- should terminate
                                
testbranch3 :: Maybe [LambdaTerm]
testbranch3 = branch 10 (reductree term_b)

-- Church numeral of a number
church :: Int -> LambdaTerm
church n = Lam "f" $ Lam "x" $ repeated_app n
    where
        repeated_app n = case n of
            0 -> Var "x"
            n | n < 0 -> error "This encoding does not support negative numbers."
            n -> App (Var "f") $ repeated_app $ n - 1

-- convert from Church numeral back to number
backch :: LambdaTerm -> Int
backch term = case term of
    (Lam "f" (Lam "x" repeated_app)) -> back_repeated_app repeated_app
    _ -> error "Not a Church numeral."
    where
        back_repeated_app term = case term of
            Var "x" -> 0
            App (Var "f") t -> 1 + back_repeated_app t
            _ -> error "Not a Church numeral."

prop_conversionRoundtrip :: NonNegative Int -> Bool
prop_conversionRoundtrip (NonNegative n) = n == backch (church n)

prop_conversionRoundtripWithReduce :: NonNegative Int -> Bool
prop_conversionRoundtripWithReduce (NonNegative n) = n == backch (reduce (church n))

-- lambda term for successor
tsucc :: LambdaTerm 
tsucc = Lam "n" $ Lam "f" $ Lam "x" $ App (Var "f") (App (App (Var "n") (Var "f")) (Var "x"))

lamSuc :: Int -> Int
lamSuc a = backch ((reduce (App tsucc (church a))))

prop_lamSuc :: NonNegative Int -> Bool
prop_lamSuc (NonNegative a) = (lamSuc a) == (a + 1)

-- lambda term for addition
tadd :: LambdaTerm
tadd = Lam "n" $ Lam "m" $ Lam "f" $ Lam "x" $ App (App (Var "n") (Var "f")) (App ((App (Var "m") (Var "f"))) (Var "x"))

lamAdd :: Int -> Int -> Int
lamAdd a b = backch ((reduce (App (App tadd (church a)) (church b))))

prop_lamAdd :: NonNegative Int -> NonNegative Int -> Bool
prop_lamAdd (NonNegative a) (NonNegative b) = (a `lamAdd` b) == (a + b)

return [] -- TH weirdness

main :: IO ()
main = do
  result <- $quickCheckAll
  if result then
    putStrLn "All tests passed"
  else
    putStrLn "\n\n\x1b[31mSome tests failed!!\x1b[0m\n\n"
