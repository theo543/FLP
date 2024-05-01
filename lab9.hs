{-# OPTIONS_GHC -Wall -Wextra -Wno-unused-do-bind -Wno-name-shadowing #-}
{-# LANGUAGE TemplateHaskell #-}

import Data.List (delete)
import Test.QuickCheck (quickCheckAll, once, NonNegative(NonNegative), Property)
import Test.QuickCheck.Monadic (monadicIO, run)
import Control.Concurrent (forkIO, threadDelay, putMVar, newEmptyMVar, killThread, tryTakeMVar)
import Test.QuickCheck.Property (succeeded, failed, reason)

notNull :: [a] -> Bool
notNull = not . null

data PCFTerm = Var String | Lam String PCFTerm | App PCFTerm PCFTerm | Zero | Suc PCFTerm | IfZ PCFTerm PCFTerm String PCFTerm | Fix String PCFTerm
    deriving Show

-- union of two sets represented as lists
union2 :: (Eq a) => [a] -> [a] -> [a]
union2 x y = x ++ [z | z <- y, notElem z x]

-- variables of a PCF term
var :: PCFTerm -> [String]
var term = case term of
    Var v -> [v]
    Lam param body -> [param] `union2` var body
    App a b -> var a `union2` var b
    Zero -> []
    Suc nr -> var nr
    IfZ num if_body else_param else_body -> var num `union2` var if_body `union2` [else_param] `union2` var else_body
    Fix fix_param fix_body -> [fix_param] `union2` var fix_body

-- free variables of a PCF term
fv :: PCFTerm -> [String]
fv term = case term of
    Var v -> [v]
    Lam param body -> delete param $ var body
    App a b -> var a `union2` var b
    Zero -> []
    Suc nr -> var nr
    IfZ num if_body else_param else_body -> var num `union2` var if_body `union2` delete else_param (var else_body)
    Fix fix_param fix_body -> delete fix_param $ var fix_body

-- an endless reservoir of variables
freshvarlist :: [String]
freshvarlist = map ("x" ++) (map show [(0 :: Integer)..])

-- fresh variable for a PCF term
freshforterm :: PCFTerm -> String
freshforterm t = case [x | x <- freshvarlist, notElem x (var t)] of
    freshVar : _ -> freshVar
    [] -> error "Can never happen, terms don't have infinite variables."

-- the substitution operation for PCF terms
subst :: PCFTerm -> String -> PCFTerm -> PCFTerm
subst (Var x) y t
    | x == y        = t
    | otherwise     = Var x
subst (Lam x s) y t
    | x == y        = Lam x s
    | elem x (fv t) = let z = freshforterm (Lam y (App s t)) in Lam z (subst (subst s x (Var z)) y t)
    | otherwise     = Lam x (subst s y t)
subst (App s u) y t = App (subst s y t) (subst u y t)
subst Zero _ _      = Zero
subst (Suc s) y t   = Suc (subst s y t)
subst (IfZ n s w u) y t
    | w == y        = IfZ (subst n y t) (subst s y t) w u
    | elem w (fv t) = let z = freshforterm (Fix y (App u t)) in IfZ (subst n y t) (subst s y t) z (subst (subst u w (Var z)) y t)
    | otherwise     = IfZ (subst n y t) (subst s y t) w (subst u y t)
subst (Fix x s) y t
    | x == y        = Fix x s
    | elem x (fv t) = let z = freshforterm (Fix y (App s t)) in Fix z (subst (subst s x (Var z)) y t)
    | otherwise     = Fix x (subst s y t)

-- eager isValue
isValueE :: PCFTerm -> Bool
isValueE term = case term of
    Var _ -> True
    App _ _ -> False
    Lam _ _ -> True
    Zero -> True
    Suc num -> isValueE num
    IfZ _ _ _ _ -> False
    Fix _ _ -> False

-- eager beta reduction in one step
beta1E :: PCFTerm -> [PCFTerm]
beta1E term = case term of
    Var _ -> []
    Lam _ _ -> []
    App a b | notNull $ a' -> fmap (`App` b) $ a'
        where a' = beta1E a
    App a b | isValueE a && notNull b' -> fmap (a `App`) b'
        where b' = beta1E b
    App (Lam param body) arg | isValueE arg -> [subst body param arg]
    App _ _ -> []
    Zero -> []
    Suc nr | notNull nr' -> fmap Suc nr'
        where nr' = beta1E nr
    Suc _ -> []
    IfZ Zero if_body _ _ -> [if_body]
    IfZ nr if_body else_param else_body | notNull nr' -> fmap (\nr' -> IfZ nr' if_body else_param else_body) nr'
        where nr' = beta1E nr
    IfZ suc_nr@(Suc nr) _ else_param else_body | isValueE suc_nr -> [subst else_body else_param nr]
    IfZ _ _ _ _ -> []
    Fix fix_param fix_body -> [subst fix_body fix_param term]

-- checks whether a term is in normal form
nfE :: PCFTerm -> Bool
nfE = null . beta1E

data TermTree = TermTree PCFTerm [TermTree]
    deriving Show

-- the beta-reduction tree of a lambda term
reductreeE :: PCFTerm -> TermTree
reductreeE t = TermTree t (map reductreeE (beta1E t))

--depth-first traversal of all the leaves in a term tree
df_leaves :: TermTree -> [PCFTerm]
df_leaves (TermTree t []) = [t]
df_leaves (TermTree _ l) = concatMap df_leaves l

-- the left-most outer-most reduction of a term
reduceE :: PCFTerm -> PCFTerm
reduceE term = case df_leaves $ reductreeE term of
    x : _ -> x
    [] -> error "Failed to reduce term."

-- natural numbers in PCF
number :: Int -> PCFTerm
number 0 = Zero
number n | n < 0 = error "This encoding does not support negative numbers."
number n = Suc (number (n-1))

-- conversion from PCF back to natural numbers
backnr :: PCFTerm -> Int
backnr term = case term of
    Zero -> 0
    (Suc n) -> (backnr n) + 1
    _ -> error $ "Term " ++ show term ++ " is not a number."

prop_numberIsNormalForm :: NonNegative Int -> Bool
prop_numberIsNormalForm (NonNegative n) = nfE (number n)

prop_conversionRoundtrip :: NonNegative Int -> Bool
prop_conversionRoundtrip (NonNegative n) = n == backnr (number n)

prop_conversionRoundtripWithReduce :: NonNegative Int -> Bool
prop_conversionRoundtripWithReduce (NonNegative n) = n == backnr (reduceE (number n))

lamSuc :: Int -> Int
lamSuc = backnr . reduceE . Suc . number

prop_lamSuc :: NonNegative Int -> Bool
prop_lamSuc (NonNegative n) = n + 1 == lamSuc n

-- PCF term for addition
tadd :: PCFTerm
tadd =  Fix "plus_rec" (
            Lam "x" ( Lam "y" ( 
                IfZ (Var "y")
                    (Var "x")
                "y'" (
                    Suc (App (App (Var "plus_rec") (Var "x")) (Var "y'"))
                )
            ))
        )

lamAdd :: Int -> Int -> Int
lamAdd a b = backnr (reduceE (App (App tadd (number a)) (number b)))

prop_lamAdd :: NonNegative Int -> NonNegative Int -> Bool
prop_lamAdd (NonNegative a) (NonNegative b) = a + b == lamAdd a b

-- PCF term for saturating subtraction
tsub :: PCFTerm
tsub =  Fix "subst_rec" (
            Lam "x" ( Lam "y" (
                IfZ (Var "y")
                    (Var "x")
                "y'" (
                    IfZ (Var "x")
                        Zero
                    "x'" (
                        App (App (Var "subst_rec") (Var "x'")) (Var "y'")
                    )
                )
            ))
        )

lamSub :: Int -> Int -> Int
lamSub a b = backnr (reduceE (App (App tsub (number a)) (number b)))

prop_lamSub :: NonNegative Int -> NonNegative Int -> Bool
prop_lamSub (NonNegative a) (NonNegative b) = max 0 (a - b) == lamSub a b

-- PCF term for GCD
tgcd :: PCFTerm
tgcd =  Fix "gcd_rec" (
            Lam "x" ( Lam "y" (
                IfZ (Var "x")
                    (Var "y")
                "_" (
                    IfZ (Var "y")
                        (Var "x")
                    "_" (
                        IfZ (App (App tsub (Var "y")) (Var "x"))
                            (App (App (Var "gcd_rec") (App (App tsub (Var "x")) (Var "y"))) (Var "y"))
                        "y_minus_x'" (
                            (App (App (Var "gcd_rec") (Var "x")) (Suc (Var "y_minus_x'")))
                        )
                    )
                )
            ))
        )

lamGCD :: Int -> Int -> Int
lamGCD a b = backnr (reduceE (App (App tgcd (number a)) (number b)))

prop_lamGCD :: NonNegative Int -> NonNegative Int -> Bool
prop_lamGCD (NonNegative a) (NonNegative b) = gcd a b == lamGCD a b

-- PCF term for minimization
tmu :: PCFTerm
tmu =   Lam "function" (App
            (Fix "find_first_zero_rec" (
                Lam "counter" (
                    IfZ (App (Var "function") (Var "counter"))
                        (Var "counter")
                    "_" (
                        App (Var "find_first_zero_rec") (Suc (Var "counter"))
                    )
                )
            ))
            Zero
        )

lamMu :: PCFTerm -> Int
lamMu function = backnr (reduceE (App tmu function))

lamMuForever :: Int
lamMuForever =  lamMu (Lam "x" (App (App tadd (number 15)) (Var "x"))) -- should not terminate

prop_foreverDoesNotTerminateIn2Sec :: Property
prop_foreverDoesNotTerminateIn2Sec = once $ monadicIO $ run $ do
    atomicFlag <- newEmptyMVar
    workerThread <- forkIO $ do
        result <- return $! lamMuForever
        putMVar atomicFlag result
    threadDelay $ 2 * 1000000
    killThread workerThread
    tryResult <- tryTakeMVar atomicFlag
    return $ case tryResult of
        Nothing -> succeeded
        Just x -> failed { reason = "Expected the computation to not terminate, but got " ++ show x ++ " after waiting for 2 seconds." }

prop_lamMu :: NonNegative Int -> Bool
prop_lamMu (NonNegative a) = a == lamMu function
    where function = Lam "x" (App (App tsub (number a)) (Var "x"))

return [] -- TH weirdness

main :: IO ()
main = do
  result <- $quickCheckAll
  if result then
    putStrLn "All tests passed"
  else
    putStrLn "\n\n\x1b[31mSome tests failed!!\x1b[0m\n\n"
