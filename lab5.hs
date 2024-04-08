{-# OPTIONS_GHC -Wall -Wextra -Wno-unused-do-bind -Wno-name-shadowing #-}

import Data.List

data Term = Variable String | FuncSym String [Term]
    deriving (Eq, Show)

-- returns all variables of a term
var :: Term -> [String]
var term = case term of
    Variable varName -> [varName]
    FuncSym _ terms -> concatMap var terms

-- substitutes, in a term, a variable by another term
subst :: Term -> String -> Term -> Term
subst term findName replaceWith = case term of
    Variable varName -> if varName == findName then replaceWith else term
    FuncSym f terms -> FuncSym f (map (\t -> subst t findName replaceWith) terms)

data Equ = Equ Term Term
    deriving Show

data StepResult = FailureS | Stopped | SetS [Equ]
    deriving Show

equVar :: Equ -> [String]
equVar (Equ t1 t2) = var t1 ++ var t2

failIfAny :: (Equ -> Bool) -> [Equ] -> StepResult
failIfAny predicate equs = if any predicate equs then FailureS else Stopped

step1 :: [Equ] -> StepResult
step1 equs = let
        findEq :: Equ -> Bool
        findEq eq = case eq of
            (Equ (FuncSym f1 l1) (FuncSym f2 l2)) -> (f1 == f2) && (length l1 == length l2)
            _ -> False
        (matches, rest) = partition findEq equs
        modifyMatches :: Equ -> [Equ]
        modifyMatches equ = case equ of
            (Equ (FuncSym _ l1) (FuncSym _ l2)) -> zipWith Equ l1 l2
            _ -> undefined
    in
        case matches of
            [] -> Stopped
            _ -> SetS $ concatMap modifyMatches matches ++ rest

step2 :: [Equ] -> StepResult
step2 = failIfAny findEq
    where
        findEq :: Equ -> Bool
        findEq eq = case eq of
            (Equ (FuncSym f1 _) (FuncSym f2 _)) -> f1 /= f2
            _ -> False
        

step3 :: [Equ] -> StepResult
step3 equs = let
        findEq :: Equ -> Bool
        findEq eq = case eq of
            (Equ (Variable v1) (Variable v2)) -> v1 == v2
            _ -> False
        (removed, remaining) = partition findEq equs
    in
        case removed of
            [] -> Stopped
            _ -> SetS remaining

step4 :: [Equ] -> StepResult
step4 equs = let
        findEq :: Equ -> Bool
        findEq eq = case eq of
            (Equ (FuncSym _ _) (Variable _)) -> True
            _ -> False
        (matches, rest) = partition findEq equs
        modifyMatches :: Equ -> Equ
        modifyMatches (Equ a b) = Equ b a
    in
        case matches of
            [] -> Stopped
            _ -> SetS $ map modifyMatches matches ++ rest

step5 :: [Equ] -> StepResult
step5 = failIfAny findEq
    where
        findEq :: Equ -> Bool
        findEq equ = case equ of
            (Equ (Variable v) (FuncSym _ terms)) -> elem v $ concatMap var terms
            _ -> False

findDuplicates :: (Eq a, Ord a) => [a] -> [a]
findDuplicates list = case (sort list) of
    [] -> []
    x:xs -> findDuplicates' x xs
    where
        findDuplicates' :: Eq t => t -> [t] -> [t]
        findDuplicates' lastSeen remaining = case remaining of
            [] -> []
            x:xs | x == lastSeen -> x : findDuplicates' x (dropWhile (== x) xs)
            x:xs -> findDuplicates' x xs

-- candidates for "x=t" in step 6 of the algorithm
step6cand :: [Equ] -> [Equ]
step6cand equs = filter findEq equs
    where
        eqVars = map equVar equs
        uniqueVarPerEq = map nub eqVars
        varsInMultipleEq = findDuplicates $ concat uniqueVarPerEq
        findEq :: Equ -> Bool
        findEq equ = case equ of
            (Equ (Variable v) _) -> elem v varsInMultipleEq
            _ -> False

-- substitutes in a list of equations a variable by a term EXCEPT for the equation "variable=term" (as used in step 6 of the algorithm)
substeq :: [Equ] -> String -> Term -> [Equ]
substeq equs findVar replaceWith = map (substeq' findVar replaceWith) equs
    where
        substeq' :: String -> Term -> Equ -> Equ
        substeq' findVar replaceWith eq = case eq of
            (Equ (Variable v) t) | v == findVar && t == replaceWith -> eq
            (Equ t1 t2) -> Equ (s t1) (s t2)
            where
                s term = subst term findVar replaceWith

step6 :: [Equ] -> StepResult
step6 equs = case step6cand equs of
    (Equ (Variable findVar) replaceWith):_ -> SetS $ substeq equs findVar replaceWith
    _ -> Stopped

stepsOrder :: [[Equ] -> StepResult]
stepsOrder = [step1, step2, step3, step4, step5, step6]

onestep :: [Equ] -> StepResult
onestep = onestep' stepsOrder
    where
        onestep' :: [[Equ] -> StepResult] -> [Equ] -> StepResult
        onestep' [] _ = Stopped
        onestep' (currentStep:nextSteps) es = case (currentStep es) of
            SetS fs -> SetS fs
            Stopped -> onestep' nextSteps es
            FailureS -> FailureS

data AllResult = Failure | Set [Equ]
    deriving Show

unify :: [Equ] -> AllResult
unify es = case onestep es of
                    Stopped -> Set es
                    FailureS -> Failure
                    SetS fs -> unify fs

eqset1 :: [Equ]
eqset1 = [Equ (Variable "z") (FuncSym "f" [Variable "x"]), Equ (FuncSym "f" [Variable "t"]) (Variable "y")]
         -- z=f(x), f(t)=y  --> should have z=f(x), y=f(t)

eqset2 :: [Equ]
eqset2 = [Equ (FuncSym "f" [Variable "x", FuncSym "g" [Variable "y"]]) (FuncSym "f" [FuncSym "g" [Variable "z"], Variable "z"])]
         -- f(x,g(y))=f(g(z),z) --> should have x=g(g(y)), z=g(y)

eqset3 :: [Equ]
eqset3 = [Equ (FuncSym "f" [Variable "x", FuncSym "g" [Variable "x"], FuncSym "b" []]) (FuncSym "f" [FuncSym "a" [], FuncSym "g" [Variable "z"], Variable "z"])]
          -- f(x,g(x),b)=f(a,g(z),z) --> should return failure

prettyTerm :: Term -> String
prettyTerm t = case t of
    (Variable v) -> v
    (FuncSym f terms) -> f ++ "(" ++ intercalate ", " (map prettyTerm terms) ++ ")"

prettyEq :: Equ -> String
prettyEq (Equ t1 t2) = prettyTerm t1 ++ " = " ++ prettyTerm t2

prettyEqs :: [Equ] -> String
prettyEqs eqs = (intercalate "\n" $ map prettyEq eqs) ++ "\n"

prettyUnify :: [Equ] -> String
prettyUnify eq = case unify eq of
    (Set eqs) -> prettyEqs eqs
    Failure -> "Failure\n"

prettyUnifyIO :: [Equ] -> IO ()
prettyUnifyIO = putStr . prettyUnify
