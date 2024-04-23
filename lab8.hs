{-# OPTIONS_GHC -Wall -Wextra -Wno-unused-do-bind -Wno-name-shadowing #-}

import Data.List (partition, sort, nub)

data Term = Variable String | FuncSym String [Term]
    deriving (Eq, Show)

union2 :: (Eq a) => [a] -> [a] -> [a]
union2 x y = x ++ [z | z <- y, z `notElem` x]

union :: (Eq a) => [[a]] -> [a]
union = foldr union2 []

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
            (Equ (Variable v) _) -> v `elem` varsInMultipleEq
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
        onestep' (currentStep:nextSteps) es = case currentStep es of
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

data LambdaTerm = Var String | Lam String LambdaTerm | App LambdaTerm LambdaTerm
    deriving Show

-- free variables of a lambda term
fv :: LambdaTerm -> [String]
fv term = case term of
    Var v -> [v]
    Lam x t -> filter (/= x) $ fv t
    App t1 t2 -> fv t1 ++ fv t2

-- an endless reservoir of variables
freshvarlist :: [String]
freshvarlist = map (("x" ++) . show) [(0 :: Integer)..]

-- This is where the new stuff starts

-- annotated lambda term
data AnnLambdaTerm = AVar String | ALam String String AnnLambdaTerm | AApp AnnLambdaTerm AnnLambdaTerm
    deriving Show

-- the gamma_M context from the type inference algorithm
gamma :: LambdaTerm -> [(String,String)]
gamma t = zip (fv t) freshvarlist

-- auxiliary function for annotation: given a term and a list of fresh variables, returns the annotated term and the list of remaining fresh variables
annotateAux :: LambdaTerm -> [String] -> (AnnLambdaTerm, [String])
annotateAux term vars = case term of
    Var x -> (AVar x, vars)
    Lam p b -> (ALam p (head vars) annB, remainingVars)
        where (annB, remainingVars) = annotateAux b (tail vars)
    App a b -> (AApp annA annB, vars'')
        where (annA, vars' ) = annotateAux a vars
              (annB, vars'') = annotateAux b vars'

-- annotates a term as in the type inference algorithm; returns the annotated term and the list of remaining fresh variables
annotate :: LambdaTerm -> (AnnLambdaTerm, [String])
annotate t = annotateAux t [x | x <- freshvarlist, x `notElem` [w | (_, w) <- gamma t]]

-- auxiliary function for constraints: given an annotated term, a list of fresh variables and a context, returns the list of equations and the list of remaining fresh variables
constraintsAux :: AnnLambdaTerm -> [String] -> [(String,String)] -> ([Equ], [String])
constraintsAux _ [] _ = error "Empty fresh vars"
constraintsAux term (nextVar:freshVars) dict = case term of
    AVar x -> case lookup x dict of
        Just type_ -> ([Equ (Variable type_) (Variable nextVar)], freshVars)
        Nothing -> error "Type not found"
    ALam param type_ body ->
        let
            (result, freshVars') = constraintsAux body freshVars ((param, type_):dict)
        in
            (Equ (Variable nextVar) (FuncSym "X" [Variable type_, Variable (head freshVars)]) : result, freshVars')
    AApp a b -> let
            (res1, freshVars') = constraintsAux a freshVars dict
            (res2, freshVars'') = constraintsAux b freshVars' dict
        in
            (Equ (Variable $ head freshVars) (FuncSym "X" [Variable $ head freshVars', Variable nextVar]) : res1 ++ res2, freshVars'')

-- finds the list of equations associated to a term together with the type variable to which the term corresponds
constraints :: LambdaTerm -> ([Equ], String)
constraints t = let (u, freshVars) = annotate t
                    (es, _) = constraintsAux u freshVars (gamma t)
                in (es, head freshVars)

-- finds the value of a variable in a set of equations in solved form
find :: String -> [Equ] -> Term
find z ((Equ (Variable w) t):_) | z == w = t
find z ((Equ t (Variable w)):_) | z == w = t
find z (_:es) = find z es
find z [] = error $ z ++ " not found."

data SimpleType = TypeVar String | Arrow SimpleType SimpleType
    deriving Show

-- converts a type expressed as a first-order term into a type properly formalized
totype :: Term -> SimpleType
totype (Variable x) = TypeVar x
totype (FuncSym _ [t, s]) = Arrow (totype t) (totype s)
totype (FuncSym _ _) = error "Cannot convert FuncSym without exactly two list elements."

-- finds the type of a term if it exists
typeinf :: LambdaTerm -> Maybe SimpleType
typeinf t = let (es, z) = constraints t
            in case unify es of
                   Set fs -> Just (totype (find z fs))
                   Failure -> Nothing

testl1 :: Maybe SimpleType
testl1 = typeinf $ Lam "x" (Var "x")

testl2 :: Maybe SimpleType
testl2 = typeinf $ Lam "x" (Lam "y" (Var "x"))

testm1 :: Maybe SimpleType
testm1 = typeinf $ App (Lam "z" (Lam "u" (Var "z"))) (App (Var "y") (Var "x"))

testm2 :: Maybe SimpleType
testm2 = typeinf $ App (Var "x") (Var "x")
