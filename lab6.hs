{-# OPTIONS_GHC -Wall -Wextra -Wno-unused-do-bind -Wno-name-shadowing #-}

import Data.List
import Data.Maybe

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
              
-- This is where the new stuff starts

-- an endless reservoir of variables
freshvarlist :: [String]
freshvarlist = map ("x" ++) (map show [0 :: Integer ..])

solved_form_to_tuples :: [Equ] -> [(String, Term)]
solved_form_to_tuples = map
    (\equ -> case equ of
        (Equ (Variable v) t) -> (v, t)
        bad -> error $ "Not in solved form: " ++ show bad 
    )

-- a list of equations in solved form acting as a substitution
substitute :: [Equ] -> Term -> Term
substitute subst_equs = substitute'
    where
        subst_key_val = solved_form_to_tuples subst_equs
        substitute' t = case t of
            (Variable v) -> fromMaybe t $ fmap snd $ find (\(key, _) -> key == v) subst_key_val
            (FuncSym f vars) -> FuncSym f (map substitute' vars)

data AtomicRel = AtomicRel String [Term]
    deriving (Eq, Show)

-- variables of a relational atomic formula
vara :: AtomicRel -> [String]
vara (AtomicRel _ ts) = concatMap var ts

-- substitution for an atomic formula
substitutea :: [Equ] -> AtomicRel -> AtomicRel
substitutea subst_equs (AtomicRel p terms) = AtomicRel p $ map (substitute subst_equs) terms

-- unification for two atomic formulas
unifya :: AtomicRel -> AtomicRel -> AllResult
unifya (AtomicRel _ tlist1) (AtomicRel _ tlist2) = unify $ zipWith Equ tlist1 tlist2

data Clause = Clause AtomicRel [AtomicRel]
    deriving (Eq, Show)

-- variables of a clause
varcl :: Clause -> [String]
varcl (Clause at ats) = concatMap vara $ at:ats

-- substitution for a clause
substitutecl :: [Equ] -> Clause -> Clause
substitutecl subst_equs (Clause at ats) = Clause (subst at) (map subst ats)
    where subst = substitutea subst_equs

data Goal = Goal [AtomicRel]
    deriving (Eq, Show)

-- variables of a goal
vargl :: Goal -> [String]
vargl (Goal ats) = concatMap vara ats

-- fresh variables for a goal
varngl :: Goal -> [String]
varngl g = undefined

-- renaming of a clause according to a goal
renclause :: Goal -> Clause -> Clause
renclause g c = undefined

-- substitution for a goal
substitutegl :: [Equ] -> Goal -> Goal
substitutegl es (Goal ats) = undefined

-- auxiliary function for composition of solved forms
composeaux :: [Equ] -> [Equ] -> [Equ]
composeaux [] _ = []
composeaux ((Equ (Variable x) t):es) fs = (Equ (Variable x) (substitute fs t)):(composeaux es fs)

-- variables in a solved form
vareq :: [Equ] -> [String]
vareq [] = []
vareq ((Equ (Variable x) _):es) = x:(vareq es)

-- composition of solved forms
compose :: [Equ] -> [Equ] -> [Equ]
compose es fs = (composeaux es fs) ++ [Equ (Variable x) t | (Equ (Variable x) t) <- fs, notElem x (vareq es)]

-- evaluates a clause in a goal with a selected formula (the full program is the first argument)
evaluatemix :: [Clause] -> Clause -> ([AtomicRel], AtomicRel, [AtomicRel]) -> [[Equ]]
evaluatemix p (Clause bt bts) (l1, at, l2) = case (unifya at bt) of
                                                Failure -> []
                                                Set es -> map (compose es) (evaluatep p (substitutegl es (Goal (l1 ++ bts ++ l2))))

-- creates goals with selected formulas for use in the above function
mixg :: [a] -> [([a], a, [a])]
mixg [] = []
mixg (x:xs) = ([],x,xs):(map (\(a,b,c) -> (x:a,b,c)) (mixg xs))

-- evaluates a goal in a clause (the full program is the first argument)
evaluatenc :: [Clause] -> Goal -> Clause -> [[Equ]]
evaluatenc p (Goal ats) c = undefined

-- evaluates a program and a goal, assuming all the clauses in the program have already been appropriately renamed
evaluatenp :: [Clause] -> Goal -> [[Equ]]
evaluatenp p g = undefined

-- evaluates a program and a goal
evaluatep :: [Clause] -> Goal -> [[Equ]]
evaluatep p (Goal []) = [[]]
evaluatep p g = undefined

-- restricts the variables in a solved form to the variables that appear in a given list
restrict :: [String] -> [Equ] -> [Equ]
restrict _ [] = []
restrict vs ((Equ (Variable x) t):es) | elem x vs = (Equ (Variable x) t):(restrict vs es)
restrict vs (_:es) = restrict vs es

-- evaluates a program and a goal (restricting the solved form to the variables that actually appear in the goal)
evaluate :: [Clause] -> Goal -> [[Equ]]
evaluate p g = undefined

-- zero term
termz :: Term
termz = FuncSym "z" []

-- successor
terms :: Term -> Term
terms t = FuncSym "s" [t]

-- variables
vx :: Term
vx = Variable "x"

vy :: Term
vy = Variable "y"

vz :: Term
vz = Variable "z"

vw :: Term
vw = Variable "w"

-- addition predicate
vadd :: Term -> Term -> Term -> AtomicRel
vadd t s u = AtomicRel "add" [t, s, u]

-- multiplication predicate
vmul :: Term -> Term -> Term -> AtomicRel
vmul t s u = AtomicRel "mul" [t, s, u]

-- term for natural number
termn :: Int -> Term
termn 0 = termz
termn n = terms (termn (n-1))

-- recovering the natural number from a term
backp :: Term -> Int
backp (FuncSym "z" []) = 0
backp (FuncSym "s" [t]) = (backp t) + 1

extr :: [[Equ]] -> Int
extr (((Equ (Variable "x") t):_):_) = backp t

proga = [Clause (vadd vx termz vx) [], Clause (vadd vx (terms vy) (terms vz)) [vadd vx vy vz]]
progm = [Clause (vmul vx termz termz) [], Clause (vmul vx (terms vy) vz) [vmul vx vy vw, vadd vw vx vz]]
prog  = proga ++ progm
goal1 = Goal [vadd (termn 3) (termn 4) vx]
goal2 = Goal [vmul (termn 3) (termn 4) vx]
test1 = extr (evaluate prog goal1) == 7
test2 = extr (evaluate prog goal2) == 12
