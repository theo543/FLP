{-# OPTIONS_GHC -Wall -Wextra -Wno-unused-do-bind -Wno-name-shadowing #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
import Data.Char

newtype Parser a = Parser { parse :: String -> [(a,String)] }

item :: Parser Char
item = Parser (\cs -> case cs of
                "" -> []
                (c:cs) -> [(c,cs)])

instance Monad Parser where
    p >>= f = Parser (\cs -> concat (map (\(a, cs') -> (parse (f a) cs')) (parse p cs)))

instance Applicative Parser where
    pure a = Parser (\cs -> [(a,cs)])
    mf <*> ma = do
        f <- mf
        va <- ma
        return (f va)    

instance Functor Parser where              
    fmap f ma = pure f <*> ma   
  
zero :: Parser a
zero = Parser (const [])

psum :: Parser a -> Parser a -> Parser a
psum p q = Parser (\cs -> (parse p cs) ++ (parse q cs))

(<|>) :: Parser a -> Parser a -> Parser a
p <|> q = Parser (\cs -> case parse (psum p q) cs of
                                [] -> []
                                (x:_) -> [x])

dpsum0 :: Parser [a] -> Parser [a]                       
dpsum0 p = p <|> (return [])

sat :: (Char -> Bool) -> Parser Char
sat p = do
            c <- item
            if p c then return c else zero

char :: Char -> Parser Char
char c = sat (c ==)

string :: String -> Parser String
string [] = return []
string (c:cs) = do
                    pc <- char c
                    prest <- string cs
                    return (pc : prest)

many0 :: Parser a -> Parser [a]
many0 p = dpsum0 (many1 p)

many1 :: Parser a -> Parser [a]
many1 p = do 
    a <- p
    aa <- many0 p
    return (a : aa)

spaces :: Parser String
spaces = many0 (sat isSpace)

token :: Parser a -> Parser a
token p = do
            spaces
            a <- p
            spaces
            return a

symbol :: String -> Parser String
symbol symb = token (string symb)

data AExp = Nu Int | Qid String | PlusE AExp AExp | TimesE AExp AExp | DivE AExp AExp
    deriving Show
    
aexp :: Parser AExp
aexp = plusexp <|> mulexp <|> divexp <|> npexp

npexp :: Parser AExp
npexp = parexp <|> qid <|> integer

parexp :: Parser AExp
parexp = do
            symbol "("
            p <- aexp
            symbol ")"
            return p

look :: Parser (Maybe Char)
look = Parser (\cs -> case cs of
      [] -> [(Nothing, [])]
      (c:cs') -> [(Just c, c:cs')]
    )

digit :: Parser Int
digit = do
          d <- sat isDigit
          return (digitToInt d)

integer :: Parser AExp
integer = do
                  spaces
                  s <- look
                  ss <- do
                            if s == (Just '-') then
                                                  do
                                                    item
                                                    return (-1)
                                               else return 1
                  d <- digitToInt <$> sat isDigit
                  if d == 0 
                    then 
                      return (Nu 0)
                    else 
                      do
                        ds <- many0 digit
                        return (Nu (ss*(asInt (d:ds))))
          where asInt ds = sum [d * (10^p) | (d, p) <- zip (reverse ds) [(0 :: Int)..] ]

qid :: Parser AExp
qid = do
            char '\''
            a <- many1 (sat isLetter)
            return (Qid a)

plusexp :: Parser AExp
plusexp = do
            p <- npexp
            symbol "+"
            q <- npexp
            return (PlusE p q)

mulexp :: Parser AExp
mulexp = do
            p <- npexp
            symbol "*"
            q <- npexp
            return (TimesE p q)

divexp :: Parser AExp
divexp = do
            p <- npexp
            symbol "/"
            q <- npexp
            return (DivE p q)


data BExp = BE Bool | LE AExp AExp | NotE BExp | AndE BExp BExp
    deriving Show
    
bexp :: Parser BExp
bexp = lexp <|> notexp <|> andexp <|> npexpb

npexpb :: Parser BExp
npexpb = parexpb <|> true <|> false

parexpb :: Parser BExp
parexpb = do
            symbol "("
            p <- bexp
            symbol ")"
            return p

true :: Parser BExp
true = do
            symbol "true"
            return (BE True)

false :: Parser BExp
false = do
            symbol "false"
            return (BE False)

lexp :: Parser BExp
lexp = do
            p <- npexp
            symbol "<="
            q <- npexp
            return (LE p q)

notexp :: Parser BExp
notexp =  do
            symbol "not"
            q <- npexpb
            return (NotE q)

andexp :: Parser BExp
andexp = do
            p <- npexpb
            symbol "&&"
            q <- npexpb
            return (AndE p q)
          
data Stmt = Skip | AtrE String AExp | Seq Stmt Stmt | IfE BExp Stmt Stmt | WhileE BExp Stmt
    deriving Show

stmt :: Parser Stmt
stmt = seqp <|> stmtneseq

stmtneseq :: Parser Stmt
stmtneseq = atre <|> ife <|> whileE <|> skip

atre :: Parser Stmt
atre = do
            spaces
            y <- qid
            case y of
                (Qid x) -> do
                            symbol ":="
                            a <- aexp
                            spaces
                            return (AtrE x a)
                _ -> zero

seqp :: Parser Stmt
seqp = do
            x <- stmtneseq
            rest x
      where rest x = (
                     do
                        symbol ";"
                        y <- stmtneseq
                        rest (Seq x y)
                     )
                     <|> return x

ife :: Parser Stmt
ife = do
          symbol "if"
          symbol "("
          b <- bexp
          symbol ")"
          symbol "{"
          s1 <- stmt
          symbol "}"
          symbol "else"
          symbol "{"
          s2 <- stmt
          symbol "}"
          return (IfE b s1 s2)

whileE :: Parser Stmt
whileE =  do
              symbol "while"
              symbol "("
              b <- bexp
              symbol ")"
              symbol "{"
              s1 <- stmt
              symbol "}"
              return (WhileE b s1)

skip :: Parser Stmt
skip = do
          symbol "skip"
          return Skip

parseGet :: Parser a -> String -> a
parseGet p s = case parse p s of
    [] -> error "Parsing produced no results."
    (a, _):[] -> a
    _ -> error "Parsing produced multiple results."

sum_no :: String
sum_no = "'n:=100; 's:=0; 'i:=0; while ( ('i<= 'n)) { 's:='s+'i; 'i:= 'i+1} "

sum_no_p :: Stmt
sum_no_p = parseGet stmt sum_no

inf_cycle :: String
inf_cycle = "'n := 0; while (0 <= 0) {'n := 'n +1}"

inf_cycle_p :: Stmt
inf_cycle_p = parseGet stmt inf_cycle

recall :: String -> [(String, Int)] -> Int
recall key vars = case matches of
    (_, val):_ -> val
    [] -> error $ "Attempt to access uninitialized variable " ++ show key
    where matches = filter ((== key) . fst) vars

hasKey :: Eq a => a -> [(a, b)] -> Bool
hasKey key = any ((== key) . fst)

setValue :: Eq a => a -> b -> [(a, b)] -> [(a, b)]
setValue key val = map (\t@(k, _) -> if k == key then (k, val) else t)

update :: String -> Int -> [(String, Int)] -> [(String, Int)]
update key val vars = if hasKey key vars then setValue key val vars else (key, val) : vars

value :: AExp -> [(String, Int)] -> Int
value expr vars = case expr of
    Nu int -> int
    Qid key -> recall key vars
    PlusE a b -> v a + v b
    TimesE a b -> v a * v b
    DivE a b -> v a `div` v b
    where v e = value e vars

valueb :: BExp -> [(String, Int)] -> Bool
valueb expr vars = case expr of
    BE bool -> bool
    LE a b -> v a <= v b
    NotE a -> not $ vb a
    AndE a b -> vb a && vb b
    where
        v expr = value expr vars
        vb expr = valueb expr vars

bssos :: Stmt -> [(String, Int)] -> [(String, Int)]
bssos stmt vars = case stmt of
    AtrE name expr -> update name (value expr vars) vars
    Seq a b -> bssos b $ bssos a vars
    IfE expr true false -> bssos (if valueb expr vars then true else false) vars
    WhileE cond body -> if valueb cond vars then bssos stmt (bssos body vars) else vars
    Skip -> vars

prog :: Stmt
prog = sum_no_p

test_bssos :: [(String, Int)]
test_bssos = bssos prog []

-- This is where the new stuff starts

-- substitutes the QidX with the string by the the arithmetic expression
substaexp :: AExp -> String -> AExp -> AExp
substaexp exp searchStr replaceWith = case exp of
    (Nu _) -> exp
    (Qid str) -> if (str == searchStr) then replaceWith else exp
    (PlusE expr1 expr2) -> PlusE (subst expr1) (subst expr2)
    (TimesE expr1 expr2) -> TimesE (subst expr1) (subst expr2)
    (DivE expr1 expr2) -> DivE (subst expr1) (subst expr2)
    where subst expr = substaexp expr searchStr replaceWith

data Assn = BEX Bool | LEX AExp AExp | NotEX Assn | AndEX Assn Assn | DisjInfX [Assn]

-- value of an assertion relative to a state, similar to valueb
valueassn :: Assn -> [(String, Int)] -> Bool
valueassn assert vars = case assert of
    (BEX b) -> b
    (LEX l r) -> (value l vars) <= (value r vars)
    (NotEX a) -> not (v a)
    (AndEX a1 a2) -> (v a1) && (v a2)
    (DisjInfX aList) -> any v aList
    where v assert = valueassn assert vars

-- converts a boolean expression to an assertion
convassn :: BExp -> Assn
convassn bexp = case bexp of
    (BE b) -> BEX b
    (LE l r) -> LEX l r
    (NotE e) -> NotEX (convassn e)
    (AndE b1 b2) -> AndEX (convassn b1) (convassn b2)

-- substitutes the QidX with the string by the the arithmetic expression
substassn :: Assn -> String -> AExp -> Assn
substassn assert searchFor replaceWith = case assert of
    (BEX _) -> assert
    (LEX l r) -> LEX (subst_a l) (subst_a r)
    (NotEX notAssert) -> NotEX $ subst notAssert
    (AndEX a1 a2) -> AndEX (subst a1) (subst a2)
    (DisjInfX infList) -> DisjInfX $ fmap subst infList
    where subst a = substassn a searchFor replaceWith
          subst_a aexp = substaexp aexp searchFor replaceWith

-- logical or
orx :: Assn -> Assn -> Assn
orx p q = NotEX (AndEX (NotEX p) (NotEX q))

-- extracts the list
extr :: Assn -> [Assn]
extr (DisjInfX li) = li
extr _ = error "Must be a DisjInfX"

-- computes the weakest precondition
wp :: Stmt -> Assn -> Assn
wp st asrt = case st of
    Skip -> asrt
    (AtrE name aexp) -> substassn asrt name aexp
    (Seq s1 s2) -> wp s1 $ wp s2 asrt
    (IfE cond_ s_if s_else) -> (cond `AndEX` wp s_if asrt) `orx` (NotEX cond `AndEX` wp s_else asrt)
        where cond = convassn cond_
    (WhileE cond_ body) -> DisjInfX pInfList
        where cond = convassn cond_
              p0 = NotEX cond `AndEX` asrt
              pk_plus_1 pk = cond `AndEX` wp body pk
              pInfList = iterate pk_plus_1 p0

test1 :: Bool
test1 = valueassn (wp prog (LEX (Qid "s") (Nu 5051))) [] -- should return true

test2 :: Bool
test2 = valueassn (wp prog (LEX (Qid "s") (Nu 5050))) [] -- should return true

test3 :: Bool
test3 = valueassn (wp prog (LEX (Qid "s") (Nu 5049))) [] -- should not terminate

