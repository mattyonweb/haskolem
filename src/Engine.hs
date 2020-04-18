{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UnicodeSyntax #-}

module Engine where

import Data.List
import Data.Maybe
import Data.Char
import Control.Monad
import Control.Arrow
import qualified Data.Set as Set

data Expr =
    Forall Expr Expr
  | Exists Expr Expr
  | T
  | F
  | V String
  | Not Expr
  | And Expr Expr
  | Or Expr Expr
  | Func String [Expr]
  | Pred String [Expr]
  deriving (Eq, Ord, Read)

instance Show Expr where
  show T = "True"
  show F = "False"
  show (V s) = s
  show (Not e) = "¬" ++ show e
  show (And e1 e2) = "(" ++ show e1 ++ "∧" ++ show e2 ++ ")"
  show (Or e1 e2)  = "(" ++ show e1 ++ "∨" ++ show e2 ++ ")"
  show (Forall e1 e2) = "∀" ++ show e1 ++ "(" ++ show e2 ++ ")"
  show (Exists e1 e2) = "∃" ++ show e1 ++ "(" ++ show e2 ++ ")"
  show (Func c []) = c
  show (Func c args) = c ++ "(" ++ (intercalate "," $ map show args) ++ ")"
  show (Pred r []) = map toUpper r
  show (Pred r args) = map toUpper r ++ "(" ++ (intercalate "," $ map show args) ++ ")"
  
a ∧ b = And a b
a ∨ b = Or  a b

-- Servirà MOLTO più avanti
apply :: (Expr -> Expr) -> Expr -> Expr
apply f (Not e) = f (Not (apply f e))
apply f (And e1 e2) = f (And (apply f e1) (apply f e2))
apply f (Or e1 e2) = f (Or (apply f e1) (apply f e2))
apply f (Forall v e) = f (Forall (apply f v) (apply f e))
apply f (Exists v e) = f (Exists (apply f v) (apply f e))
apply f e = f e

ex1 = Forall (V "x")
        (Exists (V "y")
            ((V "x") ∨ (V "y")))

-------------------------------------------------------------
-- Trasformazione in forma normale vattelapesca.
-- Queste sono tranquillissime sostituzioni di logica
-- proposizionale, niente di cui temere.

type Transformation = Expr -> Expr

--  ¬∀x(y) ↔ ∃x(¬y)
notForallRule :: Transformation
notForallRule (Not (Forall v x)) = Exists v (Not x)
notForallRule e = e

-- Non ho voglia di scrivere i simbolini hai capito
notExistsRule :: Transformation
notExistsRule (Not (Exists v x)) = Forall v (Not x)
notExistsRule e = e

-- Doppia negazione
notNotRule :: Transformation
notNotRule (Not (Not x)) = x
notNotRule e = e


firstRules :: [Transformation]
firstRules = [notForallRule, notExistsRule, notNotRule]

{-
Questa funzione applica la lista di trasformazioni finché non
diventa idempotente.
Aka: applica le trasformazioni a sfinimento e quando non ottiene
più espressioni nuove ritorna ciò che ha trovato. -}
myFix :: [Transformation] -> Expr -> Expr
myFix ts e =
    if res == e
    then res
    else myFix ts res
  where res = foldl (\acc f -> apply f acc) e ts 


-------------------------------------------------------------
-- Trasformazione in forma normale prenessa.
-- Qua in pratica spingiamo i quantificatori verso la sinistra
-- in previsione della skolemizzazione.

--
foldExpr :: (Expr -> Maybe a) -> Expr -> [a]
foldExpr f (Not e) = (maybeToList $ f (Not e)) ++ foldExpr f e 
foldExpr f (And e1 e2) = (maybeToList $ f (And e1 e2)) ++ foldExpr f e1 ++ foldExpr f e2
foldExpr f (Or e1 e2) = (maybeToList $ f (Or e1 e2)) ++ foldExpr f e1 ++ foldExpr f e2
foldExpr f (Forall v e) = (maybeToList $ f (Forall v e)) ++ foldExpr f v ++ foldExpr f e
foldExpr f (Exists v e) = (maybeToList $ f (Exists v e)) ++ foldExpr f v ++ foldExpr f e
foldExpr f other = maybeToList $ f other


-- Ritorna i nomi presenti in un'espressione
namesInside :: Expr -> Set.Set String
namesInside = Set.fromList . foldExpr getName
  where getName (Forall (V s) _) = Just s
        getName (Exists (V s) _) = Just s
        getName (V s) = Just s
        getName (Func c _) = Just c
        getName (Pred r _) = Just r
        getName _ = Nothing


-- Genera nuovo nome non presente nella lista di nomi
newName :: String -> Set.Set String -> String
newName s names =
  if Set.notMember s names
  then s
  else newName (s ++ "'") names


-- Sostituisce il nome di una variabile con un altro nome
subName :: String -> String -> Expr -> Expr
subName s1 s2 (V v) = if s1 == v then V s2 else (V s1)
subName _ _ e = e


-- Rinomina ogni occorrenza di s nell'espressione
rename :: Expr -> String -> Expr
rename e s =
    if Set.notMember s alreadyInside
    then e
    else apply (subName s (newName s alreadyInside)) e
  where alreadyInside = namesInside e 


-- Regole vere e proprie di trasformazione

existsAndRule :: Transformation
existsAndRule (And (Exists (V v) e1) e2) = Exists (V v) (e1 ∧ rename e2 v) 
existsAndRule (And e2 (Exists (V v) e1)) = Exists (V v) (e1 ∧ rename e2 v) 
existsAndRule other = other

existsOrRule :: Transformation
existsOrRule (Or (Exists (V v) e1) e2) = Exists (V v) (e1 ∨ rename e2 v) 
existsOrRule (Or e2 (Exists (V v) e1)) = Exists (V v) (e1 ∨ rename e2 v) 
existsOrRule other = other

forallAndRule :: Transformation
forallAndRule (And (Forall (V v) e1) e2) = Forall (V v) (e1 ∧ rename e2 v) 
forallAndRule (And e2 (Forall (V v) e1)) = Forall (V v) (e1 ∧ rename e2 v) 
forallAndRule other = other

forallOrRule :: Transformation
forallOrRule (Or (Forall (V v) e1) e2) = Forall (V v) (e1 ∨ rename e2 v) 
forallOrRule (Or e2 (Forall (V v) e1)) = Forall (V v) (e1 ∨ rename e2 v) 
forallOrRule other = other

pushOutRules = [existsAndRule, existsOrRule, forallAndRule, forallOrRule]

ex2 = Forall (V "x")
        (Exists (V "y")
            ((V "x") ∧ (Exists (V "z") ((V "y") ∧ (V "z")))))
ex3 = And (Exists (V "x") (Or (V "x") (V "x"))) (Exists (V "x") (And (V "x") T)) 


-------------------------------------------------------------
-- Skolemizzazione.
-- Sostituisco gli x introdotti da un ∃ con f(t1..tn) 


-- Sostituisco le variabili (V s1) con una (Func "sklm" [...])
subVarSkolem :: String -> Expr -> Transformation
subVarSkolem s1 func (V v) = if s1 == v then func else (V v)
subVarSkolem _ _ e = e

-- Cerca un nuovo nome per la funzione di skolem introdotta
-- (se necessario), quindi rinomina le variabili introdotte
-- da un ∃
renameSkolem :: String -> [Expr] -> Transformation
renameSkolem s args e =
    if Set.notMember "sklm" alreadyInside
    then apply (subVarSkolem s (Func "sklm" args)) e
    else apply (subVarSkolem s (Func (newName "sklm" alreadyInside) args)) e
  where alreadyInside = namesInside e

-- Skolemizzazione vera e propria
skolem :: [Expr] -> Transformation
skolem univ (Exists (V s) e) = skolem univ $ renameSkolem s univ e
skolem univ (Forall (V s) e) = skolem ((V s) : univ) e
skolem _ other = other


cost :: String -> Expr
cost s = Func s []

ex4 =
  Forall (V "x")
    (Exists (V "y")
      (Or
         (And (And (V "x") (Not (V "x"))) (V "y"))
         (Exists (V "z") (And (And (V "y") (Not (V "y"))) (V "z")))))



-------------------------------------------------------------
-- Forma Normale Congiuntiva
-- Passare in forma normale congiunta, quindi congiunzioni di disgiunzioni 

data Clause = Clause [Expr] [Expr] deriving (Eq, Ord)
instance Show Clause where
  show (Clause n p) =
    (intercalate ";" (map show n)) ++ " => " ++ (intercalate ";" (map show p))
  
fncRule1 :: Transformation
fncRule1 (Not (Or x y)) = (Not x) ∧ (Not y)
fncRule1 e = e

fncRule2 :: Transformation
fncRule2 (Not (And x y)) = (Not x) ∨ (Not y)
fncRule2 e = e

fncRule3 :: Transformation
fncRule3 (Or a (And b c)) = And (Or a b) (Or a c)
fncRule3 e = e

fncRule4 :: Transformation
fncRule4 (Or (And b c) a) = And (Or a b) (Or a c)
fncRule4 e = e

fncRules = [notNotRule, fncRule1, fncRule2, fncRule3, fncRule4]

-------------------------------------------------------------
-- Ora generiamo le clausole vere e proprie

isLit :: Expr -> Bool
isLit T = True
isLit F = True
isLit (V _) = True
isLit (Func _ _) = True
isLit (Pred _ _) = True
isLit (Not e) = isLit e
isLit _ = False


-- Genera la clausola per una disgiunzione
genDisjClaus :: Expr -> Clause
genDisjClaus (Or e1 e2) = Clause (n1 ++ n2) (p1 ++ p2)
  where (Clause n1 p1) = genDisjClaus e1 
        (Clause n2 p2) = genDisjClaus e2
genDisjClaus (Not t) =
  if not (isLit t)
  then error "Prevista FNC ma trovata espressione non in FNC"
  else Clause [t] []
genDisjClaus t =
  if not (isLit t)
  then error "Prevista FNC ma trovata espressione non in FNC"
  else Clause [] [t]


-- Crea le clausole di una espressione qualsiasi
genClaus :: Expr -> [Clause]
genClaus (And e1 e2) = genClaus e1 ++ genClaus e2
genClaus e = [genDisjClaus e]

-- Pretty printing
pprintClauses :: [Clause] -> IO ()
pprintClauses cs = mapM_ print $ cs

-------------------------------------------------------------
-- Ottimizzazioni sulle clausole.

-- Δ ⇒ Δ è ridondante
opt1 :: Clause -> Bool
opt1 (Clause n p) = n /= p

-- Riordina i letterali per effettuare ottimizazioni (cfr. opt1)
opt2 :: Clause -> Clause
opt2 (Clause n p) = Clause (Set.toList $ Set.fromList n)
                           (Set.toList $ Set.fromList p)

-- Δ,A ⇒ Γ,A ≡ A ⇒ A che è tautologia
opt3 :: Clause -> Bool
opt3 (Clause n p) = [] == intersect n p

-- Altre tautologie
opt4 :: Clause -> Bool
opt4 (Clause [] [T]) = False
opt4 (Clause [F] []) = False
opt4 _ = True


ottimizzazioni = [
    filter opt3
  , (Set.toList . Set.fromList)
  , filter opt1
  , map opt2
  , filter opt1
  ]

-- Coq
mapi :: (a -> Int -> b) -> [a] -> [b]
mapi f l = map (uncurry f) (zip l [0..])


-- Lift IO per le funzioni di ottimizzazione su clausole;
-- Sembra complicata, in realtà è solo un po' di testo carino
-- e scritte informative
liftOptzs :: (Show a, Eq a) => String -> (a -> a) -> (a -> IO a)  
liftOptzs name f = \a -> do
  putStrLn $ name ++ ":"
  let result = f a in
    if result == a
    then return result
    else do
      putStrLn $ "\tInput:  " ++ show a ;
      putStrLn $ "\tResult: " ++ show result ;
      return result


-- Non usato in pratica, più bello usare IO
optz :: [Clause] -> [Clause]  
optz = foldl (.) id ottimizzazioni

-- Fa un "merge" di tutte le ottimizazioni in un'unica funzione
-- che stampa utili informazioni di debug in IO
optzIO :: [Clause] -> IO [Clause]
optzIO = foldl (>=>) return $
  mapi (\foo i -> liftOptzs ("Optim." ++ show i) foo) ottimizzazioni


-- Versione più generica di liftOptzs ma sostanzialmente simile.
liftDebug :: (Show a, Show b) => String -> (a -> b) -> (a -> IO b)
liftDebug stepName f = \a -> do
  putStrLn $ stepName ++ ":"
  putStrLn $ "\tInput:  " ++ show a
  let result = f a in do
    putStrLn $ "\tResult: " ++ show result ;
    return result

skolemIO =
  liftDebug "Preliminari" (myFix firstRules) >=>
  liftDebug "Push-out rules" (myFix (pushOutRules ++ firstRules)) >=>
  liftDebug "Skolemizzazione" (skolem []) >=>
  liftDebug "Verso FNCongiuntiva" (myFix fncRules) >=>
  liftDebug "FNC" genClaus >=>
  liftDebug "Riduzioni" optz >=>
  optzIO

skolemMultipleIO :: [Expr] -> IO [Clause] 
skolemMultipleIO es = do
  listsClauses <- mapM skolemIO es
  return $ concat listsClauses


-------------------------------------------------------------

solverIO =
  skolemIO >=>
  liftDebug "out" attemptSolution

solverMultipleIO =
  skolemMultipleIO >=>
  liftDebug "out" attemptSolution
  
  
data Judgment = NonSAT | Unknown String | Taut
  deriving (Show, Eq)

impossibleClause1 :: Clause -> Bool
impossibleClause1 (Clause n _) =
  T `elem` n

attemptSolution :: [Clause] -> Judgment
attemptSolution [] = Taut
attemptSolution xs =
  case find impossibleClause1 xs of
    Nothing -> Unknown "a"
    Just _  -> NonSAT


-- -------------------------------------------------------------
-- Da qui in poi sperimentale
resFatt :: Clause -> Clause -> Clause
resFatt (Clause n1 p1) (Clause n2 p2) =
  Clause (fatt $ del_n1 ++ del_n2) (fatt $ del_p1 ++ del_p2)

  where del_n1 = filter (\e -> not (e `elem` p2)) n1 
        del_p2 = filter (\e -> not (e `elem` n1)) p2

        del_p1 = filter (\e -> not (e `elem` n2)) p1
        del_n2 = filter (\e -> not (e `elem` p1)) n2

        fatt :: Ord a => [a] -> [a]
        fatt = Set.toList . Set.fromList
