module Main where

import qualified Data.Map as Map
import Data.List (find)
import Data.Maybe (isNothing, fromMaybe)
import Data.Foldable (asum)

-- Literals are either positive or negations of a variable.
data Literal a = Positive a | Negative a
instance (Show a) => Show (Literal a) where
  show (Positive a) = show a
  show (Negative a) = "¬" ++ show a

-- Returns the variable in a literal.
variable :: Literal a -> a
variable (Positive a) = a
variable (Negative a) = a

-- Checks if the given valuation satisfies a literal.
satisfies :: Literal a -> Bool -> Bool
satisfies l = (==) (satisfiedBy l)

-- Returns the value satisfying the litteral.
satisfiedBy :: Literal a -> Bool
satisfiedBy (Positive _) = True
satisfiedBy (Negative _) = False

-- Clauses are disjunctions of literals.
newtype Clause a = Clause [Literal a]
instance (Show a) => Show (Clause a) where
  show (Clause []) = ""
  show (Clause [l]) = show l
  show (Clause (l : tl)) = show l ++ " v " ++ show (Clause tl)

-- Returns the literals contained in a clause.
clauseLiterals :: Clause a -> [Literal a]
clauseLiterals (Clause c) = c

-- Formulas are cunjonction of clauses.
newtype Formula a = Formula [Clause a]
instance (Show a) => Show (Formula a) where
  show (Formula []) = ""
  show (Formula [l]) = "(" ++ show l ++ ")"
  show (Formula (l : tl)) = "(" ++ show l ++ ")" ++ " ∧ " ++ show (Formula tl)

-- Returns the literals contained in a formula.
literals :: Formula a -> [Literal a]
literals (Formula f) = concatMap clauseLiterals f

-- A valuation is a mapping from variables to booleans.
newtype Valuation a = Valuation (Map.Map a Bool)
instance (Show a)  => Show (Valuation a) where
  show (Valuation v) = Map.foldlWithKey (\acc v b -> acc ++ "\n" ++ show v ++ " -> " ++ show b) [] v

-- Checks if a literal is satified by the current valuation.
-- Returns Nothing if the literal is unassigned.
literalIsSatisfied :: Ord a => Literal a -> Valuation a -> Maybe Bool
literalIsSatisfied l (Valuation v) = Map.lookup (variable l) v >>= Just . satisfies l

-- The empty valuation.
emptyValuation :: Valuation a
emptyValuation = Valuation Map.empty

-- Assigns a boolean value to a variable in a valuation.
assign :: Ord a => a -> Bool -> Valuation a -> Valuation a
assign l b (Valuation v) = Valuation $ Map.insert l b v

-- Evaluates a clause given a valuation.
-- Returns Nothing if the clause contains only literals evaluating to false and at least one residue.
evaluateClause :: Ord a => Clause a -> Valuation a -> Maybe Bool
evaluateClause (Clause []) _ = Just True
evaluateClause (Clause [l]) v = literalIsSatisfied l v
evaluateClause (Clause (l : tl)) v = literalIsSatisfied l v >>= (\sat -> if sat then Just True else evaluateClause (Clause tl) v)

-- Evaluates a formula given a valuation.
-- Returns Nothing if any clause contains only literals evaluaing to false and at least one residue.
evaluateFormula :: Ord a => Formula a -> Valuation a -> Maybe Bool
evaluateFormula (Formula []) _ = Just True
evaluateFormula (Formula [c]) v = evaluateClause c v
evaluateFormula (Formula (c : tl)) v = case evaluateClause c v of
  Just True -> evaluateFormula (Formula tl) v
  r -> r

-- Unit propagation on a formula given a valuation.
unitPropagation :: Ord a => Formula a -> Valuation a -> Valuation a
unitPropagation (Formula []) v = v
unitPropagation (Formula (c : tl)) v = 
  let unitary = findUnitary Nothing c in
  let new_valuation = fromMaybe v (unitary >>= (\l -> Just $ assign (variable l) (satisfiedBy l) v)) in
  unitPropagation (Formula tl) new_valuation
  where
  findUnitary unit (Clause []) = unit
  findUnitary unit (Clause (l : tl)) = case literalIsSatisfied l v of
    Just sat -> if sat then Nothing else findUnitary unit (Clause tl)
    Nothing -> if isNothing unit then findUnitary (Just l) (Clause tl) else Nothing

-- Chooses one unassigned variable in the formula, and returns the possible choices
-- of value for said variable.
choiceUnassigned :: Ord a => Formula a -> Valuation a -> [Valuation a]
choiceUnassigned formula@(Formula f) v =
  let unassigned = find (\l -> isNothing $ literalIsSatisfied l v) (literals formula) in
  case unassigned of
    Just l -> [assign (variable l) False v, assign (variable l) True v]
    Nothing -> []

-- DPLL algorithm to find wether a formula is satisfiable.
dpll :: Ord a => Formula a -> Maybe (Valuation a)
dpll f = dpll' f emptyValuation
  where
  dpll' :: Ord a => Formula a -> Valuation a -> Maybe (Valuation a)
  dpll' f v = 
    let valuation = unitPropagation f v in
    case evaluateFormula f valuation of
      Just True -> Just valuation
      Just False -> Nothing
      Nothing -> asum (map (dpll' f) (choiceUnassigned f valuation))
      
main :: IO ()
main = do
  putStrLn "DPLL/CDCL solver in Haskell"
