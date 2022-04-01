import qualified Data.Map as Map

data TConst = TOne | TZero deriving (Show, Eq)
data TOp = TTensor | TPlus | TWith deriving (Show, Eq)

data Type 
  = TConst TConst
  | TOp TOp Type Type
  | TMu String Type
  | TVar String
  deriving (Show, Eq)

type Substitution = Map.Map String Type

compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = fmap (subst s1) s2 `Map.union` s1

free :: Type -> [String]
free (TConst _)    = []
free (TOp _ t1 t2) = free t1 ++ free t2
free (TMu x t)     = filter (/= x) (free t)
free (TVar x)      = [x]

subst :: Substitution -> Type -> Type
subst _ (TConst c)     = TConst c
subst s (TOp op t1 t2) = TOp op (subst s t1) (subst s t2)
subst s (TMu x t)      = TMu x (subst (Map.delete x s) t)
subst s (TVar x)       = case Map.lookup x s of
  Just t  -> t
  Nothing -> TVar x

rename :: String -> String -> Type -> Type
rename v v' = subst (Map.singleton v (TVar v'))

mguPrim :: Bool -> Type -> Type -> Either String Substitution
mguPrim _ (TConst c1) (TConst c2)
  | c1 == c2  = pure Map.empty
  | otherwise = Left $ "can't unify " ++ show c1 ++ " and " ++ show c2
mguPrim b (TOp op t1 t2) (TOp op' t1' t2')
  | op == op' = do
      s1 <- mguPrim b t1 t1'
      s2 <- mguPrim b (subst s1 t2) (subst s1 t2')
      pure (s2 `compose` s1)
  | otherwise = Left $ "can't unify " ++ show (TOp op t1 t2) ++ " and " ++ show (TOp op' t1' t2')
mguPrim b (TMu v t) (TMu v' t')
  | v == v'   = mguPrim b t t'
  | otherwise = mguPrim b t (rename v' v t')
mguPrim _ (TVar v) t
  | t == TVar v     = pure Map.empty
  | v `elem` free t = Left $ "occurs check failed: " ++ v ++ " in " ++ show t
  | otherwise       = pure (Map.singleton v t)
mguPrim b t (TVar v) = if b
  then mguPrim b (TVar v) t
  else Left $ "can't unify " ++ show t ++ " to given type variable " ++ v ++ " which is more general"
mguPrim _ a b = Left $ "can't unify " ++ show a ++ " and " ++ show b

mgu :: Type -> Type -> Either String Substitution
mgu = mguPrim True

mguTo :: Type -> Type -> Either String Substitution
mguTo = mguPrim False