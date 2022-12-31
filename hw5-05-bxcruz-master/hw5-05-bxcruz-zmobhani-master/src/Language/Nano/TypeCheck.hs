{-# LANGUAGE FlexibleInstances, OverloadedStrings, BangPatterns #-}

module Language.Nano.TypeCheck where

import Language.Nano.Types
import Language.Nano.Parser

import qualified Data.List as L
import           Text.Printf (printf)  
import           Control.Exception (throw)

--------------------------------------------------------------------------------
typeOfFile :: FilePath -> IO Type
typeOfFile f = parseFile f >>= typeOfExpr

typeOfString :: String -> IO Type
typeOfString s = typeOfExpr (parseString s)

typeOfExpr :: Expr -> IO Type
typeOfExpr e = do
  let (!st, t) = infer initInferState preludeTypes e
  if (length (stSub st)) < 0 then throw (Error ("count Negative: " ++ show (stCnt st)))
  else return t

--------------------------------------------------------------------------------
-- Problem 1: Warm-up
--------------------------------------------------------------------------------

-- | Things that have free type variables
class HasTVars a where
  freeTVars :: a -> [TVar]

-- | Type variables of a type
instance HasTVars Type where
  freeTVars TInt        = []          --empty if int
  freeTVars TBool       = []          --empty if bool
  freeTVars (TVar id)   = [id]        --show that var
  freeTVars (TList l)   = freeTVars l --recursion
  freeTVars (type1 :=> type2) = L.nub (freeTVars type1 ++ freeTVars type2)

-- | Free type variables of a poly-type (remove forall-bound vars)
instance HasTVars Poly where
  freeTVars (Mono t) = freeTVars t
  freeTVars (Forall id t) = L.delete id (freeTVars t)

-- | Free type variables of a type environment
instance HasTVars TypeEnv where
  freeTVars gamma   = concat [freeTVars s | (x, s) <- gamma]  
  
-- | Lookup a variable in the type environment  
lookupVarType :: Id -> TypeEnv -> Poly
lookupVarType x ((y, s) : gamma)
  | x == y    = s
  | otherwise = lookupVarType x gamma
lookupVarType x [] = throw (Error ("unbound variable: " ++ x))

-- | Extend the type environment with a new biding
extendTypeEnv :: Id -> Poly -> TypeEnv -> TypeEnv
extendTypeEnv x s gamma = (x,s) : gamma  

-- | Lookup a type variable in a substitution;
--   if not present, return the variable unchanged
lookupTVar :: TVar -> Subst -> Type
lookupTVar a [] = (TVar a)
lookupTVar a ((id, key):xs)       --list of x:xs of key value pairs
  | a == id = key                 --return type if found id
  | otherwise = lookupTVar a xs   --continue parsing list

-- | Remove a type variable from a substitution
removeTVar :: TVar -> Subst -> Subst
removeTVar a sub
  | (lookupTVar a sub) /= TVar a = L.delete (a, (lookupTVar a sub)) sub
  | otherwise = sub --lookupTVar returns (TVar a), aka isnt found
     
-- | Things to which type substitutions can be apply
class Substitutable a where
  apply :: Subst -> a -> a
  
-- | Apply substitution to type
instance Substitutable Type where  
  apply sub TInt              = TInt
  apply sub TBool             = TBool
  apply sub (TVar id)         = lookupTVar id sub
  apply sub (TList l)         = TList(apply sub l)
  apply sub (type1 :=> type2) = apply sub type1 :=> apply sub type2

-- | Apply substitution to poly-type
instance Substitutable Poly where    
  apply sub (Mono t)          = Mono(apply sub t)
  apply sub (Forall id t)     = Forall id (apply (removeTVar id sub) t)

-- | Apply substitution to (all poly-types in) another substitution
instance Substitutable Subst where  
  apply sub to = zip keys $ map (apply sub) vals
    where
      (keys, vals) = unzip to
      
-- | Apply substitution to a type environment
instance Substitutable TypeEnv where  
  apply sub gamma = zip keys $ map (apply sub) vals
    where
      (keys, vals) = unzip gamma
      
-- | Extend substitution with a new type assignment
extendSubst :: Subst -> TVar -> Type -> Subst
extendSubst sub a t = (a, apply sub t) : apply [(a,t)] sub
      
--------------------------------------------------------------------------------
-- Problem 2: Unification
--------------------------------------------------------------------------------
      
-- | State of the type inference algorithm      
data InferState = InferState { 
    stSub :: Subst -- ^ current substitution
  , stCnt :: Int   -- ^ number of fresh type variables generated so far
} deriving (Eq,Show)

-- | Initial state: empty substitution; 0 type variables
initInferState = InferState [] 0

-- | Fresh type variable number n
freshTV n = TVar $ "a" ++ show n      
    
-- | Extend the current substitution of a state with a new type assignment   
extendState :: InferState -> TVar -> Type -> InferState
extendState (InferState sub n) a t = InferState (extendSubst sub a t) n
        
-- | Unify a type variable with a type; 
--   if successful return an updated state, otherwise throw an error
unifyTVar :: InferState -> TVar -> Type -> InferState
unifyTVar st a t 
  | (TVar a) == t = st
  | L.elem a (freeTVars t) = throw (Error ( "type error: cannot unify" ++ (show a) ++ " and " ++ (show t) ++ "(occurs check)"))
  | otherwise = extendState st a t

-- | Unify two types;
--   if successful return an updated state, otherwise throw an error
unify :: InferState -> Type -> Type -> InferState
unify st t1 t2 = helper st t1' t2'
  where
    t1' = apply (stSub st) t1 
    t2' = apply (stSub st) t2 
    helper st TInt TInt = st
    helper st TBool TBool = st
    helper st (TVar a1) a2 = unifyTVar st a1 a2
    helper st a1 (TVar a2) = unifyTVar st a2 a1
    helper st (TList a1) (TList a2) = unify st a1 a2
    helper st (a1 :=> a2) (a3 :=> a4) = unify (unify st a1 a3) a2 a4
    helper _ t1 t2 = throw (Error ("type error: cannot unify " ++ (show t1) ++ " and " ++ (show t2)))

--------------------------------------------------------------------------------
-- Problem 3: Type Inference
--------------------------------------------------------------------------------    
freshTVtracker :: InferState -> (InferState, Type)
freshTVtracker is = ((InferState (stSub is) (stCnt is + 1)), freshTV(stCnt is))

infer :: InferState -> TypeEnv -> Expr -> (InferState, Type)
infer st _   (EInt _)          = (st, TInt)
infer st _   (EBool _)         = (st, TBool)
infer st gamma (EVar x)        = (st', t)
  where 
    numFresh = stCnt st
    currSub = stSub st
    (id, t) = instantiate numFresh (lookupVarType x gamma)
    st' = InferState currSub id

infer st gamma (ELam x body)   = (stRet, argType :=> bodyType)
  where (st', argTypeVar) = freshTVtracker st
        gamma'            = extendTypeEnv x (Mono argTypeVar) gamma
        (stRet, bodyType) = infer st' gamma' body
        argType           = apply (stSub stRet) argTypeVar
        
infer st gamma (EApp e1 e2) = (stRet, resultType)
  where
    (st', funType) = infer st gamma e1
    gamma'                  = apply (stSub st') gamma 
    (st'', argType)         = infer st' gamma e2
    (st''', resultTypeVar)  = freshTVtracker st'' 
    stRet                   = unify st''' funType (argType :=> resultTypeVar)
    resultType              = apply (stSub stRet) resultTypeVar

infer st gamma (ELet x e1 e2)  = infer st''' ext e2
  where 

    freshX = (freshTV (stCnt st))
    gamma' = extendTypeEnv x (Mono freshX) gamma
    -- gamma ' = gamma ++ [(x, Mono freshX)] -- or
    st' = InferState (stSub st) (stCnt st + 1)
    (st'', t) = infer st' gamma' e1
    st''' = unify st'' freshX t
    gen = generalize gamma t
    ext = extendTypeEnv x gen gamma
    

infer st gamma (EBin op e1 e2) = infer st gamma asApp
  where
    asApp = EApp (EApp opVar e1) e2
    opVar = EVar (show op)

infer st gamma (EIf c e1 e2) = infer st gamma asApp
  where
    asApp = EApp (EApp (EApp ifVar c) e1) e2
    ifVar = EVar "if"    
infer st gamma ENil = infer st gamma (EVar "[]")

-- | Generalize type variables inside a type
generalize :: TypeEnv -> Type -> Poly
generalize gamma t = foldl gen (Mono t) free
    where
      gen mono free = Forall free mono
      --mono = Mono t
      free = L.nub((freeTVars t) L.\\ (freeTVars gamma)) 
    
-- | Instantiate a polymorphic type into a mono-type with fresh type variables
instantiate :: Int -> Poly -> (Int, Type)
instantiate n (Mono s) = (n,s)                                                --single case
instantiate n (Forall id t) = instantiate (n+1) (apply [(id, (freshTV n))] t) --line 89 and 90 format
      
-- | Types of built-in operators and functions      
preludeTypes :: TypeEnv
preludeTypes =
  [ ("+",    Mono $ TInt :=> TInt :=> TInt)
  , ("-",    Mono $ TInt :=> TInt :=> TInt)
  , ("*",    Mono $ TInt :=> TInt :=> TInt)
  , ("/",    Mono $ TInt :=> TInt :=> TInt)
  , ("==",   Forall "t" $ Mono $ TVar "t" :=> TVar "t" :=> TBool)
  , ("!=",   Forall "t" $ Mono $ TVar "t ":=> TVar "t" :=> TBool)
  , ("<",    Mono $ TInt :=> TInt :=> TBool)
  , ("<=",   Mono $ TInt :=> TInt :=> TBool)
  , ("&&",   Mono $ TBool :=> TBool :=> TBool)
  , ("||",   Mono $ TBool :=> TBool :=> TBool)
  , ("if",   Forall "t" $ Mono $ TBool :=> TVar "t" :=> TVar "t" :=> TVar "t")
  -- lists: 
  , ("[]",   Forall "t" $ Mono $ TList (TVar "t"))
  , (":",    Forall "t" $ Mono $ TVar "t" :=> TList (TVar "t") :=> TList (TVar "t"))
  , ("head", Forall "t" $ Mono $ TList (TVar "t") :=> TVar "t")
  , ("tail", Forall "t" $ Mono $ TList (TVar "t") :=> TList (TVar "t"))
  ]
