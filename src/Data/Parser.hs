{-# LANGUAGE RankNTypes,
             GADTs,
             TypeFamilies,
             MultiParamTypeClasses,
             FlexibleInstances,
             DeriveFunctor,
             GeneralizedNewtypeDeriving,
             ScopedTypeVariables #-}

module Data.Parser where

------------------------------------------------------------------------------
import           Control.Applicative
import           Control.Monad (unless)
import           Control.Monad.State (StateT, gets, modify, execStateT, lift)
import           Data.TypedMap (Ord1 (..), Eq1 (..), P (..), Show2 (..), Show1 (..))
import qualified Data.TypedMap as TM
import qualified Data.TypedSet as TS
import           Control.Monad.ST
import           Data.STRef

------------------------------------------------------------------------------
data RHS nt tok v a where
    Return  :: a                                -> RHS nt tok v a
    Choice  :: RHS nt tok v a -> RHS nt tok v a -> RHS nt tok v a
    Failure ::                                     RHS nt tok v a
    Token   :: (tok -> RHS nt tok v a)          -> RHS nt tok v a
    NT      :: nt b -> (v b -> RHS nt tok v a)  -> RHS nt tok v a

type Grammar nt tok f = forall v a. nt a -> RHS nt tok v (f v a)

------------------------------------------------------------------------------
-- An example
data Expr
data Sent

data AST v category where
    Exp    :: v Expr           -> AST v Sent
    VarExp ::                     AST v Expr
    AddExp :: v Expr -> v Expr -> AST v Expr

instance Show2 AST where
    show2 (Exp e)        = show1 e
    show2 VarExp         = "x"
    show2 (AddExp e1 e2) = "(" ++ show1 e1 ++ "+" ++ show1 e2 ++ ")"

data NT category where
    Expr  :: NT Expr
    Expr' :: NT Expr
    Sent  :: NT Sent

instance Eq1 NT where
    Expr === Expr = Just TM.Refl
    Expr' === Expr' = Just TM.Refl
    Sent === Sent = Just TM.Refl
    _    === _    = Nothing

instance Ord1 NT where
    compare1 Expr  Expr  = TM.EQ1
    compare1 Sent  Sent  = TM.EQ1
    compare1 Sent  Expr  = TM.LT1
    compare1 Expr  Sent  = TM.GT1
    compare1 Expr' Expr' = TM.EQ1
    compare1 Expr' _     = TM.LT1
    compare1 Expr  Expr' = TM.GT1
    compare1 Sent  Expr' = TM.GT1

expr :: Grammar NT Char AST
expr Sent =
    NT Expr (\e -> Return (Exp e))
expr Expr =
    Choice (Token (\tok -> if tok == 'x' then Return VarExp else Failure))
           (NT Expr (\e1 -> Token (\tok -> if tok == '+' then NT Expr (\e2 -> Return (AddExp e1 e2)) else Failure)))

expr2 :: Grammar NT Char AST
expr2 Sent =
    NT Expr (Return . Exp)
expr2 Expr =
    Choice (Token (\tok -> if tok == 'x' then Return VarExp else Failure))
           (NT Expr (\e1 -> Token (\tok -> if tok == '+' then NT Expr' (\e2 -> Return (AddExp e1 e2)) else Failure)))
expr2 Expr' =
    Token (\tok -> if tok == 'x' then Return VarExp else Failure)

------------------------------------------------------------------------------
class (Functor m, Monad m) => ParseResultsMonad f m where
    type ResultNode f m :: * -> *

    newResult :: Int -> Int -> f (ResultNode f m) x -> m (ResultNode f m x)
    addResult :: ResultNode f m x -> f (ResultNode f m) x -> m ()

data Item nt tok f m where
    Item :: RHS nt tok (ResultNode f m) (f (ResultNode f m) b)
         -> StackNode nt tok f m b
         -> Item nt tok f m

{-
    Top  :: nt b
         -> StackNode nt tok f m b
         -> Item nt tok f m
    Fin  :: ResultNode f m a
         -> StackNode nt tok f m a
         -> Item nt tok f m
-}
------------------------------------------------------------------------------
data WaitingItem nt tok f m a where
    WItem :: (ResultNode f m a ->
                  RHS nt tok (ResultNode f m) (f (ResultNode f m) b))
          -> StackNode nt tok f m b
          -> WaitingItem nt tok f m a
{-
    WTop  :: StackNode nt tok f m b
          -> WaitingItem nt tok f m b
-}

ofWaiting :: ResultNode f m a
          -> WaitingItem nt tok f m a
          -> Item nt tok f m
ofWaiting node (WItem k returnAddress) = Item (k node) returnAddress
--ofWaiting node (WTop  returnAddress)   = Fin node returnAddress

class ParseResultsMonad f m => ParseStackMonad nt tok f m where
    data StackNode nt tok f m :: * -> *

    newStackNode     :: Int -> nt a -> m (StackNode nt tok f m a)
    addToStackNode   :: WaitingItem nt tok f m a -> StackNode nt tok f m a -> m ()
    readStackNode    :: StackNode nt tok f m a -> m [WaitingItem nt tok f m a]
    getPositionAndNT :: StackNode nt tok f m a -> m (Int, nt a)

------------------------------------------------------------------------------
data Fix1 f a = In Int Int (f (Fix1 f) a)

instance Show2 f => Show1 (Fix1 f) where
    show1 (In i j x) = show2 x

data AmbiguityCheckResult f a where
    UnambiguousResult :: a -> AmbiguityCheckResult f a
    AmbiguityDetected :: Int -> Int -> f (Fix1 f) b -> f (Fix1 f) b -> AmbiguityCheckResult f a
    -- and also parse failures, where we would like to print out a
    -- stack trace, or at least a list of things that failed.

instance Functor (AmbiguityCheckResult f) where
    fmap f (UnambiguousResult a)       = UnambiguousResult (f a)
    fmap f (AmbiguityDetected i j x y) = AmbiguityDetected i j x y

instance (Show2 f, Show a) => Show (AmbiguityCheckResult f a) where
    show (UnambiguousResult a)       = "UnambiguousResult (" ++ show a ++ ")"
    show (AmbiguityDetected i j x y) = "AmbiguityDetected (" ++ show i ++ ", " ++ show j ++ ") : " ++ show2 x ++ " and " ++ show2 y


instance Show (Fix1 AST a) where
    show (In _ _ (Exp e))        = show e
    show (In _ _ VarExp)         = "x"
    show (In _ _ (AddExp e1 e2)) = "(" ++ show e1 ++ "+" ++ show e2 ++ ")"

newtype StGraphM f s a = STGM { unSTGM :: ST s (AmbiguityCheckResult f a) }
    deriving (Functor)

instance Monad (StGraphM f s) where
    return x = STGM (return (UnambiguousResult x))
    STGM c >>= f =
        STGM $ do
          a <- c
          case a of
            UnambiguousResult a -> unSTGM (f a)
            AmbiguityDetected i j x y -> return (AmbiguityDetected i j x y)

instance ParseResultsMonad f (StGraphM f s) where
    type ResultNode f (StGraphM f s) = Fix1 f

    newResult i j result   = STGM (return (UnambiguousResult (In i j result)))
    addResult (In i j x) y = STGM (return (AmbiguityDetected i j x y))

data STStackNode nt tok f s a =
  STSN { position :: (Int, nt a)
       , witems   :: [WaitingItem nt tok f (StGraphM f s) a]
       }

instance ParseStackMonad nt tok f (StGraphM f s) where
    data StackNode nt tok f (StGraphM f s) a = SN (STRef s (STStackNode nt tok f s a))

    newStackNode i nt =
        STGM $ UnambiguousResult <$> (SN <$> newSTRef (STSN (i, nt) []))

    addToStackNode witem (SN ref) =
        STGM $ UnambiguousResult <$> (modifySTRef ref $ \s -> s { witems = witem:witems s })

    readStackNode (SN ref) =
        STGM $ UnambiguousResult <$> (witems <$> readSTRef ref)

    getPositionAndNT (SN ref) =
        STGM $ UnambiguousResult <$> (position <$> readSTRef ref)

------------------------------------------------------------------------------
parse :: (Ord1 nt, ParseStackMonad nt tok f m) =>
         Grammar nt tok f
      -> nt a
      -> [tok]
      -> m (Maybe (ResultNode f m a))
parse grammar nt input = do
  stackNode <- newStackNode 0 nt
  go [Item (grammar nt) stackNode] 0 input
    where
      go items j [] = do
        (_, complete) <- executeItems grammar Nothing j items
        return (TM.lookup (P 0 nt) complete)

      go items j (tok:toks) = do
        (newItems, _) <- executeItems grammar (Just tok) j items
        go newItems (j+1) toks

------------------------------------------------------------------------------
data ExecState nt tok f m
    = ExSt { known      :: TM.Map (P Int nt) (ResultNode f m)
           , called     :: TS.Set nt
           , waiting    :: TM.Map (P Int nt) (StackNode nt tok f m)
           , continuing :: [Item nt tok f m]
           }

initialState :: ExecState nt tok f m
initialState =
    ExSt { known      = TM.empty
         , called     = TS.empty
         , waiting    = TM.empty
         , continuing = []
         }

------------------------------------------------------------------------------
-- using the StateT monad transformer, which allows for the use of
-- 'gets' and 'modify'.
type M nt tok f m a = StateT (ExecState nt tok f m) m a

checkKnown :: (Eq1 nt, Functor m, Monad m) =>
              Int
           -> nt a
           -> M nt tok f m (Maybe (ResultNode f m a))
checkKnown i nt = TM.lookup (P i nt) <$> gets known

addKnown :: Monad m =>
            Int
         -> nt a
         -> ResultNode f m a
         -> M nt tok f m ()
addKnown i nt v =
    modify $ \s -> s { known = TM.insert (P i nt) v (known s) }

addContinuing :: Monad m =>
                 Item nt tok f m
              -> M nt tok f m ()
addContinuing item =
    modify $ \s -> s { continuing = item : continuing s }

addWaitingItem :: (Eq1 nt, ParseStackMonad nt tok f m, Functor m) =>
                  Int
               -> nt a
               -> WaitingItem nt tok f m a
               -> M nt tok f m (StackNode nt tok f m a)
addWaitingItem j nt witem = do
  maybeStackNode <- TM.lookup (P j nt) <$> gets waiting
  case maybeStackNode of
    Nothing -> do
      stackNode <- lift $ newStackNode j nt
      lift $ addToStackNode witem stackNode
      modify $ \s -> s { waiting = TM.insert (P j nt) stackNode (waiting s) }
      return stackNode
    Just stackNode -> do
      lift $ addToStackNode witem stackNode
      return stackNode

recordCall :: (Ord1 nt, Monad m) =>
              nt a
           -> M nt tok f m Bool
recordCall nt = do
  calledSet <- gets called
  case nt `TS.member` calledSet of
    True  -> return True
    False -> do
      modify $ \s -> s { called = TS.insert nt (called s) }
      return False

------------------------------------------------------------------------------
executeItems :: (Ord1 nt, ParseStackMonad nt tok f m) =>
                Grammar nt tok f
             -> Maybe tok
             -> Int
             -> [Item nt tok f m]
             -> m ([Item nt tok f m], TM.Map (P Int nt) (ResultNode f m))
executeItems grammar token j items = do
  st <- execStateT (mapM_ execute items) initialState
  return (continuing st, known st)
    where
      execute (Item (Return a) returnAddress) = do
        (i,nt) <- lift $ getPositionAndNT returnAddress
        known <- checkKnown i nt
        case known of
          Nothing -> do
            v <- lift $ newResult i j a
            addKnown i nt v
            parents <- lift $ readStackNode returnAddress
            mapM_ (execute . ofWaiting v) parents
          Just v -> do
            lift $ addResult v a

      execute (Item Failure returnAddress) = do
        return ()

      execute (Item (Choice rhs1 rhs2) returnAddress) = do
        execute (Item rhs1 returnAddress)
        execute (Item rhs2 returnAddress)

      execute (Item (Token k) returnAddress) = do
        case token of
          Nothing -> return ()
          Just t  -> addContinuing (Item (k t) returnAddress)

      execute (Item (NT nt k) returnAddress) = do
        stackNode <- addWaitingItem j nt (WItem k returnAddress)
        known     <- checkKnown j nt
        case known of
          Just v -> do
            execute (Item (k v) returnAddress)
          Nothing -> do
            alreadyCalled <- recordCall nt
            unless alreadyCalled $ execute (Item (grammar nt) stackNode)

------------------------------------------------------------------------------
