module GF.GFCC.DataGFCC where

import GF.GFCC.AbsGFCC
import GF.GFCC.PrintGFCC
import GF.Infra.CompactPrint
import Data.Map
import Data.List

-- internal datatypes for GFCC

data GFCC = GFCC {
  absname   :: CId ,
  cncnames  :: [CId] ,
  abstract  :: Abstr ,
  concretes :: Map CId Concr
  }

data Abstr = Abstr {
  aflags  :: Map CId String,     -- value of a flag
  funs    :: Map CId (Type,Exp), -- type and def of a fun
  cats    :: Map CId [Hypo],     -- context of a cat
  catfuns :: Map CId [CId]       -- funs yielding a cat (redundant, for fast lookup)
  }

data Concr = Concr {
  flags   :: Map CId String, -- value of a flag
  lins    :: Map CId Term,   -- lin of a fun
  opers   :: Map CId Term,   -- oper generated by subex elim
  lincats :: Map CId Term,   -- lin type of a cat
  lindefs :: Map CId Term,   -- lin default of a cat
  printnames :: Map CId Term -- printname of a cat or a fun
  }

statGFCC :: GFCC -> String
statGFCC gfcc = unlines [
  "Abstract\t" ++ pr (absname gfcc), 
  "Concretes\t" ++ unwords (lmap pr (cncnames gfcc)), 
  "Categories\t" ++ unwords (lmap pr (keys (cats (abstract gfcc)))) 
  ]
 where pr (CId s) = s

-- convert parsed grammar to internal GFCC

mkGFCC :: Grammar -> GFCC
mkGFCC (Grm a cs ab@(Abs afls fs cts) ccs) = GFCC {
  absname = a,
  cncnames = cs,
  abstract = 
    let
      aflags  = fromAscList [(f,v) | Flg f v <- afls]
      lfuns   = [(fun,(typ,def)) | Fun fun typ def <- fs]
      funs    = fromAscList lfuns
      lcats   = [(c,hyps) | Cat c hyps <- cts]
      cats    = fromAscList lcats
      catfuns = fromAscList 
        [(cat,[f | (f, (DTyp _ c _,_)) <- lfuns, c==cat]) | (cat,_) <- lcats]
    in Abstr aflags funs cats catfuns,
  concretes = fromAscList (lmap mkCnc ccs)
  }
 where
   mkCnc (Cnc lang fls ls ops lincs linds prns) = 
       (lang, Concr flags lins opers lincats lindefs printnames) where
     flags      = fromAscList [(f,v) | Flg f v <- fls]  
     lins       = fromAscList [(f,v) | Lin f v <- ls]  
     opers      = fromAscList [(f,v) | Lin f v <- ops]  
     lincats    = fromAscList [(f,v) | Lin f v <- lincs]  
     lindefs    = fromAscList [(f,v) | Lin f v <- linds]  
     printnames = fromAscList [(f,v) | Lin f v <- prns]  


-- convert internal GFCC and pretty-print it

printGFCC :: GFCC -> String
printGFCC gfcc = compactPrintGFCC $ printTree $ Grm
  (absname gfcc) 
  (cncnames gfcc)
  (Abs
    [Flg f v     | (f,v) <- assocs (aflags (abstract gfcc))]
    [Fun f ty df | (f,(ty,df)) <- assocs (funs (abstract gfcc))]
    [Cat f v     | (f,v) <- assocs (cats (abstract gfcc))]
    )
  [fromCnc lang cnc | (lang,cnc) <- assocs (concretes gfcc)]
 where
   fromCnc lang cnc = Cnc lang 
     [Flg f v | (f,v) <- assocs (flags cnc)]
     [Lin f v | (f,v) <- assocs (lins cnc)]
     [Lin f v | (f,v) <- assocs (opers cnc)]
     [Lin f v | (f,v) <- assocs (lincats cnc)]
     [Lin f v | (f,v) <- assocs (lindefs cnc)]
     [Lin f v | (f,v) <- assocs (printnames cnc)]

-- default map and filter are for Map here
lmap = Prelude.map
lfilter = Prelude.filter


