----------------------------------------------------------------------
-- |
-- Module      : PGFtoPython
-- Maintainer  : Peter Ljunglöf
--
-- exports a GF grammar into a Python module
-----------------------------------------------------------------------------

module GF.Compile.PGFtoPython (pgf2python) where

import PGF(showCId)
import PGF.Internal as M

import GF.Data.Operations

import qualified Data.Array.IArray as Array
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
--import Data.List (intersperse)

pgf2python :: PGF -> String
pgf2python pgf = ("# -*- coding: utf-8 -*-" ++++
                  "# This file was automatically generated by GF" +++++
                  showCId name +++ "=" +++ 
                  pyDict 1 pyStr id [
                              ("flags", pyDict 2 pyCId pyLiteral (Map.assocs (gflags pgf))),
                              ("abstract", pyDict 2 pyStr id [
                                              ("name", pyCId name), 
                                              ("start", pyCId start), 
                                              ("flags", pyDict 3 pyCId pyLiteral (Map.assocs (aflags abs))),
                                              ("funs", pyDict 3 pyCId pyAbsdef (Map.assocs (funs abs)))
                                             ]),
                              ("concretes", pyDict 2 pyCId pyConcrete (Map.assocs cncs))
                             ] ++ "\n")
    where
      name  = absname pgf
      start = M.lookStartCat pgf
      abs = abstract pgf
      cncs = concretes pgf

pyAbsdef :: (Type, Int, Maybe ([Equation], [[M.Instr]]), Double) -> String
pyAbsdef (typ, _, _, _) = pyTuple 0 id [pyCId cat, pyList 0 pyCId args]
    where (args, cat) = M.catSkeleton typ 

pyLiteral :: Literal -> String
pyLiteral (LStr s) = pyStr s
pyLiteral (LInt n) = show n
pyLiteral (LFlt d) = show d

pyConcrete :: Concr -> String
pyConcrete cnc = pyDict 3 pyStr id [
                  ("flags", pyDict 0 pyCId pyLiteral (Map.assocs (cflags cnc))),
                  ("printnames", pyDict 4 pyCId pyStr (Map.assocs (printnames cnc))),
                  ("lindefs", pyDict 4 pyCat (pyList 0 pyFun) (IntMap.assocs (lindefs cnc))),
                  ("productions", pyDict 4 pyCat pyProds (IntMap.assocs (productions cnc))),
                  ("cncfuns", pyDict 4 pyFun pyCncFun (Array.assocs (cncfuns cnc))),
                  ("sequences",  pyDict 4 pySeq pySymbols (Array.assocs (sequences cnc))),
                  ("cnccats", pyDict 4 pyCId pyCncCat (Map.assocs (cnccats cnc))),
                  ("size",  show (totalCats cnc))
                 ]
    where pyProds prods = pyList 5 pyProduction (Set.toList prods)
          pyCncCat (CncCat start end _) = pyList 0 pyCat [start..end]
          pyCncFun (CncFun f lins) = pyTuple 0 id [pyList 0 pySeq (Array.elems lins), pyCId f]
          pySymbols syms = pyList 0 pySymbol (Array.elems syms)

pyProduction :: Production -> String
pyProduction (PCoerce arg)       = pyTuple 0 id [pyStr "", pyList 0 pyCat [arg]]
pyProduction (PApply funid args) = pyTuple 0 id [pyFun funid, pyList 0 pyPArg args]
    where pyPArg (PArg [] fid) = pyCat fid
          pyPArg (PArg hypos fid) = pyTuple 0 pyCat (fid : map snd hypos)

pySymbol :: Symbol -> String
pySymbol (SymCat n l)    = pyTuple 0 show [n, l]
pySymbol (SymLit n l)    = pyDict 0 pyStr id [("lit", pyTuple 0 show [n, l])]
pySymbol (SymVar n l)    = pyDict 0 pyStr id [("var", pyTuple 0 show [n, l])]
pySymbol (SymKS t)       = pyStr t
pySymbol (SymKP ts alts) = pyDict 0 pyStr id [("pre", pyList 0 pySymbol ts), ("alts", pyList 0 alt2py alts)]
    where alt2py (ps,ts) = pyTuple 0 (pyList 0 pyStr) [map pySymbol ps, ts]
pySymbol SymBIND         = pyStr "&+"
pySymbol SymSOFT_BIND    = pyStr "&+"
pySymbol SymNE           = pyDict 0 pyStr id [("nonExist", pyTuple 0 id [])]

----------------------------------------------------------------------
-- python helpers 

pyDict :: Int -> (k -> String) -> (v -> String) -> [(k, v)] -> String
pyDict n pk pv [] = "{}"
pyDict n pk pv kvlist = prCurly (pyIndent n ++ prTList ("," ++ pyIndent n) (map pyKV kvlist) ++ pyIndent n)
    where pyKV (k, v) = pk k ++ ":" ++ pv v

pyList :: Int -> (v -> String) -> [v] -> String
pyList n pv [] = "[]"
pyList n pv xs = prBracket (pyIndent n ++ prTList ("," ++ pyIndent n) (map pv xs) ++ pyIndent n)

pyTuple :: Int -> (v -> String) -> [v] -> String
pyTuple n pv [] = "()"
pyTuple n pv [x] = prParenth (pyIndent n ++ pv x ++ "," ++ pyIndent n)
pyTuple n pv xs = prParenth (pyIndent n ++ prTList ("," ++ pyIndent n) (map pv xs) ++ pyIndent n)

pyCat :: Int -> String
pyCat n = pyStr ('C' : show n)

pyFun :: Int -> String
pyFun n = pyStr ('F' : show n)

pySeq :: Int -> String
pySeq n = pyStr ('S' : show n)

pyStr :: String -> String
pyStr s = 'u' : prQuotedString s

pyCId :: CId -> String
pyCId = pyStr . showCId

pyIndent :: Int -> String
pyIndent n | n > 0 = "\n" ++ replicate n ' '
           | otherwise = ""
