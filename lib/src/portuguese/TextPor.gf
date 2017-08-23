concrete TextPor of Text = CommonX - [Temp,TTAnt,Tense,TPres,TPast,TFut,TCond] ** open Prelude in {

  flags coding=utf8 ;
-- This works for the special punctuation marks of Portuguese.

  lin
    TEmpty = {s = []} ;
    TFullStop x xs = {s = x.s ++ SOFT_BIND ++ "." ++ xs.s} ;
    TQuestMark x xs = {s = x.s ++ SOFT_BIND ++ "?" ++ xs.s} ;
    TExclMark x xs = {s = x.s ++ SOFT_BIND ++ "!" ++ xs.s} ;

}
