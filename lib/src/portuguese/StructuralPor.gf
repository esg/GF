concrete StructuralPor of Structural = CatPor ** 
  open PhonoPor, MorphoPor, ParadigmsPor, BeschPor, 
       MakeStructuralPor, (X = ConstructX), Prelude in {

  flags optimize=all ;
    coding=utf8 ;

lin
  -- have_V3
  -- have_not_V3

  above_Prep = mkPrep "sobre" ;
  after_Prep = {s = ["depois"] ; c = MorphoPor.genitive ; isDir = False} ;
  all_Predet = {
    s = \\a,c => prepCase c ++ aagrForms "todo" "toda" "todos" "todas" ! a ;
    c = Nom ;
    a = PNoAg
    } ;
  almost_AdA, almost_AdN = ss "quase" ;
  always_AdV = ss "sempre" ;
  although_Subj = ss "ainda que" ** {m = Conjunct} ;
  and_Conj = {s1 = [] ; s2 = etConj.s ; n = Pl} ;
  at_least_AdN = ss "no mínimo" ;
  at_most_AdN = ss "no máximo" ;
  because_Subj = ss "porque" ** {m = Indic} ;
  before_Prep = {s = "antes" ; c = MorphoPor.genitive ; isDir = False} ;
  behind_Prep = {s = "atrás" ; c = MorphoPor.genitive ; isDir = False} ;
  between_Prep = mkPrep "entre" ;
  both7and_DConj = {s1,s2 = etConj.s ; n = Pl} ;
  but_PConj = ss "mas" ;
  by8agent_Prep = mkPrep "por" ;
  by8means_Prep = mkPrep "por" ;
  can8know_VV = mkVV (verboV (saber_71 "saber")) ;
  can_VV = mkVV (verboV (poder_58 "poder")) ;
  during_Prep = mkPrep "durante" ; 
  either7or_DConj = {s1,s2 = "ou" ; n = Sg} ;
  everybody_NP = makeNP ["todos"] Masc Pl ;
  every_Det = mkDeterminer "cada" "cada" Sg False ;
  everything_NP = pn2np (mkPN ["tudo"] Masc) ;
  everywhere_Adv = ss ["em todo lugar"] ;
  except_Prep = mkPrep "exceto" ;
  few_Det = mkDeterminer "poucos" "poucas" Pl False ;
---  first_Ord = {s = \\ag => (regA "primeiro").s ! Posit ! AF ag.g ag.n} ;
  for_Prep = mkPrep "para" ;
  from_Prep = complGen ; ---
  he_Pron = 
    mkPronoun 
     "ele" "o" "lhe" "ele"
     "seu" "sua" "seus" "suas"
      Masc Sg P3 ;
  here_Adv = mkAdv "aqui" ;
  here7to_Adv = mkAdv ["para cá"] ;
  here7from_Adv = mkAdv ["de cá"] ;
  how_IAdv = ss "como" ;
  how8many_IDet = mkIDet "quantos" "quantas" Pl ;
  how8much_IAdv = ss "quanto" ;
  if_Subj = ss "se" ** {m = Indic} ;
  if_then_Conj = {s1 = "se" ; s2 = "então" ; n = Sg ; lock_Conj = <>} ;
  in8front_Prep = {s = "em frente" ; c = MorphoPor.genitive ; isDir = False} ;
  i_Pron = 
    mkPronoun
      "eu" "me" "me" "mim"
      "meu" "minha" "meus" "minhas"
      Masc Sg P1 ;
  in_Prep = mkPrep "em" ;
  it_Pron = 
    mkPronoun
      "ele" "o" "lhe" "ele"
      "seu" "sua" "seus" "suas"
      Masc Sg P3 ;
  less_CAdv = X.mkCAdv "menos" conjThan ; ----
  many_Det = mkDeterminer "muitos" "muitas" Pl False ;
  more_CAdv = X.mkCAdv "mais" conjThan ;
  most_Predet = {s = \\_,c => prepCase c ++ ["a maior parte"] ; c = CPrep P_de ;
    a = PNoAg} ;
  much_Det = mkDeterminer "muito" "muita" Sg False ;
  must_VV = mkVV (verboV (dever_6 "dever")) ;
  no_Quant =
    let
      ningun : ParadigmsPor.Number => ParadigmsPor.Gender => Case => Str = table {
        Sg => \\g,c => prepCase c ++ genForms "nenhum" "nenhuma" ! g ;
        Pl => \\g,c => prepCase c ++ genForms "nenhuns" "nenhumas" ! g
        }
    in {
      s = \\_ => ningun ;
      sp = ningun ;
      s2 = [] ; isNeg = True
    } ;
  no_Utt = ss "não" ;
  not_Predet = {s = \\a,c => prepCase c ++ "não" ; c = Nom ; a = PNoAg} ;
  nobody_NP = pn2npNeg (mkPN "ninguém") ;
  nothing_NP = pn2npNeg (mkPN "nada") ;

  on_Prep = mkPrep "sobre" ;
---  one_Quant = {s = \\g,c => prepCase c ++ genForms "um" "uma" ! g} ;
  only_Predet = {s = \\_,c => prepCase c ++ "somente" ; c = Nom ;
    a = PNoAg} ;
  or_Conj = {s1 = [] ; s2 = "ou" ; n = Sg} ;
  otherwise_PConj = ss "de outra forma" ;
  part_Prep = complGen ;
  please_Voc = ss ["por favor"] ;
  possess_Prep = complGen ;
  quite_Adv = ss "bastante" ;
  she_Pron = 
    mkPronoun
      "ela" "a" "lhe" "ela"
      "seu" "sua" "seus" "suas"
      Fem Sg P3 ;
  so_AdA = ss "tanto" ;
  somebody_NP = pn2np (mkPN "alguém" Masc) ;
  somePl_Det = mkDeterminer "alguns" "algumas" Pl False ;
  someSg_Det = mkDeterminer "algum" "alguma" Sg False ; 
  something_NP = pn2np (mkPN ["algo"] Masc) ;
  somewhere_Adv = ss ["em algum lugar"] ;
  that_Quant = mkQuantifier "esse" "essa" "esses" "essas" ;
  there_Adv = mkAdv "lá" ; -- allá
  there7to_Adv = mkAdv ["para lá"] ;
  there7from_Adv = mkAdv ["de cá"] ;
  therefore_PConj = ss ["por isso"] ;
  they_Pron = mkPronoun
    "eles" "os" "lhes" "eles"
    "dele" "dela" "deles" "delas"
    Masc Pl P3 ;
  this_Quant = mkQuantifier "este" "esta" "estes" "estas" ;
  through_Prep = mkPrep "por" ;
  too_AdA = ss "demasiado" ;
  to_Prep = complDat ;
  under_Prep = mkPrep "abaixo" ;
  very_AdA = ss "muito" ;
  want_VV = mkVV (verboV (querer_64 "querer")) ;
  we_Pron = 
    mkPronoun 
      "nós" "nos" "nos" "nós"
      "nosso" "nossa" "nossos" "nossas"
      Masc Pl P1 ;
  whatSg_IP = {s = \\c => prepCase c ++ ["qual"] ; a = aagr Masc Sg} ;
  whatPl_IP = {s = \\c => prepCase c ++ ["quais"] ; a = aagr Masc Pl} ; ---
  when_IAdv = ss "quando" ;
  when_Subj = ss "quando" ** {m = Indic} ;
  where_IAdv = ss "onde" ;
  which_IQuant = {s = table {
    Sg => \\g,c => prepCase c ++ "qual" ; --- cual
    Pl => \\g,c => prepCase c ++ "quais" 
    }
   } ;
  whoPl_IP = {s = \\c => prepCase c ++ "quem" ; a = aagr Masc Pl} ;
  whoSg_IP = {s = \\c => prepCase c ++ "quem" ; a = aagr Masc Sg} ;
  why_IAdv = ss ["por que"] ;
  without_Prep = mkPrep "sem" ;
  with_Prep = mkPrep "com" ;
  yes_Utt = ss "sim" ;
  youSg_Pron = mkPronoun 
    "tu" "te" "te" "ti"
    "teu" "tua" "teus" "tuas"
    Masc Sg P2 ;
  youPl_Pron =
    mkPronoun
      "vós" "os" "lhes" "vós"
      "vosso" "vossa" "vossos" "vossas"
      Masc Pl P2 ;
  youPol_Pron =
    mkPronoun
      "você" "o" "lhe" "você"
      "seu" "sua" "seus" "suas"
      Masc Sg P3 ;

oper
  etConj : {s : Str ; n : MorphoPor.Number} = {s = pre {
    "e" ; 
    "e" / strs {"ya" ; "ye" ; "yo" ; "yu"} ;
    "e" / strs {"i" ; "hi" ; "y"}
    }} ** {n = Pl} ;
lin
  as_CAdv = X.mkCAdv "como" conjThan ; ----
   have_V2 = dirV2 (verboV (ter_4 "ter")) ;

  that_Subj = {s = "que" ; m = Conjunct} ;

  lin language_title_Utt = ss "português" ;
}

