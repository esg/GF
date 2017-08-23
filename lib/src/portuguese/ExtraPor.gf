concrete ExtraPor of ExtraPorAbs = ExtraRomancePor ** 
  open CommonRomance, PhonoPor, MorphoPor, ParadigmsPor, ParamX, ResPor, BeschPor, (I = IrregPor),
  Prelude in {
  flags coding=utf8 ;
  
  lin
    i8fem_Pron =  mkPronoun
      "eu" "me" "me" "mim"
      "meu" "minha" "meus" "minhas"
      Fem Sg P1 ;
    these8fem_NP = makeNP ["estas"] Fem Pl ;
    they8fem_Pron = mkPronoun
      "elas" "as" "lhes" "elas"
      "seu" "sua" "seus" "suas"
      Fem Pl P3 ;
    this8fem_NP = pn2np (mkPN ["esta"] Fem) ;
    those8fem_NP = makeNP ["essas"] Fem Pl ;

    we8fem_Pron = mkPronoun 
      "nós" "nos" "nos" "nós"
      "nosso" "nossa" "nossos" "nossas"
      Fem Pl P1 ;
    whoPl8fem_IP = {s = \\c => prepCase c ++ "quem" ; a = aagr Fem Pl} ;
    whoSg8fem_IP = {s = \\c => prepCase c ++ "quem" ; a = aagr Fem Sg} ;

    youSg8fem_Pron = mkPronoun 
      "tu" "te" "te" "ti"
      "teu" "tua" "teus" "tuas"
      Fem Sg P2 ;
    youPl8fem_Pron = mkPronoun
      "vós" "vos" "vos" "vós"
      "vosso" "vossa" "vossos" "vossas"
      Fem Pl P2 ;
    youPol8fem_Pron = mkPronoun
      "você" "a" "o" "você"
      "seu" "sua" "seus" "suas"
      Fem Sg P3 ;

    youPolPl_Pron = mkPronoun
      "vocês" "as" "os" "vocês"
      "seu" "sua" "seus" "suas"
      Masc Pl P3 ;
    youPolPl8fem_Pron = mkPronoun
      "vocês" "as" "os" "vocês"
      "seu" "sua" "seus" "suas"
      Fem Pl P3 ;

   ImpNeg np vp = lin Utt{ 
      s = (mkClause (np.s ! Nom).comp np.hasClit False np.a vp).s 
          ! DInv ! RPres ! Simul ! RNeg False ! Conjunct
      } ;

   InvQuestCl cl = {
      s = \\t,a,p => 
            let cls = cl.s ! DInv ! t ! a ! p 
            in table {
              QDir   => cls ! Indic ;
              QIndir => subjIf ++ cls ! Indic
              }
      } ;

    -- ExtraRomance.PassVPSlash uses estar 
    PassVPSlash_ser vps = 
      let auxvp = predV copula
      in
      insertComplement (\\a => let agr = complAgr a in vps.s.s ! VPart agr.g agr.n) {
        s = auxvp.s ;
        agr = auxvp.agr ;
        neg = vps.neg ;
        clit1 = vps.clit1 ;
        clit2 = vps.clit2 ;
        clit3 = vps.clit3 ;
        isNeg = vps.isNeg ;
        comp  = vps.comp ;
        ext   = vps.ext
        } ;

    ExistsNP np = 
      mkClause [] True False np.a (insertComplement (\\_ => (np.s ! Nom).ton) (predV (mkV "existir"))) ;

    UseComp_estar comp = insertComplement comp.s (predV I.estar_V) ;

}
