--# -path=.:../romance:../common:../abstract:../../prelude

concrete LexiconPor of Lexicon = CatPor ** open 
  (M=MorphoPor), ParadigmsPor, BeschPor in {

flags 
    coding=utf8 ;
  optimize=values ;

lin
   airplane_N = regN "avião" ;	-- avião  is masculine
   answer_V2S = mkV2S (regV "responder") dative ;
   apartment_N = regN "apartamento" ;
   apple_N = regN "maçã" ;
   art_N = regN "arte" ;	
   ask_V2Q = mkV2Q (regV "perguntar") dative ;
   baby_N = regN "bebê" ;		-- can be used for both fem. & masc.
   bad_A = prefA (mkADeg (regA "mau") (regA "pior")) ;
   bank_N = regN "banco" ;
   beautiful_A = prefA (regADeg "bonito") ;	-- bonita
   become_VA = reflV (mkV "converter" "converto") ;  --- converter-se em
   beer_N = regN "cerveja" ;
   beg_V2V = mkV2V (mkV "rogar" "rogo") accusative dative ;   -- pedir
   big_A = prefA (regADeg "grande") ;
   bike_N = regN "bicicleta" ;
   bird_N = regN "pássaro" ;
   black_A = regADeg "negro" ;	-- negra
   blue_A = regADeg "azul" ;
   boat_N = regN "bote" ;
   book_N = regN "livro" ;
   boot_N = regN "bota" ;
   boss_N = regN "chefe" ;
   boy_N = regN "menino" ;
   bread_N = regN "pão" ;
   break_V2 = dirV2 (special_ppV (regV "estragar") "estrago") ;
   broad_A = regADeg "largo" ;
   brother_N2 = deN2 (regN "irmão") ;
   brown_A = regADeg "marrom" ; --- *
   butter_N = regN "manteiga" ;
   buy_V2 = dirV2 (regV "comprar") ;
   camera_N = regN "câmera" ; -- ["máquina fotográfica"]
   cap_N = regN "gorro" ;
   car_N = regN "carro" ;
   carpet_N = regN "piso" ;
   cat_N = regN "gato" ;		-- gata
   ceiling_N = regN "teto" ;
   chair_N = regN "cadeira" ;
   cheese_N = regN "queijo" ;
   child_N = regN "criança" ;		-- niña
   church_N = regN "igreja" ;
   city_N = femN (regN "cidade") ;		-- fem
   clean_A = regADeg "limpo" ;
   clever_A = regADeg "inteligente" ;
   close_V2 = dirV2 (mkV "fechar" "fecho") ;
   coat_N = regN "casaco" ;
   cold_A = regADeg "frio" ;		-- fría
   come_V = verboV (venir_82 "venir") ;
   computer_N = regN "computador" ;		-- also computador, ordenador in Porin
   country_N = regN "país" ;		-- masc
   cousin_N = regN "primo" ;
   cow_N = regN "vaca" ;
   die_V = verboV (morir_35b "morir") ;
   dirty_A = regADeg "sujo" ;
   distance_N3 = mkN3 (regN "distância") genitive dative ;
   doctor_N = regN "médico" ;		-- médica
   dog_N = regN "cachorro" ;		-- perra
   door_N = regN "porta" ;
   drink_V2 = dirV2 (regV "tomar") ;     -- beber
   easy_A2V = mkA2V (regA "fácil") dative genitive ;
   eat_V2 = dirV2 (regV "comer") ;
   empty_A = regADeg "vazio" ;
   enemy_N = regN "inimigo" ;		-- enemiga
   factory_N = regN "fábrica" ;	
   father_N2 = deN2 (regN "pai") ;
   fear_VS = mkVS (regV "temer") ;
   find_V2 = dirV2 (verboV (encontrar_38 "encontrar")) ;
   fish_N = mascN (regN "peixe") ;
   floor_N = regN "chão" ;		-- piso
   forget_V2 = dirV2 (regV "esquecer") ;
   fridge_N = regN "geladeira" ;
   friend_N = regN "amigo" ;		-- amiga
   fruit_N = regN "fruta" ;
   fun_AV = mkAV (regA "divertido") genitive ;		-- entretenido
   garden_N = regN "jardim" ;
   girl_N = regN "menina" ;
   glove_N = regN "luva" ;
   gold_N = regN "ouro" ;
   good_A = prefA (mkADeg (regA "bom") (regA "melhor")) ; ---- adv?
   go_V = (verboV (ir_46 "ir")) ;
   green_A = regADeg "verde" ;
   harbour_N = regN "porto" ;
   hate_V2 = dirV2 (mkV "odiar" "odeio") ;
   hat_N = regN "chapéu" ;
   hear_V2 = dirV2 (mkV (oir_51 "oír")) ;
   hill_N = regN "colina" ;
   hope_VS = mkVS (regV "esperar") ;
   horse_N = regN "cavalo" ;
   hot_A = regADeg "quente" ;
   house_N = regN "casa" ;
   important_A = regADeg "importante" ;
   industry_N = regN "indústria" ;
   iron_N = regN "ferro" ;
   king_N = regN "rei" ;
   know_V2 = mkV2 (verboV (conocer_25 "conocer")) ;
   know_VQ = mkVQ (verboV (saber_71 "saber")) ;
   know_VS = mkVS (verboV (saber_71 "saber")) ;
   lake_N = regN "lago" ;
   lamp_N = regN "lâmpada" ;
   learn_V2 = dirV2 (regV "aprender") ;
   leather_N = regN "couro" ;
   leave_V2 = dirV2 (regV "partir") ;	-- irse, dejar
   like_V2 = dirV2 (regV "gostar") ;
   listen_V2 = dirV2 (regV "escutar") ;
   live_V = verboV (vivir_7 "viver") ;
   long_A = regADeg "largo" ;
   lose_V2 = dirV2 (verboV (defender_29 "perder")) ;
   love_N = regN "amor" ;
   love_V2 = dirV2 (regV "amar") ;
   man_N = regN "homem" ;		-- masc
   married_A2 = mkA2 (regA "casado") dative ;
   meat_N = femN (regN "carne") ;
   milk_N = femN (regN "leite") ;
   moon_N = regN "lua" ;
   mother_N2 = deN2 (mkN "mãe" feminine) ;
   mountain_N = mkN "montanha" ;
   music_N = mkN "música" ;
   narrow_A = regADeg "estreito" ;
   new_A = prefA (regADeg "novo") ;
   newspaper_N = mkN "jornal" ;		-- diario  
   oil_N = mkN "óleo" ;
   old_A =  prefA (regADeg "velho") ;
   open_V2 = dirV2 (special_ppV (regV "abrir") "aberto") ;
   paint_V2A = mkV2A (regV "pintar") accusative (mkPrep "en") ;
   paper_N = mkN "papel" ;
   paris_PN = mkPN "Paris" masculine ;
   peace_N = mkN "paz" feminine ;
   pen_N = mkN "caneta" ;
   planet_N = mkN "planeta" masculine ;
   plastic_N = mkN "plástico" ;
   play_V2 = dirV2 (verboV (jugar_47 "jogar")) ;
   policeman_N = mkN "polícia" masculine ;	-- fem refers to the institution
   priest_N = mkN "padre" masculine ;		-- masc
   probable_AS = mkAS (regA "provável") ;	
   queen_N = mkN "rainha" ;
   question_N = mkN "pergunta" ;
   radio_N = mkN "rádio" feminine ;
   rain_V0 = mkV0 (verboV (llover_89 "llover")) ;
   read_V2 = dirV2 (verboV (creer_26 "leer")) ;
   reason_N = mkN "razão" feminine ;
   red_A = regADeg "vermelho" ;
   religion_N = mkN "religião" "religiões" feminine ;
   restaurant_N = mkN "restaurante" ;		-- restorán, restaurán, masc
   river_N = mkN "rio" ;
   rock_N = mkN "rocha" ;
   roof_N = mkN "teto" ;
   rubber_N = regN "borracha" ;
   run_V = regV "correr" ;
   say_VS = mkVS (verboV (decir_28 "decir")) ;
   school_N = regN "escola" ;
   science_N = regN "ciência" ;
   sea_N = regN "mar" ;			-- masc & fem 
   seek_V2 = dirV2 (regV "buscar") ;
   see_V2 = dirV2 (verboV (ver_83 "ver")) ;
   sell_V3 = dirV3 (regV "vender") dative ;
   send_V3 = dirV3 (regV "mandar") dative ;
   sheep_N = regN "ovelha" ;
   ship_N = femN (regN "navio") ;
   shirt_N = regN "camisa" ;
   shoe_N = regN "sapato" ;
   shop_N = regN "negócio" ;
   short_A = regADeg "curto" ; --- breve
   silver_N = regN "prata" ;
   sister_N = regN "irmã" ;
   sleep_V = verboV (dormir_35 "dormir") ;
   small_A = prefA (regADeg "pequeno") ;
   snake_N = femN (regN "serpente") ;		-- fem
   sock_N = regN "meia" ;
   speak_V2 = dirV2 (regV "hablar") ;
   star_N = regN "estrela" ;
   steel_N = regN "acero" ;
   stone_N = regN "pedra" ;
   stove_N = regN "forno" ;		-- estufa
   student_N = regN "estudante" ;	-- used both for fem & masc
   stupid_A = regADeg "estúpido" ;
   sun_N = regN "sol" ;	
   switch8off_V2 = dirV2 (regV "apagar") ;
   switch8on_V2 = dirV2 (regV "prender") ;
   table_N = regN "mesa" ; 
   talk_V3 = mkV3 (regV "hablar") dative genitive ;
   teacher_N = regN "professor" ;		-- maestra
   teach_V2 = dirV2 (regV "enseñar") ;
   television_N = mkN "televisão" feminine ;	-- televisor masc
   thick_A = regADeg "grosso" ;
   thin_A = regADeg "fino" ;			-- delgado
   train_N = regN "trem" ;
   travel_V = regV "viajar" ;
   tree_N = regN "árvore" ;
  --- trousers_N = regN "pantalón" ;	-- masc
   ugly_A = regADeg "feio" ;
   understand_V2 = dirV2 (mkV "entender" "entendo") ;
   university_N = femN (regN "universidade") ;
   village_N = regN "povo" ;
   wait_V2 = mkV2 (regV "esperar") dative ;
   walk_V = mkV "caminhar" ;
   warm_A = regADeg "quente" ;
   war_N = mkN "guerra" ;
   watch_V2 = dirV2 (regV "mirar") ;		-- ver
   water_N = mkN "água" ; 
   white_A = compADeg (regA "branco") ;
   window_N = regN "janela" ;
   wine_N = regN "vinho" ;
   win_V2 = dirV2 (regV "ganar") ;
   woman_N = mkN "mulher" feminine ;
   wonder_VQ = mkVQ (reflV (regV "perguntar")) ;
   wood_N = regN "madeira" ;
   write_V2 = dirV2 (special_ppV (regV "escribir") "escrito") ;
   yellow_A = regADeg "amarelo" ;
   young_A = prefA (mkA "jovem" "jovem" "jóvens" "jóvens" "jovialmente") ; 

   do_V2 =  dirV2 (verboV (hacer_44 "hacer")) ;
   now_Adv = mkAdv "agora" ;
   already_Adv = mkAdv "ya" ;
   song_N = mkN "canção" "canções" feminine ;
   add_V3 = dirV3 (regV "sumar") dative ;
   number_N = regN "número" ;
   put_V2 = dirV2 (verboV (poner_60 "poner")) ;
   stop_V = regV "parar" ; 
   jump_V = regV "saltar" ;

  left_Ord = M.mkOrd (regA "esquerda") ;
  right_Ord = M.mkOrd (regA "direita") ;
  far_Adv = mkAdv "longe" ; ----?
   correct_A = regA "correto" ;
   dry_A = regA "seco" ;
   dull_A = regA "lento" ;
   full_A = regA "cheio" ;
   heavy_A = regA "pesado" ;
   near_A = regA "próximo" ;
   rotten_A = regA "podre" ;
   round_A = regA "redondo" ;
   sharp_A = regA "pontudo" ; -- afilado, puntiagudo
   smooth_A = regA "liso" ;     -- suave
   straight_A = regA "direto" ;
   wet_A = regA "molhado" ;
   wide_A = regA "largo" ;      -- extenso
   animal_N = regN "animal" ;           -- masc (sometimes fem when adj)
   ashes_N = regN "cinza" ;
   back_N = regN "costa" ;
   bark_N = regN "corteza" ;
   belly_N = regN "pança" ;             -- barriga
   blood_N = femN (regN "sangue") ;
   bone_N = regN "osso" ;
   breast_N = regN "seio" ;             -- pecho
   cloud_N = femN (regN "nuvem") ;
   day_N = mascN (regN "dia") ;
   dust_N = regN "pó" ;
   ear_N = regN "orelha" ;
   earth_N = regN "terra" ;
   egg_N = regN "ovo" ;
   eye_N = regN "olho" ;
   fat_N = regN "gordura" ;
   feather_N = regN "pluma" ;
   fingernail_N = regN "unha" ;
   fire_N = regN "fogo" ;
   flower_N = femN (regN "flor") ;
   fog_N = regN "neblina" ;
   foot_N = regN "pé" ;
   forest_N = regN "floresta" ;
   grass_N = regN "gramado" ;             -- hierba, césped (masc)
   guts_N = regN "tripa" ;              -- gut=intestino ---- pl.t. tripas
   hair_N = regN "cabelo" ;            -- pelo
   hand_N = femN (regN "mão") ;
   head_N = regN "cabeça" ;
   heart_N = mkN "coração" "corações" masculine ;
   horn_N = regN "chifre" ;
   husband_N = regN "marido" ;  -- esposo
   ice_N = regN "gelo" ;
   knee_N = regN "joelho" ;
   leaf_N = regN "folha" ;
   leg_N = regN "perna" ;
   liver_N = regN "fígado" ;
   louse_N = regN "piolho" ;
   mouth_N = regN "boca" ;
   name_N = regN "nome" ;
   neck_N = regN "pescoço" ;
   night_N = femN (regN "noite") ;
   nose_N = femN (regN "nariz") ;
   person_N = regN "pessoa" ;
   rain_N = regN "chuva" ;
   road_N = femN (regN "rua") ;               -- camino
   root_N = femN (regN "raiz") ;
   rope_N = regN "corda" ;
   salt_N = femN (regN "sal") ;
   sand_N = regN "areia" ;
   seed_N = regN "semente" ;
   skin_N = femN (regN "pele") ;        -- fem
   sky_N = regN "céu" ;
   smoke_N = regN "fumaça" ;
   snow_N = femN (regN "neve") ;       -- fem
   stick_N = mkN "bastão" "bastões" masculine ;                -- palo
   tail_N = regN "rabo" ;
   tongue_N = regN "língua" ;
   tooth_N = regN "dente" ;
   wife_N = regN "esposa" ;
   wind_N = regN "viento" ;
   wing_N = regN "asa" ;
   worm_N = regN "minhoca" ;             -- lombriz (fem)
   year_N = regN "añn" ;
  bite_V2 = dirV2 (verboV (morder_50b "morder")) ;
   blow_V = regV "soprar" ;
   burn_V = regV "queimar" ;
  count_V2 = dirV2 (verboV (contar_38b "contar")) ;
  cut_V2 = dirV2 (regV "cortar") ;
   dig_V = regV "escarbar" ;
   fall_V = verboV (caer_20 "cair") ;
  fear_V2 = dirV2 (regV "temer") ;
  fight_V2 = dirV2 (regV "brigar") ;
   float_V = regV "flutuar" ;
   flow_V = verboV (influir_45 "fluir") ;             -- circular
   fly_V = regV "voar" ;
   freeze_V = regV "congelar" ;
   give_V3 = dirdirV3 (verboV (dar_27 "dar")) ;
  hit_V2 = dirV2 (regV "golpear") ;
  hold_V2 = dirV2 (verboV (tener_4 "tener")) ;
  hunt_V2 = dirV2 (regV "caçar") ;
  kill_V2 = dirV2 (regV "matar") ;
   laugh_V = regV "rir" ; ----V reír_67
   lie_V = reflV (regV "acostar") ; --  "acostarse"
   play_V = regV "jogar" ;
  pull_V2 = dirV2 (regV "tirar") ;
  push_V2 = dirV2 (regV "empurrar") ;
  rub_V2 = dirV2 (regV "esfregar") ;
  scratch_V2 = dirV2 (regV "rascar") ;
   sew_V = regV "coser" ;
   sing_V = regV "cantar" ;
   sit_V = reflV (mkV "sentar" "sento") ;
  smell_V = verboV (oler_52 "cheirar") ;
   spit_V = regV "escupir" ;
  split_V2 = dirV2 (regV "separar") ; -- dividir,) ;
  squeeze_V2 = dirV2 (regV "exprimir") ;
  stab_V2 = dirV2 (regV "apunhalar") ;
   stand_V = verboV (estar_2 "estar") ; ---- "estar de pie" ;
  suck_V2 = dirV2 (regV "chupar") ;
   swell_V = regV "tragar" ;
   swim_V = regV "nadar" ;
   think_V = regV "pensar" ;
  throw_V2 = dirV2 (regV "tirar") ;
  tie_V2 = dirV2 (regV "atar") ;
   turn_V = regV "dobrar" ;
   vomit_V = regV "vomitar" ;
  wash_V2 = dirV2 (regV "lavar") ;
  wipe_V2 = dirV2 (regV "secar") ;
    breathe_V = (regV "respirar") ;

  john_PN = mkPN "João" masculine ;
  today_Adv = mkAdv "hoje" ;

  grammar_N = regN "gramática" ;
  language_N = regN "língua" ;
  rule_N = regN "regra" ;


} ;
