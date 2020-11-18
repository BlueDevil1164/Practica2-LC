-- Si phi en PL es una disyunci ́on de literales,
-- entonces disLit2ListLit transforma phi en una lista de literales.
--Ejemplos: (x3 | !x4) --> [x3,!x4], Bot ---> []
disLit2ListLit :: PL -> [PL]
disLit2ListLit phi = case phi of
Bot -> []
Var x -> [Var x]
Neg (Var x) -> [Neg (Var x)]
(Dis alpha beta) -> (disLit2ListLit alpha) ++ (disLit2ListLit beta)
_ -> error $
"disLit2ListLit: phi no es una disyuncion de literales, phi="++(show phi)

-- Dado un literal l en PL, litComp calcula el literal complementario de l.
litComp :: PL -> PL
litComp phi= case phi of

Var x -> Neg (Var x)
Neg (Var x) -> Var x
_ -> error $ "litComp: phi no es literal, phi="++(show phi)
-- Dada una clausula de PL, representada por una lista de literales ll,

1

-- clausulaVAL determina si ll es una clausula valida.
-- ll es valida sii ll tiene al menos dos literales complementarios.
clausulaVal :: [PL] -> Bool
clausulaVal ll = case ll of
[] -> False
(l:ls) -> (litComp l) `elem` ll || clausulaVal ls

-- Dada phi en PL, cnf2LListLit transforma phi a una formula phi' en CNF,
-- donde phi' esta representada como una lista de listas de literales.
--Ejemplos: (x1 | x2) & (x3 | !x4) ---> [[x1,x2], [x3,!x4]], Top ---> []
cnf2LListLit :: PL -> [[PL]]
cnf2LListLit phi = case phi of
Top -> []
Var x -> [[Var x]]
Neg (Var x) -> [[Neg (Var x)]]
(Dis _ _) -> [disLit2ListLit phi]
(Con alpha beta) -> (cnf2LListLit alpha) ++ (cnf2LListLit beta)
_ -> error $ "cnf2LListLit: phi no esta en CNF, phi="++(show phi)
-- Dada phi en CNF, representada como una lista de listas de literales lc,
-- clauListTrue determina si todas las clausulas de lc son validas.
-- Es decir clauListTrue determina si todos los elementos de lc son clausulas validas.
clauListVal :: [[PL]] -> Bool
clauListVal lc = case lc of
[] -> True
(c:cs) -> clausulaVal c && clauListVal cs

-- Dada phi en PL, decide si phi pertenece, o no, a VAL:={phi in PL | forall m: m |= phi}.
-- Esto se hace transformando primero phi a una f ́ormula en CNF representada mediante una lista de listas de literales,
-- y luego aplicando clauListVal a dicha lista.
decideCNFenVAL :: PL -> Bool
decideCNFenVAL phi = clauListVal (cnf2LListLit phi)
