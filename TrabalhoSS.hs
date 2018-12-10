import Estado


data AExp = Num Int
     |Var String
     |Som AExp AExp
     |Sub AExp AExp
     |Mul AExp AExp
  deriving(Show)

data BExp = TRUE
     | FALSE
     | Not BExp
     | And BExp BExp
     | Or  BExp BExp
     | Ig  AExp AExp
     | Leq AExp AExp
   deriving(Show)

data CExp =    While BExp CExp
     | If BExp CExp CExp
     | Seq CExp CExp
     | Atrib AExp AExp
     | DupAtrib AExp AExp AExp AExp
     | Repeat CExp BExp
     | For AExp AExp AExp CExp
     | Skip
   deriving(Show)                



aSmallStep :: (AExp,Estado) -> (AExp,Estado)
aSmallStep (Var x,s) = (Num (procuraVar s x),s)
aSmallStep (Som (Num x) (Num y), s) = (Num (x+y),s)
aSmallStep (Som (Num x) e2, s) = let (ef,_) = aSmallStep (e2 ,s)
                                 in (Som (Num x) ef,s)
aSmallStep (Som e1 e2,s)  = let (ef,_) = aSmallStep (e1, s)
                            in (Som ef e2,s)
aSmallStep (Sub (Num x) (Num y), s) = (Num (x-y), s)
aSmallStep (Sub (Num x) e2, s) = let (ef,_) = aSmallStep (e2,s)
                                  in (Sub (Num x) ef, s)
aSmallStep (Sub e1 e2, s)  = let (ef,_) = aSmallStep (e1, s)
                               in (Sub ef e2,s)
aSmallStep (Mul (Num x) (Num y), s) = (Num (x*y), s)
aSmallStep (Mul (Num x) e2,s) = let (ef,_) = aSmallStep(e2,s)
                                  in (Mul (Num x) ef, s)
aSmallStep (Mul e1 e2,s)  = let (ef,_) = aSmallStep(e1,s)
                              in (Mul ef e2,s)



interpretA :: (AExp,Estado) -> (AExp,Estado)
interpretA (a,s) = if isFinalA a then (a,s) else interpretA (aSmallStep (a,s))

isFinalA :: AExp -> Bool
isFinalA (Num a) = True
isFinalA x = False



bSmallStep :: (BExp,Estado) -> (BExp,Estado)
bSmallStep (Not FALSE,s)      = (TRUE,s)
bSmallStep (Not TRUE,s)       = (FALSE, s)
bSmallStep (Not b, s) = let (bn,sn) = bSmallStep (b,s)
                        in (Not bn ,sn)
bSmallStep (And TRUE b2,s)  = (b2,s)
bSmallStep (And FALSE b2,s) = (FALSE,s)
bSmallStep (And b1 b2,s)    = let (bn,sn) = bSmallStep (b1,s)
                              in (And bn b2,sn)
bSmallStep (Ig (Num x) (Num y),s) = ((if x==y then TRUE else FALSE), s)
bSmallStep (Ig (Num x) e2, s) = let (ef,_) = aSmallStep(e2,s)
                                in (Ig (Num x) ef, s)
bSmallStep (Ig e1 e2,s )  = let (ef,_) = aSmallStep(e1,s)
                            in (Ig ef e2, s)
bSmallStep (Or TRUE b2, s) = (TRUE, s)
bSmallStep (Or FALSE b2, s) = (b2, s)
bSmallStep (Or b1 b2,s )  = let (bn, sn) = bSmallStep (b1, s)
                            in (Or bn b2, sn)
bSmallStep (Leq (Num x) (Num y),s) = ((if x<=y then TRUE else FALSE), s)
bSmallStep (Leq (Num x) e2, s) = let (ef,_) = aSmallStep(e2,s)
                                 in (Leq (Num x) ef, s)
bSmallStep (Leq e1 e2,s )  = let (ef,_) = aSmallStep(e1,s)
                              in (Leq ef e2, s)


interpretB :: (BExp,Estado) -> (BExp,Estado)
interpretB (b,s) = if isFinalB b then (b,s) else interpretB (bSmallStep (b,s))

isFinalB :: BExp -> Bool
isFinalB TRUE = True
isFinalB FALSE = True
isFinalB x = False




cSmallStep :: (CExp,Estado) -> (CExp,Estado)
cSmallStep (If TRUE c1 c2, s) = (c1, s)
cSmallStep (If FALSE c1 c2, s) = (c2, s)
cSmallStep (If b c1 c2, s) = let (bn,sn) = bSmallStep(b,s)
                              in (If bn c1 c2, sn)
cSmallStep (Seq Skip c, s) = (c,s)
cSmallStep (Seq c1 c2,s)  = let (cn,sn) = cSmallStep(c1,s)
                              in (Seq cn c2,sn)
cSmallStep (Atrib (Var x) (Num y), s) = (Skip, (mudaVar s x y))
cSmallStep (Atrib (Var x) e,s) = let (ef,_) = aSmallStep(e, s)
                                 in (Atrib (Var x) ef, s)
cSmallStep (While b c, s) = cSmallStep(If b (Seq c (While b c)) Skip, s)
cSmallStep (DupAtrib (Var x) (Var y) (Num z) (Num w), s) = let (_,s1) = cSmallStep (Atrib (Var x) (Num z), s)
                                                            in let (_,sf) = cSmallStep (Atrib (Var y) (Num w), s1)
                                                            in (Skip, sf)
cSmallStep (DupAtrib (Var x) (Var y) (Num z) e, s) = let (ef,_) = aSmallStep(e,(mudaVar s x z))
                                                      in (DupAtrib (Var x) (Var y) (Num z) ef, s)
cSmallStep (DupAtrib (Var x) (Var y) e1 e2, s) = let (ef,_) = aSmallStep(e1, s)
                                                   in (DupAtrib (Var x) (Var y) ef e2, s)
cSmallStep (For (Var x) e1 e2 c, s) = (Seq (Atrib (Var x) e1) (If (Leq e1 e2) (Seq c (For (Var x) (Som e1 (Num 1)) e2 c)) Skip), s)
cSmallStep (Repeat c b, s) = (Seq c (If b Skip (Repeat c b)), s)




interpretC :: (CExp,Estado) -> (CExp,Estado)
interpretC (c,s) = if isFinalC c then (c,s) else interpretC (cSmallStep (c,s))

isFinalC :: CExp -> Bool
isFinalC Skip = True
isFinalC x = False


meuEstado :: Estado
meuEstado = [("x",3), ("y",1), ("z",0)]


exemplo :: AExp
exemplo = Som (Num 3) (Som (Var "x") (Var "y"))

-- RODANDO O EXEMPLO:
-- Hugs> interpretA (exemplo, meuEstado)

exemplo2 :: BExp
exemplo2 = And (And TRUE (Not FALSE)) (And (Not (Not TRUE)) TRUE)

-- *Main> interpretB (exemplo2,meuEstado)
-- (TRUE,[("x",3),("y",0),("z",0)])


