import List
import Char

data Prop = P Int              -- variables P 0, P 1, etc
          | F                  -- Bottom (falso)
          | Prop `Y` Prop      -- conjunción
          | Prop `O` Prop      -- disyunción
          | Prop `I` Prop      -- implica
          deriving Eq

n :: Prop -> Prop              -- negacion
n a = a `I` F

es_conjuncion :: Prop -> Bool
es_conjuncion (a `Y` b) = True
es_conjuncion _ = False

es_disyuncion :: Prop -> Bool
es_disyuncion (a `O` b) = True
es_disyuncion _ = False

es_implicacion :: Prop -> Bool
es_implicacion (a `I` b) = True
es_implicacion _ = False

es_bot :: Prop -> Bool
es_bot F = True
es_bot _ = False

es_negacion :: Prop -> Bool
--es_negacion a = es_implicacion a && es_bot (derecha a)
es_negacion (a `I` F) = True
es_negacion _ = False

izquierda :: Prop -> Prop -- pre: el argumento es una conjuncion, disyuncion, implicacion o equivalencia
izquierda (a `Y` b) = a
izquierda (a `O` b) = a
izquierda (a `I` b) = a

derecha :: Prop -> Prop -- pre: el argumento es una conjuncion, disyuncion, implicacion o equivalencia
derecha (a `Y` b) = b
derecha (a `O` b) = b
derecha (a `I` b) = b

-- visualizador de proposiciones
instance Show Prop where
  show (P v) = "p" ++ show v
  show F = "⊥"
  show (a `Y` b) = "(" ++ show a ++ " ∧ " ++ show b ++ ")"
  show (a `O` b) = "(" ++ show a ++ " ∨ " ++ show b ++ ")"
  show (a `I` b) = if es_bot b then if es_bot a then "⊤"
                                                else "(¬" ++ show a ++ ")"
                               else "(" ++ show a ++ " → " ++ show b ++ ")"

-- ejemplos de variables 
p0 = P 0
p1 = P 1
p2 = P 2
p3 = P 3
p4 = P 4
p5 = P 5

-- otros ejemplos
np0 = n p0
np1 = n p1
p0ip1 = p0 `I` p1
p0inp1 = p0 `I` np1
a0 = p0ip1 `O` p0inp1
np0ip1 = np0 `I` p1

-- variables de una proposicion
vars :: Prop -> [Int]
vars (P v) = [v]
vars F = []
vars (a `Y` b) = vars a `union` vars b
vars (a `O` b) = vars a `union` vars b
vars (a `I` b) = vars a `union` vars b

-- variables de un conjunto de proposiciones
varsGamma :: [Prop] -> [Int]
varsGamma as = foldr union [] (map vars as)

-- valuación de una proposición para una asignación
val :: Prop -> (Int -> Bool) -> Bool
val     (P v) f = f v
val        F  f = False
val (a `Y` b) f = val a f && val b f
val (a `O` b) f = val a f || val b f
val (a `I` b) f = val a f <= val b f

-- asignaciones asociadas a un conjunto de variables
asignaciones :: [Int] -> [Int -> Bool]
asignaciones [] = [\_ -> False]
asignaciones (v:vs) = asignar v (asignaciones vs)

asignar :: Int -> [Int -> Bool] -> [Int -> Bool]
asignar v fs = map (\f w -> if w == v then True else f w) fs ++ map (\f w -> if w == v then False else f w) fs

tautologia :: Prop -> Bool
tautologia a = all (val a) (asignaciones (vars a)) 

consecuencia_logica :: [Prop] -> Prop -> Bool
consecuencia_logica as b = all (\f -> all (\a -> val a f) as <= val b f) (asignaciones (varsGamma (b:as)))

data Deriv = Base Prop
           | Yintro Deriv Deriv
           | YelimIzq Deriv
           | YelimDer Deriv
           | Bot Deriv Prop
           | Ielim Deriv Deriv
           | Iintro Deriv Prop
           | RAA Deriv Prop
           | OintroIzq Deriv Prop
           | OintroDer Prop Deriv
           | Oelim Deriv Deriv Deriv
           deriving Eq

dmaxi = Ielim (RAA (Ielim (Ielim (Base np0) (Base np0ip1)) (Base np1)) p0) (Base p0ip1)

terceroexcluido = RAA (Ielim (OintroDer p0 (Iintro (Ielim (OintroIzq (Base p0) np0) (Base (n (p0 `O` np0)))) p0)) (Base (n (p0 `O` np0)))) (p0 `O` np0)

es_deriv :: Deriv -> Bool
es_deriv (Base a) = True
es_deriv (Yintro d e) = es_deriv d && es_deriv e
es_deriv (YelimIzq d) = es_deriv d && es_conjuncion (conclusion d)
es_deriv (YelimDer d) = es_deriv d && es_conjuncion (conclusion d)
es_deriv (Bot d a) = es_deriv d && es_bot (conclusion d)
es_deriv (Ielim d e) = es_deriv d && es_deriv e && es_implicacion concl && izquierda concl == (conclusion d)
                     where concl = conclusion e
es_deriv (Iintro d a) = es_deriv d
es_deriv (RAA d a) = es_deriv d && es_bot (conclusion d)
es_deriv (OintroIzq d b) = es_deriv d
es_deriv (OintroDer a d) = es_deriv d
es_deriv (Oelim d e f) = es_deriv d && es_deriv e && es_deriv f && es_disyuncion (conclusion d) && conclusion e == conclusion f

conclusion :: Deriv -> Prop -- pre: el argumento satisface es_deriv
conclusion (Base a) = a
conclusion (Yintro d e) = conclusion d `Y` conclusion e
conclusion (YelimIzq d) = izquierda (conclusion d) 
conclusion (YelimDer d) = derecha (conclusion d) 
conclusion (Bot d a) = a
conclusion (Ielim d e) = derecha (conclusion e)
conclusion (Iintro d a) = a `I` conclusion d
conclusion (RAA d a) = a
conclusion (OintroIzq d b) = conclusion d `O` b
conclusion (OintroDer a d) = a `O` conclusion d
conclusion (Oelim d e f) = conclusion e

hipotesis :: Deriv -> [Prop]
hipotesis (Base a) = [a]
hipotesis (Yintro d e) = hipotesis d `union` hipotesis e
hipotesis (YelimIzq d) = hipotesis d
hipotesis (YelimDer d) = hipotesis d
hipotesis (Bot d a) = hipotesis d
hipotesis (Ielim d e) = hipotesis d `union` hipotesis e
hipotesis (Iintro d a) = hipotesis d \\ [a]
hipotesis (RAA d a) = hipotesis d \\ [n a]
hipotesis (OintroIzq d b) = hipotesis d
hipotesis (OintroDer a d) = hipotesis d
hipotesis (Oelim d e f) = hipotesis d `union` (hipotesis e \\ [izquierda concl]) `union` (hipotesis f \\ [derecha concl])
                        where concl = conclusion d

instance Show Deriv where
  show d = mostrar d "" []

mostrar :: Deriv -> String -> [(Prop,Int)] -> String
mostrar x@(Base a) indent canceladas = 
  case lookup a canceladas of
    Just i -> indent ++ "[Hip " ++ show a ++ "]" ++ show i ++ "\n"
    Nothing -> indent ++ "Hip " ++ show a ++ "\n"
mostrar x@(Yintro d e) indent canceladas =
  indent ++ "∧ I\n" ++ mostrar d (tab++indent) canceladas ++ mostrar e (tab++indent) canceladas ++ indent ++ show (conclusion x) ++ "\n"
mostrar x@(YelimIzq d) indent canceladas =
  indent ++ "∧ Eizq\n" ++ mostrar d (tab++indent) canceladas ++ indent ++ show (conclusion x) ++ "\n"
mostrar x@(YelimDer d) indent canceladas =
  indent ++ "∧ Eder\n" ++ mostrar d (tab++indent) canceladas ++ indent ++ show (conclusion x) ++ "\n"
mostrar x@(Bot d a) indent canceladas =
  indent ++ "Bot\n" ++ mostrar d (tab++indent) canceladas ++ indent ++ show a ++ "\n"
mostrar x@(Ielim d e) indent canceladas =
  indent ++ "→ E\n" ++ mostrar d (tab++indent) canceladas ++ mostrar e (tab++indent) canceladas ++ indent ++ show (conclusion x) ++ "\n"
mostrar x@(Iintro d a) indent canceladas =
  indent ++ "→ I " ++ show i ++ "\n" ++ mostrar d (tab++indent) ((a,i):canceladas) ++ indent ++ show (conclusion x) ++ "\n"
  where i = length canceladas
mostrar x@(RAA d a) indent canceladas =
  indent ++ "RAA " ++ show i ++ "\n" ++ mostrar d (tab++indent) ((n a,i):canceladas) ++ indent ++ show a ++ "\n"
  where i = length canceladas
mostrar x@(OintroIzq d a) indent canceladas =
  indent ++ "∨ Iizq\n" ++ mostrar d (tab++indent) canceladas ++ indent ++ show (conclusion x) ++ "\n"
mostrar x@(OintroDer a d) indent canceladas =
  indent ++ "∨ Ider\n" ++ mostrar d (tab++indent) canceladas ++ indent ++ show (conclusion x) ++ "\n"
mostrar x@(Oelim d e f) indent canceladas =
  indent ++ "∨ E " ++ show i ++ "\n" ++ mostrar d (tab++indent) canceladas
                                     ++ mostrar e (tab++indent) ((izquierda c,i):canceladas)
                                     ++ mostrar f (tab++indent) ((derecha c,i):canceladas) ++ indent ++ show c ++ "\n"
  where c = conclusion d
        i = length canceladas

tab :: String
tab = "|  "
