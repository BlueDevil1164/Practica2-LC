module Clausulas where
-- ---------------------------------------------------------------------
-- Librería suxiliares --
-- ---------------------------------------------------------------------
import SintaxisSemantica
import FormasNormales
import Data.List
import Test.HUnit
import Verificacion
-- ---------------------------------------------------------------------
-- Cláusulas --
-- ---------------------------------------------------------------------
-- ---------------------------------------------------------------------
-- Definir el tipo de datos Cláusula como una lista de
-- literales.
-- ---------------------------------------------------------------------
type Cláusula = [Literal]
-- ---------------------------------------------------------------------
-- Definir la función
-- cláusula :: Prop -> Cláusula
-- tal que (cláusula f) es la cláusula de la fórmula-clausal f. Por
-- ejemplo,
-- cláusula p ==> [p]
-- cláusula (no p) ==> [no p]
-- cláusula (((no p) \/ r) \/ ((no p) \/ q)) ==> [q,r,no p]
-- ---------------------------------------------------------------------
cláusula :: Prop -> Cláusula
cláusula f
| literal f = [f]
cláusula (Disj f g) = sort ((cláusula f) `union` (cláusula g))
-- ---------------------------------------------------------------------
-- Definir la función
-- cláusulasFNC :: Prop -> [Cláusula]
-- tal que (cláusulasFNC f) es el conjunto de cláusulas de la fórmula en
-- forma normal conjuntiva f. Por ejmplo,
-- cláusulasFNC (p /\ ((no q) \/ r))
-- ==> [[p],[r,-q]]
-- cláusulasFNC (((no p) \/ q) /\ ((no p) \/ (no r)))
-- ==> [[q,-p],[-p,-r]]
-- ---------------------------------------------------------------------
cláusulasFNC :: Prop -> [Cláusula]
cláusulasFNC (Conj f g) =
(cláusulasFNC f) `union` (cláusulasFNC g)
cláusulasFNC f =
[cláusula f]
-- ---------------------------------------------------------------------
-- Ejercicio 4: Definir la función
-- cláusulas :: Prop -> [Cláusula]
-- tal que (cláusulas f) es un conjunto de cláusulas equivalente a
-- f. Por ejemplo,
-- cláusulas (p /\ (q --> r))
-- ==> [[p],[r,-q]]
-- cláusulas (no (p /\ (q --> r)))
-- ==> [[q,-p],[-p,-r]]
-- cláusulas (no(p <--> r))
-- ==> [[p,r],[p,no p],[r,no r],[no p,no r]]
-- ---------------------------------------------------------------------
Capítulo 3. Cláusulas 
cláusulas :: Prop -> [Cláusula]
cláusulas f =
cláusulasFNC (formaNormalConjuntiva f)
-- ---------------------------------------------------------------------
-- Cláusulas de un conjunto de fórmulas --
-- ---------------------------------------------------------------------
-- ---------------------------------------------------------------------
-- cláusulasConjunto :: [Prop] -> [Cláusula]
-- tal que (cláusulasConjunto s) es un conjunto de cláusulas equivalente
-- a s. Por ejemplo,
-- cláusulasConjunto [p --> q, q --> r] ==> [[q,-p],[r,-q]]
-- cláusulasConjunto [p --> q, q <--> p] ==> [[q,-p],[p,-q]]
-- ---------------------------------------------------------------------
cláusulasConjunto :: [Prop] -> [Cláusula]
cláusulasConjunto s =
uniónGeneral [cláusulas f | f <- s]
-- ---------------------------------------------------------------------
-- Símbolos proposicionales de una cláusula --
-- ---------------------------------------------------------------------
-- ---------------------------------------------------------------------
-- símbolosProposicionalesCláusula :: Cláusula -> [Prop]
-- tal que (símbolosProposicionalesCláusula c) es el conjunto de los
-- símbolos proposicionales de c. Por ejemplo,
-- símbolosProposicionalesCláusula [p, q, no p] ==> [p,q]
-- ---------------------------------------------------------------------
símbolosProposicionalesCláusula :: Cláusula -> [Prop]
símbolosProposicionalesCláusula = símbolosPropConj
-- ---------------------------------------------------------------------
-- Símbolos proposicionales de un conjunto de cláusulas --
-- ---------------------------------------------------------------------
-- ---------------------------------------------------------------------
-- símbolosProposicionalesConjuntoCláusula :: [Cláusula] -> [Prop]
-- tal que (símbolosProposicionalesConjuntoCláusula s) es el conjunto de los
-- símbolos proposicionales de s. Por ejemplo,
-- símbolosProposicionalesConjuntoCláusula [[p, q],[no q, r]]
-- ==> [p,q,r]
-- ---------------------------------------------------------------------
símbolosProposicionalesConjuntoCláusula :: [Cláusula] -> [Prop]
símbolosProposicionalesConjuntoCláusula s =
uniónGeneral [símbolosProposicionalesCláusula c | c <- s]
-- ---------------------------------------------------------------------
-- Interpretaciones de una cláusula --
-- ---------------------------------------------------------------------
-- ---------------------------------------------------------------------
-- interpretacionesCláusula :: Cláusula -> [Interpretación]
-- tal que (interpretacionesCláusula c) es el conjunto de
-- interpretaciones de c. Por ejemplo,
-- interpretacionesCláusula [p, q, no p] ==> [[p,q],[p],[q],[]]
-- interpretacionesCláusula [] ==> [[]]
-- ---------------------------------------------------------------------
interpretacionesCláusula :: Cláusula -> [Interpretación]
interpretacionesCláusula c =
subconjuntos (símbolosProposicionalesCláusula c)
-- ---------------------------------------------------------------------
-- Interpretaciones de un conjunto de cláusulas --
-- ---------------------------------------------------------------------
-- ---------------------------------------------------------------------
-- interpretacionesConjuntoCláusula :: [Cláusula] -> [Interpretación]
-- tal que (interpretacionesConjuntoCláusula s) es el conjunto de
-- interpretaciones de s. Por ejemplo,
-- interpretacionesConjuntoCláusula [[p, no q],[no p, q]]
-- ==> [[p,q],[p],[q],[]]
-- interpretacionesConjuntoCláusula []
-- ==> [[]]
-- ---------------------------------------------------------------------
interpretacionesConjuntoCláusula :: [Cláusula] -> [Interpretación]
interpretacionesConjuntoCláusula c =
subconjuntos (símbolosProposicionalesConjuntoCláusula c)
-- ---------------------------------------------------------------------
-- Modelos de cláusulas --
-- ---------------------------------------------------------------------
-- ---------------------------------------------------------------------
-- esModeloLiteral :: Interpretación -> Literal -> Bool
-- tal que (esModeloLiteral i l) se verifica si i es modelo de l. Por
-- ejemplo,
-- esModeloLiteral [p,r] p ==> True
-- esModeloLiteral [p,r] q ==> False
-- esModeloLiteral [p,r] (no p) ==> False
-- esModeloLiteral [p,r] (no q) ==> True
-- ---------------------------------------------------------------------
esModeloLiteral :: Interpretación -> Literal -> Bool
esModeloLiteral i (Atom s) = elem (Atom s) i
esModeloLiteral i (Neg (Atom s)) = notElem (Atom s) i
-- ---------------------------------------------------------------------
-- esModeloCláusula :: Interpretación -> Cláusula -> Bool
-- tal que (esModeloCláusula i c) se verifica si i es modelo de c . Por
-- ejemplo,
-- esModeloCláusula [p,r] [p, q] ==> True
-- esModeloCláusula [r] [p, no q] ==> True
-- esModeloCláusula [q,r] [p, no q] ==> False
-- esModeloCláusula [q,r] [] ==> False
-- ---------------------------------------------------------------------
esModeloCláusula :: Interpretación -> Cláusula -> Bool
esModeloCláusula i c =
or [esModeloLiteral i l | l <- c]
-- ---------------------------------------------------------------------
-- modelosCláusula :: Cláusula -> [Interpretación]
-- tal que (modelosCláusula c) es la lista de los modelos de c. Por
-- ejemplo,
-- modelosCláusula [no p, q] ==> [[p,q],[q],[]]
-- modelosCláusula [no p, p] ==> [[p],[]]
-- modelosCláusula [] ==> []
-- ---------------------------------------------------------------------
modelosCláusula :: Cláusula -> [Interpretación]
modelosCláusula c =
[i | i <- interpretacionesCláusula c,
esModeloCláusula i c]
-- ---------------------------------------------------------------------
-- Modelos de conjuntos de cláusulas --
-- ---------------------------------------------------------------------
-- ---------------------------------------------------------------------
-- esModeloConjuntoCláusulas :: Interpretación -> [Cláusula] -> Bool
-- tal que (esModeloConjuntoCláusulas i c) se verifica si i es modelo de
-- c. Por ejemplo,
-- esModeloConjuntoCláusulas [p,r] [[p, no q], [r]] ==> True
-- esModeloConjuntoCláusulas [p] [[p, no q], [r]] ==> False
-- esModeloConjuntoCláusulas [p] [] ==> True
-- ---------------------------------------------------------------------
esModeloConjuntoCláusulas :: Interpretación -> [Cláusula] -> Bool
esModeloConjuntoCláusulas i s =
and [esModeloCláusula i c | c <- s]
-- ---------------------------------------------------------------------
-- modelosConjuntoCláusulas :: [Cláusula] -> [Interpretación]
-- tal que (modelosConjuntoCláusulas s) es la lista de los modelos de
-- s. Por ejemplo,
-- modelosConjuntoCláusulas [[no p, q], [no q, p]]
-- ==> [[p,q],[]]
-- modelosConjuntoCláusulas [[no p, q], [p], [no q]]
-- ==> []
-- modelosConjuntoCláusulas [[p, no p, q]]
-- ==> [[p,q],[p],[q],[]]
-- ---------------------------------------------------------------------
modelosConjuntoCláusulas :: [Cláusula] -> [Interpretación]
modelosConjuntoCláusulas s =
[i | i <- interpretacionesConjuntoCláusula s,
esModeloConjuntoCláusulas i s]
-- ---------------------------------------------------------------------
-- Cláusulas válidas, satisfacible --
-- ---------------------------------------------------------------------
-- esCláusulaVálida :: Cláusula -> Bool
-- tal que (esCláusulaVálida c) se verifica si la cláusula c es
-- válida. Por ejemplo,
-- esCláusulaVálida [p, q, no p] ==> True
-- esCláusulaVálida [p, q, no r] ==> False
-- esCláusulaVálida [] ==> False
-- ---------------------------------------------------------------------
esCláusulaVálida :: Cláusula -> Bool
esCláusulaVálida c =
[l | l <- c, elem (complementario l) c] /= []
-- Definición alternativa:
esCláusulaVálida1 :: Cláusula -> Bool
esCláusulaVálida1 c =
and [esModeloCláusula i c | i <- interpretacionesCláusula c]
-- ---------------------------------------------------------------------
-- esCláusulaSatisfacible :: Cláusula -> Bool
-- tal que (esCláusulaSatisfacible c) se verifica si la cláusula c es
-- satisfacible. Por ejemplo,
-- esCláusulaSatisfacible [p, q, no p] ==> True
-- esCláusulaSatisfacible [p, q, no r] ==> True
-- esCláusulaSatisfacible [] ==> False
-- ---------------------------------------------------------------------
esCláusulaSatisfacible :: Cláusula -> Bool
esCláusulaSatisfacible c =
not (null c)
-- Definición alternativa:
esCláusulaSatisfacible1 :: Cláusula -> Bool
esCláusulaSatisfacible1 c =
or [esModeloCláusula i c | i <- interpretacionesCláusula c]
