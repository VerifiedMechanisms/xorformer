import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin

set_option linter.style.header false
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000

/-! An exact finite certificate for a separable reciprocal relaxation.
The 512 witnesses are checked by kernel reduction. No head lower bound follows.
-/
namespace HeadComplexity.MobiusFourParameterShattering

def scale : ℤ := 2

def poles : Fin 9 → Fin 4 → ℤ :=
  ![![66049, 83022819845310162051379891201, 23921930261174538048551511546295524724904449, 23921930261174538048551511546295524724904449],
    ![4362470401, 362184594182720980613658216570962841601, 19031147999601100801, 288136807515649],
    ![288136807515649, 4362470401, 66049, 362184594182720980613658216570962841601],
    ![19031147999601100801, 1256988294225653106805249, 288136807515649, 83022819845310162051379891201],
    ![1256988294225653106805249, 19031147999601100801, 1256988294225653106805249, 1256988294225653106805249],
    ![83022819845310162051379891201, 5483574227962890893331590433934849, 83022819845310162051379891201, 4362470401],
    ![5483574227962890893331590433934849, 66049, 4362470401, 5483574227962890893331590433934849],
    ![362184594182720980613658216570962841601, 288136807515649, 5483574227962890893331590433934849, 66049],
    ![23921930261174538048551511546295524724904449, 23921930261174538048551511546295524724904449, 362184594182720980613658216570962841601, 19031147999601100801]]

def residues : Fin 9 → Fin 4 → ℤ :=
  ![![-264196, 83022819845310162051379891201, -71765790783523614145654534638886574174713347, 71765790783523614145654534638886574174713347],
    ![-13087411203, 724369188365441961227316433141925683202, -19031147999601100801, 1152547230062596],
    ![-1152547230062596, 13087411203, -132098, 724369188365441961227316433141925683202],
    ![38062295999202201602, -1256988294225653106805249, 864410422546947, -166045639690620324102759782402],
    ![1256988294225653106805249, -57093443998803302403, 5027953176902612427220996, -5027953176902612427220996],
    ![83022819845310162051379891201, -16450722683888672679994771301804547, 249068459535930486154139673603, -17449881604],
    ![-10967148455925781786663180867869698, 264196, -4362470401, 16450722683888672679994771301804547],
    ![362184594182720980613658216570962841601, -864410422546947, 21934296911851563573326361735739396, 132098],
    ![47843860522349076097103023092591049449808898, -23921930261174538048551511546295524724904449, 724369188365441961227316433141925683202, -19031147999601100801]]

def thresholds : Fin 9 → ℤ := ![1, 3, 1, 1, 1, 1, 1, 5, 5]

def cutsData : Array (Fin 4 → ℕ) :=
  #[![9, 9, 9, 9],
    ![9, 9, 9, 8],
    ![9, 7, 9, 9],
    ![9, 5, 9, 9],
    ![9, 9, 8, 7],
    ![9, 9, 9, 7],
    ![9, 7, 8, 7],
    ![9, 7, 9, 7],
    ![0, 3, 9, 9],
    ![1, 1, 8, 8],
    ![0, 2, 1, 1],
    ![2, 1, 8, 8],
    ![0, 1, 8, 7],
    ![1, 1, 8, 7],
    ![3, 1, 8, 9],
    ![3, 3, 8, 7],
    ![9, 2, 3, 9],
    ![9, 2, 3, 8],
    ![4, 5, 8, 9],
    ![4, 4, 8, 8],
    ![9, 1, 3, 9],
    ![9, 2, 3, 7],
    ![4, 6, 8, 7],
    ![4, 4, 8, 7],
    ![9, 2, 0, 9],
    ![1, 5, 8, 8],
    ![2, 5, 8, 9],
    ![2, 4, 8, 8],
    ![9, 1, 0, 9],
    ![9, 1, 2, 7],
    ![3, 6, 8, 7],
    ![3, 5, 9, 7],
    ![5, 9, 8, 8],
    ![5, 9, 9, 8],
    ![5, 7, 8, 8],
    ![5, 7, 9, 8],
    ![5, 9, 8, 7],
    ![5, 9, 9, 7],
    ![5, 7, 8, 7],
    ![5, 7, 9, 7],
    ![0, 2, 1, 3],
    ![1, 2, 1, 3],
    ![0, 1, 0, 2],
    ![2, 1, 0, 2],
    ![0, 1, 1, 3],
    ![1, 1, 1, 3],
    ![0, 1, 1, 2],
    ![3, 1, 0, 2],
    ![4, 9, 9, 9],
    ![4, 9, 9, 8],
    ![4, 7, 8, 9],
    ![4, 7, 9, 8],
    ![4, 9, 8, 7],
    ![4, 9, 9, 7],
    ![4, 7, 8, 7],
    ![4, 7, 9, 7],
    ![3, 9, 8, 9],
    ![1, 9, 9, 7],
    ![2, 7, 8, 7],
    ![3, 7, 9, 8],
    ![3, 9, 8, 7],
    ![3, 9, 9, 7],
    ![3, 7, 8, 7],
    ![3, 7, 9, 7],
    ![0, 9, 9, 1],
    ![1, 2, 6, 3],
    ![0, 5, 9, 2],
    ![2, 9, 9, 1],
    ![9, 9, 7, 6],
    ![6, 1, 3, 3],
    ![8, 6, 7, 0],
    ![9, 0, 7, 0],
    ![0, 2, 8, 6],
    ![1, 0, 9, 8],
    ![2, 0, 8, 9],
    ![2, 0, 8, 8],
    ![0, 1, 8, 6],
    ![1, 0, 8, 7],
    ![3, 0, 8, 9],
    ![3, 2, 2, 1],
    ![1, 6, 8, 5],
    ![1, 5, 9, 5],
    ![2, 6, 8, 5],
    ![2, 5, 8, 5],
    ![9, 0, 3, 9],
    ![9, 0, 0, 5],
    ![4, 6, 8, 6],
    ![4, 5, 9, 6],
    ![0, 5, 9, 6],
    ![1, 4, 8, 6],
    ![2, 6, 8, 6],
    ![2, 5, 9, 6],
    ![9, 0, 2, 9],
    ![9, 1, 2, 6],
    ![3, 6, 8, 6],
    ![3, 4, 9, 6],
    ![2, 9, 8, 3],
    ![1, 9, 9, 2],
    ![2, 9, 8, 2],
    ![2, 2, 3, 2],
    ![3, 9, 8, 3],
    ![5, 1, 2, 3],
    ![5, 7, 8, 6],
    ![5, 1, 5, 3],
    ![0, 2, 2, 3],
    ![2, 2, 2, 3],
    ![0, 2, 2, 2],
    ![2, 2, 2, 2],
    ![0, 1, 2, 3],
    ![1, 1, 2, 3],
    ![0, 1, 2, 2],
    ![3, 2, 2, 2],
    ![0, 7, 8, 5],
    ![2, 9, 9, 5],
    ![2, 7, 8, 5],
    ![2, 7, 9, 5],
    ![4, 9, 8, 6],
    ![4, 9, 9, 5],
    ![3, 7, 8, 5],
    ![4, 7, 9, 5],
    ![2, 9, 8, 6],
    ![1, 7, 9, 6],
    ![2, 7, 8, 6],
    ![2, 7, 9, 6],
    ![3, 9, 8, 6],
    ![3, 8, 9, 6],
    ![3, 7, 8, 6],
    ![3, 7, 9, 6],
    ![9, 9, 6, 9],
    ![6, 4, 0, 3],
    ![9, 7, 6, 9],
    ![9, 5, 5, 8],
    ![9, 9, 6, 7],
    ![6, 4, 1, 3],
    ![9, 7, 6, 7],
    ![4, 1, 1, 0],
    ![6, 6, 0, 3],
    ![6, 5, 0, 3],
    ![0, 3, 1, 0],
    ![1, 1, 0, 0],
    ![6, 6, 1, 3],
    ![6, 5, 1, 3],
    ![0, 1, 1, 0],
    ![3, 1, 0, 0],
    ![9, 6, 3, 9],
    ![9, 4, 3, 8],
    ![9, 6, 4, 8],
    ![9, 4, 4, 8],
    ![9, 6, 3, 7],
    ![9, 5, 3, 7],
    ![9, 6, 4, 7],
    ![4, 4, 1, 0],
    ![9, 6, 1, 8],
    ![9, 5, 0, 7],
    ![2, 6, 0, 0],
    ![2, 5, 1, 0],
    ![9, 6, 2, 7],
    ![9, 5, 1, 7],
    ![3, 7, 1, 0],
    ![3, 5, 1, 0],
    ![9, 9, 5, 8],
    ![4, 3, 0, 3],
    ![9, 7, 5, 8],
    ![5, 4, 0, 2],
    ![9, 9, 5, 7],
    ![5, 3, 1, 3],
    ![9, 7, 5, 7],
    ![5, 4, 1, 2],
    ![5, 7, 0, 3],
    ![2, 3, 0, 3],
    ![0, 3, 0, 2],
    ![1, 3, 0, 2],
    ![5, 6, 1, 3],
    ![3, 3, 1, 3],
    ![5, 6, 1, 2],
    ![3, 3, 1, 2],
    ![9, 9, 3, 9],
    ![4, 4, 0, 3],
    ![9, 7, 4, 9],
    ![4, 4, 0, 2],
    ![9, 9, 4, 7],
    ![4, 4, 1, 3],
    ![9, 7, 4, 7],
    ![4, 4, 1, 2],
    ![9, 9, 2, 9],
    ![4, 5, 0, 3],
    ![4, 8, 0, 2],
    ![4, 5, 0, 2],
    ![9, 9, 2, 7],
    ![4, 5, 1, 3],
    ![4, 8, 1, 2],
    ![4, 5, 1, 2],
    ![1, 6, 6, 3],
    ![1, 9, 9, 0],
    ![2, 6, 6, 3],
    ![9, 4, 0, 2],
    ![9, 9, 6, 6],
    ![9, 5, 3, 4],
    ![9, 7, 6, 6],
    ![9, 5, 6, 6],
    ![9, 6, 0, 4],
    ![9, 5, 0, 4],
    ![9, 9, 0, 1],
    ![9, 5, 0, 2],
    ![9, 6, 2, 4],
    ![9, 5, 2, 4],
    ![9, 9, 2, 1],
    ![9, 5, 2, 2],
    ![1, 8, 3, 1],
    ![9, 4, 0, 5],
    ![2, 7, 4, 1],
    ![2, 5, 4, 1],
    ![9, 6, 3, 6],
    ![9, 5, 3, 6],
    ![9, 6, 4, 6],
    ![9, 5, 4, 6],
    ![9, 6, 0, 6],
    ![9, 5, 0, 6],
    ![2, 7, 2, 1],
    ![2, 5, 2, 0],
    ![9, 6, 2, 6],
    ![9, 5, 2, 6],
    ![4, 7, 2, 0],
    ![4, 5, 2, 0],
    ![1, 7, 6, 3],
    ![2, 3, 3, 3],
    ![2, 7, 6, 3],
    ![2, 5, 5, 3],
    ![9, 9, 5, 6],
    ![5, 5, 3, 3],
    ![9, 9, 5, 2],
    ![5, 5, 5, 2],
    ![9, 9, 0, 4],
    ![2, 3, 2, 3],
    ![9, 9, 0, 2],
    ![2, 3, 2, 2],
    ![9, 9, 2, 4],
    ![5, 5, 2, 3],
    ![9, 9, 2, 2],
    ![5, 5, 2, 2],
    ![2, 8, 4, 3],
    ![2, 5, 3, 3],
    ![2, 7, 4, 3],
    ![2, 5, 4, 3],
    ![9, 9, 4, 6],
    ![4, 5, 3, 3],
    ![9, 7, 4, 6],
    ![4, 5, 4, 3],
    ![9, 9, 0, 6],
    ![2, 5, 2, 3],
    ![2, 7, 2, 2],
    ![2, 5, 2, 2],
    ![9, 9, 2, 6],
    ![4, 5, 2, 3],
    ![4, 6, 2, 2],
    ![3, 4, 2, 2],
    ![8, 9, 7, 9],
    ![6, 2, 0, 4],
    ![6, 7, 7, 8],
    ![6, 2, 5, 8],
    ![8, 8, 7, 7],
    ![6, 1, 1, 4],
    ![6, 7, 7, 7],
    ![8, 5, 7, 7],
    ![1, 1, 7, 9],
    ![1, 1, 7, 8],
    ![3, 2, 6, 9],
    ![3, 3, 7, 8],
    ![0, 1, 6, 7],
    ![1, 1, 6, 7],
    ![3, 1, 7, 9],
    ![3, 1, 6, 7],
    ![8, 2, 3, 9],
    ![6, 2, 0, 5],
    ![6, 2, 4, 9],
    ![4, 4, 7, 8],
    ![7, 1, 3, 9],
    ![6, 1, 0, 5],
    ![6, 1, 4, 9],
    ![6, 1, 4, 8],
    ![1, 6, 7, 8],
    ![1, 5, 7, 7],
    ![2, 6, 7, 7],
    ![2, 5, 7, 8],
    ![6, 1, 0, 9],
    ![6, 1, 2, 7],
    ![3, 6, 7, 7],
    ![3, 5, 7, 7],
    ![5, 9, 7, 8],
    ![4, 2, 0, 4],
    ![4, 2, 5, 9],
    ![4, 2, 5, 8],
    ![5, 9, 7, 7],
    ![5, 1, 0, 4],
    ![5, 7, 7, 7],
    ![4, 2, 5, 7],
    ![0, 1, 0, 4],
    ![2, 1, 0, 4],
    ![2, 1, 5, 9],
    ![3, 2, 5, 8],
    ![0, 1, 5, 7],
    ![3, 1, 0, 4],
    ![3, 1, 5, 9],
    ![3, 1, 5, 7],
    ![4, 9, 7, 9],
    ![4, 2, 0, 5],
    ![4, 7, 7, 8],
    ![4, 2, 4, 8],
    ![4, 1, 3, 9],
    ![4, 1, 1, 5],
    ![4, 1, 4, 9],
    ![4, 1, 4, 7],
    ![1, 1, 3, 9],
    ![1, 1, 0, 6],
    ![2, 7, 7, 9],
    ![2, 1, 4, 8],
    ![0, 1, 1, 7],
    ![5, 1, 1, 6],
    ![3, 1, 4, 9],
    ![3, 1, 4, 7],
    ![0, 9, 7, 1],
    ![1, 5, 7, 4],
    ![2, 9, 7, 1],
    ![2, 2, 6, 5],
    ![8, 9, 7, 6],
    ![1, 0, 6, 5],
    ![6, 0, 7, 9],
    ![6, 5, 7, 4],
    ![0, 0, 6, 8],
    ![1, 2, 6, 6],
    ![2, 0, 6, 9],
    ![2, 3, 7, 6],
    ![0, 0, 6, 7],
    ![1, 0, 6, 6],
    ![3, 0, 7, 9],
    ![3, 0, 6, 6],
    ![0, 5, 7, 5],
    ![1, 5, 7, 5],
    ![2, 6, 7, 5],
    ![2, 5, 7, 5],
    ![6, 0, 3, 9],
    ![8, 1, 0, 5],
    ![4, 6, 7, 6],
    ![3, 5, 7, 5],
    ![0, 5, 7, 6],
    ![8, 2, 0, 6],
    ![2, 6, 7, 6],
    ![2, 4, 7, 6],
    ![6, 0, 0, 9],
    ![8, 2, 1, 6],
    ![3, 6, 7, 6],
    ![3, 5, 7, 6],
    ![0, 2, 5, 5],
    ![1, 2, 3, 4],
    ![2, 7, 7, 4],
    ![2, 2, 4, 4],
    ![3, 9, 7, 4],
    ![5, 0, 0, 4],
    ![5, 9, 7, 2],
    ![5, 0, 5, 8],
    ![0, 0, 0, 4],
    ![2, 2, 2, 4],
    ![2, 0, 5, 9],
    ![2, 0, 5, 8],
    ![0, 0, 1, 4],
    ![3, 0, 2, 4],
    ![3, 0, 5, 9],
    ![3, 0, 5, 8],
    ![0, 9, 7, 5],
    ![2, 2, 3, 5],
    ![2, 7, 7, 5],
    ![2, 2, 4, 5],
    ![4, 9, 7, 6],
    ![5, 0, 3, 8],
    ![4, 7, 7, 5],
    ![4, 0, 4, 6],
    ![0, 0, 1, 8],
    ![2, 0, 0, 8],
    ![2, 7, 7, 6],
    ![2, 0, 4, 8],
    ![4, 0, 0, 9],
    ![5, 0, 1, 8],
    ![3, 0, 4, 9],
    ![3, 2, 4, 6],
    ![6, 9, 6, 9],
    ![6, 4, 0, 4],
    ![5, 6, 6, 8],
    ![5, 5, 6, 8],
    ![8, 9, 6, 7],
    ![6, 4, 1, 4],
    ![6, 7, 6, 7],
    ![6, 5, 5, 7],
    ![1, 3, 6, 9],
    ![1, 3, 6, 8],
    ![3, 3, 6, 9],
    ![3, 3, 6, 8],
    ![6, 6, 1, 4],
    ![6, 5, 1, 4],
    ![5, 9, 1, 0],
    ![3, 3, 6, 7],
    ![6, 4, 3, 9],
    ![6, 4, 3, 8],
    ![6, 4, 4, 9],
    ![4, 5, 6, 8],
    ![6, 6, 3, 7],
    ![6, 3, 3, 7],
    ![4, 6, 6, 7],
    ![4, 4, 6, 7],
    ![1, 6, 6, 9],
    ![1, 5, 6, 8],
    ![3, 6, 6, 9],
    ![3, 5, 6, 8],
    ![8, 6, 2, 7],
    ![8, 5, 2, 7],
    ![3, 9, 1, 1],
    ![3, 5, 6, 7],
    ![8, 9, 5, 9],
    ![5, 4, 0, 4],
    ![5, 5, 5, 9],
    ![5, 5, 5, 8],
    ![5, 9, 5, 7],
    ![5, 4, 1, 4],
    ![5, 7, 6, 7],
    ![4, 3, 5, 7],
    ![6, 9, 0, 4],
    ![1, 3, 5, 8],
    ![6, 9, 0, 2],
    ![3, 3, 5, 8],
    ![6, 9, 1, 4],
    ![5, 5, 1, 4],
    ![5, 9, 1, 2],
    ![3, 3, 5, 7],
    ![4, 9, 3, 9],
    ![4, 4, 0, 5],
    ![6, 7, 4, 8],
    ![5, 5, 4, 8],
    ![6, 7, 3, 7],
    ![5, 5, 3, 7],
    ![4, 7, 5, 7],
    ![5, 5, 4, 7],
    ![1, 9, 0, 4],
    ![1, 3, 0, 8],
    ![2, 3, 4, 9],
    ![2, 5, 5, 8],
    ![6, 9, 1, 7],
    ![5, 5, 1, 7],
    ![3, 6, 5, 7],
    ![3, 3, 4, 7],
    ![1, 6, 6, 4],
    ![1, 5, 6, 4],
    ![2, 6, 6, 4],
    ![2, 5, 6, 4],
    ![8, 9, 6, 3],
    ![6, 3, 2, 4],
    ![3, 6, 6, 4],
    ![6, 5, 6, 4],
    ![0, 3, 6, 6],
    ![1, 3, 6, 6],
    ![7, 9, 0, 0],
    ![2, 3, 6, 6],
    ![8, 6, 2, 4],
    ![7, 5, 1, 4],
    ![8, 9, 2, 1],
    ![3, 3, 6, 6],
    ![1, 9, 4, 1],
    ![7, 4, 0, 5],
    ![2, 6, 6, 5],
    ![2, 5, 6, 5],
    ![6, 6, 3, 6],
    ![6, 4, 2, 5],
    ![4, 6, 6, 5],
    ![6, 4, 4, 5],
    ![0, 5, 6, 6],
    ![1, 5, 6, 6],
    ![2, 9, 2, 1],
    ![2, 5, 6, 6],
    ![6, 6, 2, 6],
    ![6, 3, 2, 6],
    ![3, 6, 6, 6],
    ![3, 4, 6, 6],
    ![2, 9, 6, 4],
    ![2, 3, 3, 4],
    ![2, 7, 6, 4],
    ![2, 5, 5, 4],
    ![5, 9, 5, 6],
    ![3, 3, 3, 4],
    ![5, 9, 5, 2],
    ![5, 5, 5, 6],
    ![0, 3, 5, 6],
    ![2, 3, 2, 4],
    ![8, 9, 0, 2],
    ![2, 3, 5, 6],
    ![5, 6, 2, 4],
    ![3, 3, 2, 4],
    ![5, 9, 2, 2],
    ![3, 3, 5, 6],
    ![1, 7, 6, 5],
    ![1, 4, 3, 4],
    ![2, 9, 4, 2],
    ![2, 5, 5, 5],
    ![4, 9, 5, 5],
    ![3, 5, 3, 5],
    ![4, 7, 6, 6],
    ![4, 5, 5, 6],
    ![0, 5, 5, 6],
    ![1, 5, 5, 6],
    ![2, 7, 6, 6],
    ![2, 5, 5, 6],
    ![8, 9, 2, 6],
    ![3, 5, 3, 6],
    ![3, 7, 6, 6],
    ![3, 5, 5, 6]]

def cuts (i : Fin 512) : Fin 4 → ℕ :=
  cutsData[i.val]'(by change i.val < 512; exact i.isLt)

def witness (i : Fin 512) (h : Fin 4) : ℤ := (257 : ℤ) ^ (2 * cuts i h + 1)

def labels (i : Fin 512) (q : Fin 9) : Bool :=
  decide (i.val / 2 ^ q.val % 2 = 1)

def cleared (x : Fin 4 → ℤ) (q : Fin 9) : ℤ :=
  let d := fun h => x h + poles q h
  scale * (residues q 0 * d 1 * d 2 * d 3 +
    residues q 1 * d 0 * d 2 * d 3 +
    residues q 2 * d 0 * d 1 * d 3 +
    residues q 3 * d 0 * d 1 * d 2) - thresholds q * d 0 * d 1 * d 2 * d 3

#check witness

theorem poles_positive : ∀ q h, 0 < poles q h := by
  decide +kernel

#check poles_positive

theorem witnesses_positive : ∀ i h, 0 < witness i h := by
  intro i h
  exact pow_pos (by norm_num : (0 : ℤ) < 257) _

#check witnesses_positive

theorem labels_surjective : Function.Surjective labels := by
  intro epsilon
  let f : Fin 9 → Fin 2 := fun q => finTwoEquiv.symm (epsilon q)
  let i : Fin 512 := finFunctionFinEquiv f
  refine ⟨i, ?_⟩
  funext q
  have h := congrArg (fun g : Fin 9 → Fin 2 => (g q).val)
    (finFunctionFinEquiv.symm_apply_apply f)
  change i.val / 2 ^ q.val % 2 = (f q).val at h
  unfold labels
  rw [h]
  cases he : epsilon q <;> simp [f, he, finTwoEquiv]

#check labels_surjective

def index (block : Fin 32) (offset : Fin 16) : Fin 512 :=
  ⟨block.val * 16 + offset.val, by omega⟩

theorem checked_0 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 0 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 0 s)) q ↔ labels (index 0 s) q = true) := by
  decide +kernel

theorem checked_1 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 1 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 1 s)) q ↔ labels (index 1 s) q = true) := by
  decide +kernel

theorem checked_2 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 2 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 2 s)) q ↔ labels (index 2 s) q = true) := by
  decide +kernel

theorem checked_3 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 3 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 3 s)) q ↔ labels (index 3 s) q = true) := by
  decide +kernel

theorem checked_4 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 4 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 4 s)) q ↔ labels (index 4 s) q = true) := by
  decide +kernel

theorem checked_5 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 5 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 5 s)) q ↔ labels (index 5 s) q = true) := by
  decide +kernel

theorem checked_6 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 6 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 6 s)) q ↔ labels (index 6 s) q = true) := by
  decide +kernel

theorem checked_7 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 7 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 7 s)) q ↔ labels (index 7 s) q = true) := by
  decide +kernel

theorem checked_8 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 8 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 8 s)) q ↔ labels (index 8 s) q = true) := by
  decide +kernel

theorem checked_9 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 9 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 9 s)) q ↔ labels (index 9 s) q = true) := by
  decide +kernel

theorem checked_10 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 10 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 10 s)) q ↔ labels (index 10 s) q = true) := by
  decide +kernel

theorem checked_11 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 11 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 11 s)) q ↔ labels (index 11 s) q = true) := by
  decide +kernel

theorem checked_12 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 12 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 12 s)) q ↔ labels (index 12 s) q = true) := by
  decide +kernel

theorem checked_13 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 13 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 13 s)) q ↔ labels (index 13 s) q = true) := by
  decide +kernel

theorem checked_14 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 14 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 14 s)) q ↔ labels (index 14 s) q = true) := by
  decide +kernel

theorem checked_15 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 15 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 15 s)) q ↔ labels (index 15 s) q = true) := by
  decide +kernel

theorem checked_16 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 16 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 16 s)) q ↔ labels (index 16 s) q = true) := by
  decide +kernel

theorem checked_17 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 17 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 17 s)) q ↔ labels (index 17 s) q = true) := by
  decide +kernel

theorem checked_18 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 18 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 18 s)) q ↔ labels (index 18 s) q = true) := by
  decide +kernel

theorem checked_19 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 19 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 19 s)) q ↔ labels (index 19 s) q = true) := by
  decide +kernel

theorem checked_20 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 20 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 20 s)) q ↔ labels (index 20 s) q = true) := by
  decide +kernel

theorem checked_21 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 21 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 21 s)) q ↔ labels (index 21 s) q = true) := by
  decide +kernel

theorem checked_22 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 22 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 22 s)) q ↔ labels (index 22 s) q = true) := by
  decide +kernel

theorem checked_23 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 23 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 23 s)) q ↔ labels (index 23 s) q = true) := by
  decide +kernel

theorem checked_24 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 24 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 24 s)) q ↔ labels (index 24 s) q = true) := by
  decide +kernel

theorem checked_25 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 25 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 25 s)) q ↔ labels (index 25 s) q = true) := by
  decide +kernel

theorem checked_26 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 26 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 26 s)) q ↔ labels (index 26 s) q = true) := by
  decide +kernel

theorem checked_27 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 27 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 27 s)) q ↔ labels (index 27 s) q = true) := by
  decide +kernel

theorem checked_28 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 28 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 28 s)) q ↔ labels (index 28 s) q = true) := by
  decide +kernel

theorem checked_29 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 29 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 29 s)) q ↔ labels (index 29 s) q = true) := by
  decide +kernel

theorem checked_30 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 30 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 30 s)) q ↔ labels (index 30 s) q = true) := by
  decide +kernel

theorem checked_31 : ∀ s : Fin 16, ∀ q : Fin 9,
    cleared (witness (index 31 s)) q ≠ 0 ∧
    (0 < cleared (witness (index 31 s)) q ↔ labels (index 31 s) q = true) := by
  decide +kernel

theorem cleared_signs : ∀ i q, cleared (witness i) q ≠ 0 ∧
    (0 < cleared (witness i) q ↔ labels i q = true) := by
  have chunks (b : Fin 32) : ∀ s : Fin 16, ∀ q : Fin 9,
      cleared (witness (index b s)) q ≠ 0 ∧
      (0 < cleared (witness (index b s)) q ↔ labels (index b s) q = true) := by
    fin_cases b
    · exact checked_0
    · exact checked_1
    · exact checked_2
    · exact checked_3
    · exact checked_4
    · exact checked_5
    · exact checked_6
    · exact checked_7
    · exact checked_8
    · exact checked_9
    · exact checked_10
    · exact checked_11
    · exact checked_12
    · exact checked_13
    · exact checked_14
    · exact checked_15
    · exact checked_16
    · exact checked_17
    · exact checked_18
    · exact checked_19
    · exact checked_20
    · exact checked_21
    · exact checked_22
    · exact checked_23
    · exact checked_24
    · exact checked_25
    · exact checked_26
    · exact checked_27
    · exact checked_28
    · exact checked_29
    · exact checked_30
    · exact checked_31
  intro i q
  let b : Fin 32 := ⟨i.val / 16, by omega⟩
  let s : Fin 16 := ⟨i.val % 16, by omega⟩
  have hi : index b s = i := by
    apply Fin.ext
    dsimp [index, b, s]
    omega
  simpa only [hi] using chunks b s q

#check cleared_signs

noncomputable def test (x : Fin 4 → ℝ) (q : Fin 9) : ℝ :=
  (residues q 0 : ℝ) / (x 0 + poles q 0) +
  (residues q 1 : ℝ) / (x 1 + poles q 1) +
  (residues q 2 : ℝ) / (x 2 + poles q 2) +
  (residues q 3 : ℝ) / (x 3 + poles q 3) - (thresholds q : ℝ) / scale

theorem test_cleared (x : Fin 4 → ℤ) (q : Fin 9)
    (hx : ∀ h, 0 < x h) :
    test (fun h => (x h : ℝ)) q =
    (cleared x q : ℝ) / ((scale : ℝ) *
      ((x 0 : ℝ) + poles q 0) * ((x 1 : ℝ) + poles q 1) *
      ((x 2 : ℝ) + poles q 2) * ((x 3 : ℝ) + poles q 3)) := by
  have hp (h : Fin 4) : 0 < (x h : ℝ) + poles q h := by
    exact_mod_cast add_pos (hx h) (poles_positive q h)
  have h0 := ne_of_gt (hp 0)
  have h1 := ne_of_gt (hp 1)
  have h2 := ne_of_gt (hp 2)
  have h3 := ne_of_gt (hp 3)
  simp only [test, cleared, Int.cast_sub, Int.cast_mul, Int.cast_add]
  norm_num only [scale, Int.cast_ofNat]
  field_simp

theorem witness_test_signs (i : Fin 512) (q : Fin 9) :
    test (fun h => (witness i h : ℝ)) q ≠ 0 ∧
      (0 < test (fun h => (witness i h : ℝ)) q ↔ labels i q = true) := by
  rw [test_cleared (witness i) q (witnesses_positive i)]
  have hp (h : Fin 4) : 0 < (witness i h : ℝ) + poles q h := by
    exact_mod_cast add_pos (witnesses_positive i h) (poles_positive q h)
  have hk : (0 : ℝ) < scale := by norm_num [scale]
  have hd := mul_pos (mul_pos (mul_pos (mul_pos hk (hp 0)) (hp 1)) (hp 2)) (hp 3)
  constructor
  · exact div_ne_zero (by exact_mod_cast (cleared_signs i q).1) (ne_of_gt hd)
  · rw [div_pos_iff_of_pos_right hd]
    exact (by exact_mod_cast (cleared_signs i q).2)

/-- Nine fixed reciprocal tests on four positive parameters realize every label
vector. In particular a universal bound of twice the number of parameters fails
for this freely chosen query relaxation. -/
theorem nine_tests_shattered : ∀ ε : Fin 9 → Bool,
    ∃ x : Fin 4 → ℝ, (∀ h, 0 < x h) ∧ ∀ q,
      test x q ≠ 0 ∧ (0 < test x q ↔ ε q = true) := by
  intro ε
  obtain ⟨i, hi⟩ := labels_surjective ε
  refine ⟨fun h => (witness i h : ℝ), ?_, ?_⟩
  · intro h
    change (0 : ℝ) < (witness i h : ℝ)
    exact_mod_cast witnesses_positive i h
  · intro q
    simpa only [hi] using witness_test_signs i q

#print axioms nine_tests_shattered

end HeadComplexity.MobiusFourParameterShattering
