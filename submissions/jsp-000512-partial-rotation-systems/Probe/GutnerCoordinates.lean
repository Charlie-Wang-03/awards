import Probe.GutnerGraph
import Probe.StraightLineCertificate
import Mathlib.Data.Fin.VecNotation

namespace JSP512Probe.Gutner
open StraightLine
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def edgeTable : Fin 21 → Fin 9 × Fin 9 :=
  ![(0,1), (0,2), (1,2), (0,3), (2,3), (0,4), (1,4), (1,5), (2,5), (3,4), (4,5), (3,5), (0,6), (2,6), (0,7), (1,7), (1,8), (2,8), (6,7), (7,8), (6,8)]

theorem edgeTable_complete : ∀ a b, (a,b) ∈ blockEdges →
    ∃ k : Fin 21, edgeTable k = (a,b) := by decide +kernel

def edge (i : Fin 12) (k : Fin 21) : Fin 86 × Fin 86 :=
  (vertex i (edgeTable k).1,vertex i (edgeTable k).2)

/-- Integer coordinates independently checked below; no external checker is trusted. -/
def position : Fin 86 → ℤ × ℤ :=
  ![(148,447),
    (16000000116,700000769),
    (8300000880,1100000969),
    (8300000204,1000000659),
    (8200000378,800000176),
    (8400000167,900000023),
    (8100000612,1200000560),
    (8200000655,1400000600),
    (8200000596,1300000659),
    (8300000215,1800000330),
    (8300000252,1700000953),
    (8200000132,1500000348),
    (8400000139,1600000954),
    (8100000640,1900000800),
    (8200000257,2100000641),
    (8200000137,2000000411),
    (8300000481,2500000597),
    (8300000049,2400000776),
    (8200000927,2200000123),
    (8400000714,2300000132),
    (8100000285,2600000651),
    (8200000615,2800000931),
    (8200000666,2700000036),
    (8300000578,3200000560),
    (8300000665,3100000420),
    (8200000497,2900000081),
    (8400000708,3000000048),
    (8100000911,3300000103),
    (8200000503,3500000607),
    (8200000361,3400000933),
    (8300000690,3900000494),
    (8300000938,3800000161),
    (8200000606,3600000912),
    (8400000298,3700000828),
    (8100000267,4000000719),
    (8200000286,4200000871),
    (8200000393,4100000582),
    (8300000721,4600000430),
    (8300000501,4500000355),
    (8200000536,4300000470),
    (8400000220,4400000877),
    (8100000612,4700000367),
    (8200000153,4900000927),
    (8200000693,4800000637),
    (8300000924,5300000081),
    (8300000702,5200000443),
    (8200000291,5000000930),
    (8400000136,5100000836),
    (8100000704,5400000059),
    (8200000768,5600000619),
    (8200000874,5500000018),
    (8300000483,6000000804),
    (8300000895,5900000354),
    (8200000132,5700000096),
    (8400000261,5800000541),
    (8100000700,6100000732),
    (8200000010,6300000009),
    (8200000785,6200000550),
    (8300000152,6700000648),
    (8300000901,6600000238),
    (8200000976,6400000067),
    (8400000302,6500000939),
    (8100000729,6800000354),
    (8200000324,7000000562),
    (8200000227,6900000701),
    (8300000373,7400000357),
    (8300000627,7300000160),
    (8200000552,7100000655),
    (8400000604,7200000413),
    (8100000916,7500000867),
    (8200000971,7700000152),
    (8200000411,7600000242),
    (8300000494,8100000097),
    (8300000629,8000000016),
    (8200000687,7800000241),
    (8400000358,7900000283),
    (8400000043,8300000615),
    (8400000217,8400000314),
    (8500000300,8200000966),
    (16200000828,200000111),
    (16400000231,100000565),
    (16800000956,480),
    (16300000051,300000473),
    (15800000943,300000118),
    (15900000231,500000165),
    (16000000879,400000804)]

theorem position_injective : Function.Injective position := by decide +kernel

def VertexCheck (i : Fin 12) : Prop := ∀ k : Fin 21, ∀ v : Fin 86,
  v ≠ (edge i k).1 → v ≠ (edge i k).2 →
    orient (position (edge i k).1) (position (edge i k).2) (position v) ≠ 0

def PairCheck (i : Fin 12) : Prop := ∀ k : Fin 21, ∀ j : Fin 12, ∀ l : Fin 21,
  edge i k ≠ edge j l → edge i k ≠ ((edge j l).2,(edge j l).1) →
    Separated (position (edge i k).1) (position (edge i k).2)
      (position (edge j l).1) (position (edge j l).2)

theorem vertex_check_0 : VertexCheck 0 := by unfold VertexCheck; decide +kernel
theorem vertex_check_1 : VertexCheck 1 := by unfold VertexCheck; decide +kernel
theorem vertex_check_2 : VertexCheck 2 := by unfold VertexCheck; decide +kernel
theorem vertex_check_3 : VertexCheck 3 := by unfold VertexCheck; decide +kernel
theorem vertex_check_4 : VertexCheck 4 := by unfold VertexCheck; decide +kernel
theorem vertex_check_5 : VertexCheck 5 := by unfold VertexCheck; decide +kernel
theorem vertex_check_6 : VertexCheck 6 := by unfold VertexCheck; decide +kernel
theorem vertex_check_7 : VertexCheck 7 := by unfold VertexCheck; decide +kernel
theorem vertex_check_8 : VertexCheck 8 := by unfold VertexCheck; decide +kernel
theorem vertex_check_9 : VertexCheck 9 := by unfold VertexCheck; decide +kernel
theorem vertex_check_10 : VertexCheck 10 := by unfold VertexCheck; decide +kernel
theorem vertex_check_11 : VertexCheck 11 := by unfold VertexCheck; decide +kernel
theorem pair_check_0 : PairCheck 0 := by unfold PairCheck; decide +kernel
theorem pair_check_1 : PairCheck 1 := by unfold PairCheck; decide +kernel
theorem pair_check_2 : PairCheck 2 := by unfold PairCheck; decide +kernel
theorem pair_check_3 : PairCheck 3 := by unfold PairCheck; decide +kernel
theorem pair_check_4 : PairCheck 4 := by unfold PairCheck; decide +kernel
theorem pair_check_5 : PairCheck 5 := by unfold PairCheck; decide +kernel
theorem pair_check_6 : PairCheck 6 := by unfold PairCheck; decide +kernel
theorem pair_check_7 : PairCheck 7 := by unfold PairCheck; decide +kernel
theorem pair_check_8 : PairCheck 8 := by unfold PairCheck; decide +kernel
theorem pair_check_9 : PairCheck 9 := by unfold PairCheck; decide +kernel
theorem pair_check_10 : PairCheck 10 := by unfold PairCheck; decide +kernel
theorem pair_check_11 : PairCheck 11 := by unfold PairCheck; decide +kernel

theorem vertex_checks (i : Fin 12) : VertexCheck i := by
  fin_cases i
  · exact vertex_check_0
  · exact vertex_check_1
  · exact vertex_check_2
  · exact vertex_check_3
  · exact vertex_check_4
  · exact vertex_check_5
  · exact vertex_check_6
  · exact vertex_check_7
  · exact vertex_check_8
  · exact vertex_check_9
  · exact vertex_check_10
  · exact vertex_check_11

theorem pair_checks (i : Fin 12) : PairCheck i := by
  fin_cases i
  · exact pair_check_0
  · exact pair_check_1
  · exact pair_check_2
  · exact pair_check_3
  · exact pair_check_4
  · exact pair_check_5
  · exact pair_check_6
  · exact pair_check_7
  · exact pair_check_8
  · exact pair_check_9
  · exact pair_check_10
  · exact pair_check_11

end JSP512Probe.Gutner
