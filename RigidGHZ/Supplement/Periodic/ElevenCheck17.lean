module

public import RigidGHZ.Supplement.Periodic.ElevenCheck16

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem node_544 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 23, 19}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 23, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 23, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 23, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 23, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 23, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 23, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 23, 19} Certificate (by decide)
  decide

theorem node_545 :
    (scheme.enumerateFrom [24, 25, 26, 27, 28, 29, 30, 31, 32] {23, 19}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {23, 19} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {23, 19} Certificate (by decide)
    ?_ node_544
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {23, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {23, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {23, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {23, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {23, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {23, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {23, 19} Certificate (by decide)
  decide

theorem node_546 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 25, 24, 19}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 25, 24, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 25, 24, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 25, 24, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 25, 24, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 25, 24, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 25, 24, 19} Certificate (by decide)
  decide

theorem node_547 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 24, 19}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {25, 24, 19} Certificate (by decide)
    ?_ node_546
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 24, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 24, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 24, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 24, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 24, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 24, 19} Certificate (by decide)
  decide

theorem node_548 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 24, 19}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 24, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 24, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 24, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 24, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 24, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 24, 19} Certificate (by decide)
  decide

theorem node_549 :
    (scheme.enumerateFrom [25, 26, 27, 28, 29, 30, 31, 32] {24, 19}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {24, 19} Certificate (by decide)
    ?_ node_547
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {24, 19} Certificate (by decide)
    ?_ node_548
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {24, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {24, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {24, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {24, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {24, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {24, 19} Certificate (by decide)
  decide

theorem node_550 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 25, 19}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 25, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 25, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 25, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 25, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 25, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 25, 19} Certificate (by decide)
  decide

theorem node_551 :
    (scheme.enumerateFrom [31, 32] {30, 25, 19}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 25, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 25, 19} Certificate (by decide)
  decide

theorem node_552 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 19}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {25, 19} Certificate (by decide)
    ?_ node_550
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 19} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {25, 19} Certificate (by decide)
    ?_ node_551
  apply scheme.check_enumeration_skip 31 [32] {25, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 19} Certificate (by decide)
  decide

theorem node_553 :
    (scheme.enumerateFrom [29, 30, 31, 32] {28, 26, 19}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {28, 26, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {28, 26, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {28, 26, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {28, 26, 19} Certificate (by decide)
  decide

theorem node_554 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 19}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 19} Certificate (by decide)
  apply scheme.check_enumeration_split 28 [29, 30, 31, 32] {26, 19} Certificate (by decide)
    ?_ node_553
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 19} Certificate (by decide)
  decide

theorem node_555 :
    (scheme.enumerateFrom [31, 32] {30, 28, 19}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 28, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 28, 19} Certificate (by decide)
  decide

theorem node_556 :
    (scheme.enumerateFrom [29, 30, 31, 32] {28, 19}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {28, 19} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {28, 19} Certificate (by decide)
    ?_ node_555
  apply scheme.check_enumeration_skip 31 [32] {28, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {28, 19} Certificate (by decide)
  decide

theorem node_557 :
    (scheme.enumerateFrom [31, 32] {30, 19}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 19} Certificate (by decide)
  decide

theorem node_558 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19} Certificate (by decide)
    ?_ node_543
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19} Certificate (by decide)
  apply scheme.check_enumeration_split 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19} Certificate (by decide)
    ?_ node_545
  apply scheme.check_enumeration_split 24 [25, 26, 27, 28, 29, 30, 31, 32] {19} Certificate (by decide)
    ?_ node_549
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {19} Certificate (by decide)
    ?_ node_552
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {19} Certificate (by decide)
    ?_ node_554
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19} Certificate (by decide)
  apply scheme.check_enumeration_split 28 [29, 30, 31, 32] {19} Certificate (by decide)
    ?_ node_556
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {19} Certificate (by decide)
    ?_ node_557
  apply scheme.check_enumeration_skip 31 [32] {19} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19} Certificate (by decide)
  decide

theorem node_559 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 21, 20}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 21, 20} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 21, 20} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 21, 20} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 21, 20} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 21, 20} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 21, 20} Certificate (by decide)
  decide

theorem node_560 :
    (scheme.enumerateFrom [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 20}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 20} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 20} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {21, 20} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {21, 20} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {21, 20} Certificate (by decide)
    ?_ node_559
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {21, 20} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {21, 20} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {21, 20} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {21, 20} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {21, 20} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {21, 20} Certificate (by decide)
  decide

theorem node_561 :
    (scheme.enumerateFrom [30, 31, 32] {29, 26, 20}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 26, 20} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 26, 20} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 26, 20} Certificate (by decide)
  decide

theorem node_562 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 20}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 20} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 20} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {26, 20} Certificate (by decide)
    ?_ node_561
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 20} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 20} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 20} Certificate (by decide)
  decide

theorem node_563 :
    (scheme.enumerateFrom [30, 31, 32] {29, 27, 20}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 27, 20} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 27, 20} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 27, 20} Certificate (by decide)
  decide

theorem node_564 :
    (scheme.enumerateFrom [28, 29, 30, 31, 32] {27, 20}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {27, 20} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {27, 20} Certificate (by decide)
    ?_ node_563
  apply scheme.check_enumeration_skip 30 [31, 32] {27, 20} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {27, 20} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {27, 20} Certificate (by decide)
  decide

theorem node_565 :
    (scheme.enumerateFrom [] {32, 29, 20}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_566 :
    (scheme.enumerateFrom [30, 31, 32] {29, 20}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 20} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 20} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {29, 20} Certificate (by decide)
    ?_ node_565
  decide

theorem node_567 :
    (scheme.enumerateFrom [] {32, 30, 20}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_568 :
    (scheme.enumerateFrom [31, 32] {30, 20}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 20} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {30, 20} Certificate (by decide)
    ?_ node_567
  decide

theorem node_569 :
    (scheme.enumerateFrom [] {32, 20}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_570 :
    (scheme.enumerateFrom [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20} Certificate (by decide)
    ?_ node_560
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {20} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {20} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {20} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {20} Certificate (by decide)
    ?_ node_562
  apply scheme.check_enumeration_split 27 [28, 29, 30, 31, 32] {20} Certificate (by decide)
    ?_ node_564
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {20} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {20} Certificate (by decide)
    ?_ node_566
  apply scheme.check_enumeration_split 30 [31, 32] {20} Certificate (by decide)
    ?_ node_568
  apply scheme.check_enumeration_skip 31 [32] {20} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {20} Certificate (by decide)
    ?_ node_569
  decide

theorem node_571 :
    (scheme.enumerateFrom [24, 25, 26, 27, 28, 29, 30, 31, 32] {23, 22, 21}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {23, 22, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {23, 22, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {23, 22, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {23, 22, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {23, 22, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {23, 22, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {23, 22, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {23, 22, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {23, 22, 21} Certificate (by decide)
  decide

theorem node_572 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 22, 21}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 22, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 22, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 22, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 22, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 22, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 22, 21} Certificate (by decide)
  decide

theorem node_573 :
    (scheme.enumerateFrom [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 21}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 21} Certificate (by decide)
    ?_ node_571
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {22, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {22, 21} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {22, 21} Certificate (by decide)
    ?_ node_572
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {22, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {22, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {22, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {22, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {22, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {22, 21} Certificate (by decide)
  decide

theorem node_574 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 23, 21}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 23, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 23, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 23, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 23, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 23, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 23, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 23, 21} Certificate (by decide)
  decide

theorem node_575 :
    (scheme.enumerateFrom [24, 25, 26, 27, 28, 29, 30, 31, 32] {23, 21}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {23, 21} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {23, 21} Certificate (by decide)
    ?_ node_574
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {23, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {23, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {23, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {23, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {23, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {23, 21} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {23, 21} Certificate (by decide)
  decide

end RigidGHZ.Supplement.Periodic.Eleven
