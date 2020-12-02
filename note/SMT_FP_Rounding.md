

# SMT LIB - Floating Point Rounding
- Roundings
  - roundTowardZero
  - roundTowardPositive
  - roundTowardNegative
  - roundNearestTiesToEven
  - roundNearestTiesToAway
 
  
- Code Example
  - x = 1.0, y = 1.1
```
(set-logic QF_FP)

(declare-const x (_ FloatingPoint 15 113))
(declare-const y (_ FloatingPoint 15 113))
(declare-const r (_ FloatingPoint 15 113))

(assert (and 
    (= x (fp #b0 #b011111111111111 #x0000000000000000000000000000 ))
    (= y (fp #b0 #b011111111111111 #x199999999999A000000000000000))
    (= r (fp.div roundTowardZero x y))
))

(check-sat)
(get-value (x y r))
```

- Result Example
```
C    -> 3f fe d1 74 5d 17 45 d1 69 c8 fd e2 61 52 83 6a (= 1.0/1.1)
SMT  -> 3f fe d1 74 5d 17 45 d1 69 c8 fd e2 61 52 83 69 (roundTowardZero)
        3f fe d1 74 5d 17 45 d1 69 c8 fd e2 61 52 83 6a (roundTowardPositive)
        3f fe d1 74 5d 17 45 d1 69 c8 fd e2 61 52 83 69 (roundTowardNegative)
        3f fe d1 74 5d 17 45 d1 69 c8 fd e2 61 52 83 6a (roundNearestTiesToEven)
        3f fe d1 74 5d 17 45 d1 69 c8 fd e2 61 52 83 6a (roundNearestTiesToAway)
```
