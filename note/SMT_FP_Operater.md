# Floating Point Comparison Operator

### SMT LIB
- gt `>`
  - Terminal -> Command `z3 -smt2 -in`
  - Code
```
(set-logic QF_FP)

(declare-const x (_ FloatingPoint 15 65))
(declare-const y (_ FloatingPoint 15 65))
(declare-const r (_ FloatingPoint 15 65))
(declare-const p Bool)

(assert (and 
    (= x (fp #b1 #b011111111111111 #x8cccccccccccd000))
    (= y (fp #b0 #b000000000000000 #x0000000000000000))
    (= p (fp.gt x y))
))

(check-sat)
(get-value (x y p))

```
-Result
```
sat
((x (fp #b0 #b011111111111111 #x0000000000000000000000000000))
 (y (fp #b0 #b011111111111111 #x199999999999a000000000000000))
 (r (fp #b0 #b100000000000000 #x0cccccccccccd000000000000000)))
```


# Reference
- http://smtlib.cs.uiowa.edu/theories-FloatingPoint.shtml
