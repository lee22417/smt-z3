# 80bit Floating Point 

## In C
- x86 architecture - long double -> 80 bit floating point
- Sign - 79 bit 
- Exponent - 78 ~ 64 bit
- Integer part - 63 bit 
- Fraction - 62 ~ 0 bit
- example : 
  - 1.0 = 3f ff 80 00 00 00 00 00 00 00 (long double)
  - 1.1 = 3f ff 8c cc cc cc cc cc d0 00 (long double)

## In SMT (Same with Z3)
### Case 1 (Wrong):
- Use As it is in C
  - x = 3F FF 80 00 00 00 00 00 00 00
  - y = 3f ff 8c cc cc cc cc cc d0 00 
- r = x * y (1.0 * 1.1)
- Code
```
(set-logic QF_FP)

(declare-const x (_ FloatingPoint 15 65))
(declare-const y (_ FloatingPoint 15 65))
(declare-const r (_ FloatingPoint 15 65))

(assert (and 
    (= x (fp #b0 #b011111111111111 #b1000000000000000000000000000000000000000000000000000000000000000))
    (= y (fp #b0 #b011111111111111 #b1000110011001100110011001100110011001100110011001101000000000000))
    (= r (fp.mul roundTowardZero x y))
))

(check-sat)
(get-value (x y r))
```
- Result
```
r = 40 00 29 99 99 99 99 99 9c 00
  = which is different from 1.1 in C
```

### Case 2 (Correct):
- Implicit integer significand bit
- SMT-LIB floating point theory only being able to represent IEEE 754 classes
- Create FP 79bit
- Remove Integer Part (63bit, the first bit in fraction)
  - x = 3F FF | 00 00 00 00 00 00 00 00
  - y = 3f ff | 0c cc cc cc cc cc d0 00
- r = x * y (1.0 * 1.1)
- Code
```
(set-logic QF_FP)

(declare-const x (_ FloatingPoint 15 64))
(declare-const y (_ FloatingPoint 15 64))
(declare-const r (_ FloatingPoint 15 64))

(assert (and 
    (= x (fp #b0 #b011111111111111 #b000000000000000000000000000000000000000000000000000000000000000))
    (= y (fp #b0 #b011111111111111 #b000110011001100110011001100110011001100110011001101000000000000))
    (= r (fp.sub roundTowardZero x y))
))

(check-sat)
(get-value (x y r))
```
- Result
```
r = #b0 #b011111111111111 #b110100010111010001011101000101110100010111010001011010011100100
  = 3f ff 0c cc cc cc cc cc d0 00
r add Integer Part (1 in front of fraction)
  = 3f ff 8c cc cc cc cc cc d0 00
  = which is the same as 1.1 in C
```

# Reference
https://srg.doc.ic.ac.uk/files/papers/klee-n-version-fp-ase-17.pdf
