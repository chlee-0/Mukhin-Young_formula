# Mukhin-Young_formula

This is a Mathematica script to verify the Mukhin-Young formula for normalized characters of Kirillov-Reshetikhin modules in some cases.

## Usage
Put the following two files in the same directory :
- `KR_hvector_EFG.dat` : data for h-vectors in type E6,E7,E8,F4,G2 (necessary to define the KR quasipolynomials)
- `KR_quasipolynomial.m` : sample mathematica script to check some properties of the KR quasipolynomials

To run the sample script (assuming that the Mathematica kernel is on your path):
for type F4
```
$ math -script Mukhin-Young_formula_F4.m
```

for type E8
```
$ math -script Mukhin-Young_formula_E8.m
```
