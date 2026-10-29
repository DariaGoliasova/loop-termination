Requirements:
Python 3.14
z3-solver
numpy
scipy

To test the program call 
python witness_runner.py
from the directory and input the constraints.

The find_witnesses(A, b) function returns a dictionary with data about found witnesses.
Dictionary fields:
"bounded": tells if the polytop formed by constraints bounded
"not_empty": tells if the polytop formed by constraints empty
"point": tells if the point witness exist and if yes, provides it and orbit that it forms
"ray": tells if the ray witness exist and if yes, provides it and orbit that it forms
"line": tells if the line witness exist and if yes, provides it and orbit that it forms
"cone": tells if the cone witness exist and if yes, provides it and orbit that it forms
"half_plane": tells if the half_plane witness exist and if yes, provides it and orbit that it forms
