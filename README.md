# A Coq Formalization of Axiomatic Real Numbers
This repository presents a Coq formalization of the axiomatic definition of real numbers based on the formalization of [Morse-Kelley](https://github.com/1DGW/formalization-of-Morse-Kelley-axiomatic-set-theory) (MK) set theory.

# Files
The formalization consists of 4 \(.v\)files (sorted by file dependency):

* mk_structure.v  --  the formalization of all the definitions and axioms of MK.

* mk_theorems.v  --  the formalization and verification of all the theorems in MK.

* reals_axioms.v  --  the formalization of the axiomatic definition of reals.

* reals_uniqueness.v -- the formalization of the uniqueness of reals.

The MK part (mk_structure.v & mk_theorems.v) is guided by the appendix in Kelley’s *General Topology* publishe in 1955,
where the entire axioms, definitions and theorems of Morse-Kelley \(MK\) axiomatic set theory were introduced.

The reals part (reals_axioms.v & reals_uniqueness.v) is guided by the 2nd chapter of Zorich's *Mathematical Analysis* (Part I, 7th expanded edition),
where 'reals_axioms.v' presents the formalization of the axiomatic definition of real numbers and verifies their key algebraic properties;
'reals_uniqueness.v' presents the formalization of the uniqueness of real numbers, namely, any two algebraic structures that satisfy all the axioms of real numbers are isomorphic.

# Authors
This project is implemented by Wensheng Yu<wsyu@bupt.edu.cn>, Dakai Guo, Si Chen, Guowei Dou<dgw@bupt.edu.cn> and Shukun Len.

Beijing Key Laboratory of Space-ground Interconnection and Convergence, School of Electronic Engineering, Beijing University of Posts and Telecommunications, Beijing

# Relevant Papers
\[1\] Guo, D., Len, S., Dou, G., Chen, S., Yu, W.: Formalization in Coq of the consistency and categoricity of the real number axiomatic system based on Morse-Kelley set theory. Control Theory & Applications. 41(7),1274-1285 (2024)
