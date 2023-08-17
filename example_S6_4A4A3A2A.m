/*

The example for S6 15+45 axes 4A4A3A2A

*/
AttachSpec("../DecompAlgs/DecompAlgs.spec");
AttachSpec("../AxialTools/AxialTools.spec");
Attach("../DecompAlgs/AxialTools.m");
Attach("Automorphisms.m");

types := ["2A","2B","3A","3C","4A","4B","5A","6A"];
IdentityLength := AssociativeArray([* <"2A", (2^2*3)/5>,
                                      <"2B", 2>,
                                      <"3A", (2^2*29)/(5*7)>,
                                      <"3C", (2^5/11)>,
                                      <"4A", 4>,
                                      <"4B", 19/5>,
                                      <"5A", (2^5)/7>,
                                      <"6A", (3*17)/(2*5)> *]);
                                      
path := "../DecompAlgs/library/Monster_1,4_1,32/RationalField()/";

// S6 15+45 4A4A3A2A example in the paper
A := LoadDecompositionAlgebra(path cat "S6/15+45/6A5A4A4A3A2A_1");
F := BaseRing(A);
n := Dimension(A);

// Computation (a)
Jaxes := JordanAxes(A);
assert #Jaxes := 1;






