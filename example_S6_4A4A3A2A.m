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
G0 := MiyamotoGroup(A);
axes := Axes(A);

axis_reps := AxisOrbitRepresentatives(A: Miyamoto_closed := true);
o15 := {@ axis_reps[1]*g : g in G @};
o45 := {@ axis_reps[2]*g : g in G @};

assert #o45 eq 45;
B := Subalgebra(A, o45);
assert Dimension(B) eq 121;

// Computation (a)
time Jaxes := JordanAxes(A);
assert #Jaxes eq 1;

d := Jaxes[1];
sg_d := MiyamotoInvolution(d, 1/4: check_fusion:=false);

// Computation (b)
o15_twins := {@ a*sg_d : a in o15 @};
assert o15_twins ne o15;

// Computation (c)
// ???

// Computation (d)
no_twins := FindMultiples(o45[1]);
assert #no_twins eq 1 and no_twins[1] eq o45[1];

// Computation (e)
// ???

// Computation (f)
S :=SylowSubgroup(G0, 2);
E := ElementaryAbelianSubgroups(S: OrderEqual:=8)[1]`subgroup;
CG := CharacterGroup(A);
Y := {@ axes[i] : i in [1..#axes] | MiyamotoElement(A,i, CG.1) in E@};
YD := {@ Decomposition(a) : a in Y@};

joint := JointPartDecomposition(YD);


