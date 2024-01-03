/*

The example for S5 4A

*/
AttachSpec("../DecompAlgs/DecompAlgs.spec");
AttachSpec("../AxialTools/AxialTools.spec");
Attach("../DecompAlgs/AxialTools.m");
Attach("Automorphisms.m");

// Alter this to the path of where your algebra is stored
path := "../DecompAlgs/library/Monster_1,4_1,32/RationalField()/";

// A5 3A2B example in the paper
A := LoadDecompositionAlgebra(path cat "S5/10+15/6A5A4A_1");
F := BaseRing(A);
n := Dimension(A);

G0 := MiyamotoGroup(A);


// Computation 10.19 (a)
jordan_axis := JordanAxes(A);
assert #jordan_axis eq 1;
d := jordan_axis[1];

evals, espaces, FL := IdentifyFusionLaw(d);
assert #FL eq 3; // Jordan type fusion law
S := espaces cat [sub<VectorSpace(A)|>];
Dd := AxialDecomposition(A, S, d);

// Computation 10.19 (b)
axis_reps := AxisOrbitRepresentatives(A);
mults := FindMultiples(axis_reps[1]);
assert #mults eq 2;
assert #FindMultiples(axis_reps[2]) eq 1;
// the orbit of length 10 has multiples and the orbit of length 15 does not.

assert exists(a){ m : m in mults | m ne axis_reps[1]};
evals, espaces, FL := IdentifyFusionLaw(a: eigenvalues:={@1,0,1/4,1/32@});
assert #FL eq 4;
Da := AxialDecomposition(A, espaces, a);

AddDecompositions(~A, [Dd, Da]);
A := MiyamotoClosure(A);

G0 := MiyamotoGroup(A);
assert GroupName(G0) eq "S5";

// Computation 10.19 (a) second part
// The sigma involution of the jordan axes switches the two orbits of twins and fixes the orbit of length 15.

sg := SigmaElement(A, 1);
assert mults[1]*sg eq mults[2];
assert axis_reps[2]*sg eq axis_reps[2];

// Computation 10.19 (c)

// Computation 10.20 (a) & (b)
Dd := Decompositions(A)[1];
FL := FusionLaw(A);
assert Dimension(Part(Dd, FL!1)) eq 1;
assert Dimension(Part(Dd, FL!2)) eq 46;
assert Dimension(Part(Dd, FL!3)) eq 14;

axis_reps := AxisOrbitRepresentatives(A);


