/*

The example for A_6 5A5A4A3A3A

*/
/*
AttachSpec("DecompAlgs.spec");
AttachSpec("/home/tendai/AxialTools/AxialTools.spec");
Attach("AxialTools.m");
Attach("/home/tendai/Downloads/Automorphisms.m");
*/

AttachSpec("../DecompAlgs/DecompAlgs.spec");
AttachSpec("../AxialTools/AxialTools.spec");
Attach("../DecompAlgs/AxialTools.m");
Attach("Automorphisms.m");

// Alter this to the path of where your algebra is stored

path := "../DecompAlgs/library/Monster_1,4_1,32/RationalField()/";


/*Preliminary data.*/
A := LoadDecompositionAlgebra(path cat "A6/45/5A5A4A3A3A_sub.json");
F := BaseRing(A);
n := Dimension(A);
G0 := MiyamotoGroup(A);
assert GroupName(G0) eq "A6";

// If the algebra is Miyamoto closed, then the Miyamoto group is a permutation group on the axes
axes := Axes(A);
assert forall{ <i, g> : i in [1..#axes], g in Generators(G0) | axes[i]*g eq axes[Image(g,GSet(G0),i)]};

// Computation 13.1 (a) We show that A has no Jordan axes.
assert #JordanAxes(A) eq 0;

// Computation 13.1 (b) The known axes have no twins.
assert #axes eq 45;
axes_reps := AxisOrbitRepresentatives(A);
assert #axes_reps eq 1;
assert #(FindMultiples(axes_reps[1])) eq 1;


Miy_elts := [MiyamotoElement(A, i): i in [1..#axes]];
// Since there are no twins for this set of axes, there is a bijection between the axes and the Miyamoto involutions. Thus, we can find the action of the outer automorphism via its action on the Miyamoto involutions.

// Computation 13.1 (d) We show that the outer automorphisms of G0 induce algebra automorphisms.

aut := AutomorphismGroup(G0);
assert GroupName(OuterFPGroup(aut)) eq "C2^2";
// Thus the outer automorphism has 2 generators. The first gives S_6, while adding the second gives the full automorphism.

outs := {@ x: x in Generators(aut)| not IsInnerAutomorphism(x) @};
assert #outs eq 2;
outs := [ Sym(#axes)![ Position(Miy_elts, Miy_elts[i]@outs[j]) : i in [1..#axes]] : j in [1,2]];
// Thus it is clear that Aut(G0) is A6.C2^2

// We check that each out is indeed an automorphism of A. 
Vaxes := sub<VectorSpace(A) | [Vector(x) : x in axes]>;
out_maps := [ hom<Vaxes->VectorSpace(A) | [<Vector(axes[i]), Vector(axes[i^outs[j]])> : i in [1..45]]>: j in [1..2]];
time out_maps := [out_map where bool, out_map := ExtendMapToAlgebraAutomorphism(A, out_maps[i]): i in [1..2]];
//assert bool;
assert forall{out_map : out_map in out_maps | IsAutomorphism(A, out_map: generators:=axes)};
assert #out_maps eq 2;
// Both outer automorphisms do indeed induce algebra automorphims.
bool := exists(o){out: out in outs|IsIsomorphic(PermutationGroup<45|G0, out>, Sym(6)) };
assert bool;
G := PermutationGroup<45| G0, o>;
//assert GroupName(G) eq "S6"; Now not necessary by construction of G.

// Computation 13.1 (c) We will show that the involutions from G=S_6 are not induced by axes. We could actually combine this with Computation 13.2. 
// We seek the involutions of G outside G0
invs_G := [x[3] : x in ConjugacyClasses(G)| x[1] eq 2];
assert #invs_G eq 3;
invs_G_diff_G0 := [g :g in invs_G| g notin G0];
assert #invs_G_diff_G0 eq 2;
Vaxes_gs := [hom<Vaxes -> VectorSpace(A)|[< Vector(axes[i]), Vector(axes[i^g])>: i in [1.. #axes]]>: g in invs_G_diff_G0];
outer_gmaps := [phi where bool, phi := ExtendMapToAlgebraAutomorphism(A, Vaxes_gs[i]): i in [1,2]];
assert forall{func: func in outer_gmaps| Type(func) eq Map};
// Therefore both extend.

assert forall{func: func in outer_gmaps|not IsInducedFromAxis(A, func) };
// Hence the two classes of involutions in G\G0 are not induced by axes.

// Computation 13.2
// We will call the group G^\circ in the paper G_c
G_c := PermutationGroup<45| G, [x: x in outs| x ne o][1]>;
assert GroupName(G_c) eq "S6.C2";

// We want involutions in G_c\ G.
invs_Gc := [x : x in ConjugacyClasses(G_c)| x[1] eq 2];
invs_Gc_diff_G := [x: x in invs_Gc| x[3] notin G];
assert #invs_Gc_diff_G eq 1 and (invs_Gc_diff_G)[1][2] eq 36;
// Thus there is a single class of involutions in G_c\ G of size 36

g := invs_Gc_diff_G[1][3];
Vaxes_g := hom<Vaxes -> VectorSpace(A)|[< Vector(axes[i]), Vector(axes[i^g])>: i in [1.. #axes]]>;
bool, g_map := ExtendMapToAlgebraAutomorphism(A, Vaxes_g);
assert bool;
assert not IsInducedFromAxis(A, g_map);
// Hence the involutions in G_c\G are not induced by axes. 

// We now set up a decomposition with respect to a set of axes generating 2B algebras pairwise and whose tau involutions generate an elementary abelian group 2^2.
a := axes[1];
Y := {@ a @};
possibles := [x : x in axes | x*a eq A!0 ];

so := true;
while so do
  so := exists(b){b : b in possibles | forall{y : y in Y | IsZero(y*b)}};
  if so then
    Include(~Y, b);
  end if;
end while;

assert #Y eq 3;
b := Y[2];
c := Y[3];

assert Dimension(Subalgebra(A, Y)) eq 3;
E := sub<G_c | [MiyamotoElement(A, Position(axes, y)) : y in Y]>;
assert GroupName(E) eq "C2^2";
N := Normaliser(G_c, E);
assert GroupName(N) eq "C2*S4";


// Computation 13.3 Details of the decomposition. Here a_1=a, a_2=b and a_3=c.
YD := {@ Decomposition(x): x in Y @};
decomp := JointPartDecomposition(YD);
/*note here that the keys of the decomposition are indexed by the tuples <i,j,k> where
  1\le i,j,k\le 4 with 1:->1,0:->2, 1/4:->3 and 1/32:->4.*/

//Part (a) U_{(0,0,0)}(Y) is indexed by <2,2,2>;

U :=decomp[<2, 2, 2>];
assert Dimension(U) eq 19;

//Part (b) The rest of the componets are as follows:

// Part (b) (i) U_{(1,0,0)}(Y)=<a>, U_{(0,1,0)}(Y)=<b> and U_{(0,0,1)(Y)=<c>
// by the map above, these will be indexed <1,2,2>, <2,1,2> and <2,2,1> respectively.

assert forall{x:x in [<1, 2, 2>, <2, 1, 2>, <2, 2, 1>] |Dimension(decomp[x]) eq 1};

/* Part (b) (ii) U_{(0,1/4,1/4)}(Y), U{(1/4,0,1/4)}(Y) and U_{(1/4,1/4,0)}(Y). These are indexed by
   <2,3,3>, <3,2,3> and <3,3,2>, respectively.*/
assert forall{x:x in [<2, 3, 3>, <3, 2, 3>, <3, 3, 2>]|Dimension(decomp[x]) eq 2};

/* Part (b) (iii) U_{(1/4,0,0)}(Y), U{(0,1/4,0)}(Y) and U_{(0,0, 1/4)}(Y). These are indexed by
   <3,2,2>, <2,3,2> and <2,2,3>, respectively.*/
assert forall{x:x in [<3, 2, 2>, <2, 3, 2> ,<2, 2, 3>]|Dimension(decomp[x]) eq 5};

/*Part (b) (iv) U_{(1/4,1/32,1/32)}(Y),U_{(1/32,1/4,1/32)}(Y) and U_{(1/32,1/32,1/4)(Y),
  which are indexed by <3,4,4>,<4,3,4> and <4,4,3>, respectively.*/
assert forall{x:x in [<3, 4, 4>,<4, 3, 4>, <4, 4, 3>]|Dimension(decomp[x]) eq 6};

/*Part (b) (v) U_{(0,1/32,1/32)}(Y),U_{(1/32,0,1/32)}(Y) and U_{(1/32,1/32,0)(Y),
  which are indexed by <2,4,4>,<4,2,4> and <4,4,2>, respectively.*/

assert forall{x:x in  [<2, 4, 4>,<4, 2, 4>, <4, 4, 2>]|Dimension(decomp[x]) eq 20};

/* We turn to determining Aut(U).*/


UAlg, U_inc :=Subalgebra(A,Basis(U));

// Computation 13.4

Ws := [ decomp[x]: x in [<2, 3, 3>, <3, 2, 3>, <3, 3, 2>]];
bool, proj := HasProjection( A, U);
assert bool;
Us := [sub< U|[ Vector((A!bas[i])*(A!bas[j]))@proj where bas is Basis(Ws[k]): i,j in [1..Dimension(Ws[1])]|i le j]>: k in [1..#Ws]];

Us := [Subalgebra(UAlg, [ UAlg!(Algebra(A)!(Vector((A!bas[i])*(A!bas[j]))@proj)) where bas is Basis(Ws[k]): i,j in [1..Dimension(Ws[1])]|i le j]): k in [1..#Ws]];
assert forall{U_i: U_i in Us| Dimension(U_i) eq 3};
z_is :=[ UAlg!z where bool, z := HasOne(U_i): U_i in Us];
assert forall{z: z in z_is| Frobenius(x,x) eq 4 where x is A!(Algebra(A)!z)};
// Length of each identity element of U_i is 4.
assert forall{i:i in [1..3]| z_is[i] in Us[i]};
// so that z_i := z_is[i]

// Computation 13.5 We show that the z_is are precisely the only idempotents of length 4 in U. This is the longest computation in all the project, and requires a lot of memory (a cluster), and will take as long as a week.

length_four_idemps_U := FindAllIdempotents(A, U: length := 4, extend_field := true );

assert forall{z: z in z_is| A!(Algebra(A)!z) in length_for_idemps_U};
assert #length_four_idemps_U eq 3;
// So that the z_is are everything.


// Computation 13.6 (a) The subalgebra generated by the z_is is 4-dimensional.

V := Subalgebra(UAlg, z_is);
assert Dimension(V) eq 4;

// Computation 13.6 (b) The 1-eigenspaces of the z_is are 2-dim
V_1zs := [Eigenspace(V!z_is[i], 1): i in [1..3]];
assert forall{ V_1z: V_1z in V_1zs | Dimension(V_1z) eq 2};


// Computation 13.6 (c) Each V_1z contains the corresponding z_i, a common idempotent u of length 2, a unique idempotent u_i of length 2, and 0.

// First wee need to lift the V_1zs to A.
AA := Algebra(A);
V1_zs_long := [ sub<U| [ Vector(AA!(UAlg!(V!(V!V_1zs[i].j)))): j in [1..2]]>: i in [1..3]];
idemps_Vis := [ idemps where idemps is FindAllIdempotents(A, V1_zs_long[i] : extend_field := true):i in  [1..3]];
assert forall{idemps: idemps in idemps_Vis|{* Frobenius(x, x): x in idemps *} eq {* 0, 2^^2, 4 *}};
// So each set of idempotents has idempotents of length 0, 2 (twice) and 4, i.e., 4 idempotents.

assert forall{ i: i in [1.. #idemps_Vis]| A!(AA!z_is[i]) in idemps_Vis[i]};
// Hence each z_i is in V_1(z_i), i := 1, 2, 3. 
common := &meet[x:x in idemps_Vis];
assert #common eq 2;
assert { Frobenius(x, x):x in common } eq {0, 2};
// Hence the sets have two common idempotents, 0 and some nonzero one u.
u_A := [u: u in common| u ne A!0][1];
u_is_A := &cat[[x: x in idemps_Vis[i]| Frobenius(x, x) eq 2 and x ne u_A]: i in [1..#idemps_Vis]];
assert #u_is_A eq 3;
// Thus, there are three other idempotents, u_i in V_1(z_i), i :=1, 2, 3.

// Computation 13.6 (d) We need all the  idempotents, u, u_i, z_i in UAlg

u_U := UAlg!AA!Vector(u_A);
u_is_U := [ UAlg!AA!Vector(u_is_A[i]): i in [1..3] ];
assert forall{ u_i: u_i in u_is_U| u_U*u_i eq 0};
// Hence u*u_i=0.

assert forall{ i: i in [1..#u_is_U]| z_is[i] eq u_is_U[i]+u_U};
// So z_i=u+u_i for i := 1, 2, 3.

// Computation 13.7 (a)

assert Eigenvalues(AdjointMatrix(u_U)) eq {<1, 1>, <0, 10>, <1/2, 3>, <1/8, 5>};
_, _, Fusion_law := IdentifyFusionLaw(u_U: eigenvalues := {@1, 0, 1/2, 1/8 @} );
Fusion_law;
// It is evident that the fusion law is almost Monster (1/2, 1/8), with the exception that 1/2*1/2={1,0, 1/2}. Thus, negating the 1/8-space gives rise to an automorphism of U. That is an alternative proof.

// Computation 13.8

W := Eigenspace(AdjointMatrix(u_U), 1/8);
assert Dimension(W) eq 5;
bas_matW := BasisMatrix(W);
// each u_i acts on W since in the fusion law above 0*1/8={1/8}
u_is_on_W := [Matrix([Eltseq(Solution(bas_matW, (UAlg!W.i)*u_is_U[j])): i in [1..5]]): j in [1..3]];
assert forall{ mat: mat in u_is_on_W| Eigenvalues(mat) eq {<25/168, 1>, <1/168, 2>, <3/56, 1>, <7/24, 1> }};

// Computation 13.9 Frobenius form is nondegenerate on T_is

T_is := [Eigenspace(u_is_on_W[i], 7/24): i in [1..3]];
assert forall{T: T in T_is|Dimension(T) eq 1};
assert forall{i: i in [1..3]| Frobenius(x, x) ne 0 where x is A!AA!UAlg!((T_is[i].1)*bas_matW) };
assert forall{i: i in [1..3]| u_is_U[i]*( UAlg!((T_is[i].1)*bas_matW)) eq 7/24*(UAlg!((T_is[i].1)*bas_matW))};
// Just to make sure that the conversion/ lifting to A is correct.

// Computation 13.10 here.
Z := IntegerRing();
f := func<i| IsEven(i) select F!(i/2) else F!((i-1)/2)>;
// function for removing square from the length of an element
// Somehow when you use Magma's factorisation function, it regards powers of factors as real numbers.
ts:=[ (Z!(&*[fact[1]^(fact[2]@f): fact in Factorisation(Denominator(Frobenius(t, t)))]))/(Z!(&*[fact[1]^(fact[2]@f): fact in Factorisation(Numerator(Frobenius(t, t)))]))*t where t is  A!AA!(UAlg!((T_is[i].1)*bas_matW)): i in [1..3]];
assert forall{t: t in ts| Frobenius(t, t) eq 15};
// We now show that (t_i, t_j)=+/- 15/8 for i different from j
// Computation 13.10 (a)

assert forall{ i: i in [1..2]| forall{j :j in [i+1..3]|Frobenius(ts[i], ts[j]) in {-15/8, 15/8} }};

// Computation 13.10 (b) The t_is generate U.

assert Subalgebra(UAlg, [UAlg!(AA!Vector(t)):t in ts]) eq UAlg;


// Computation 13.13 
// In the paper, we recycled the symbols W_i, i:=1, 2, 3, but to distinguish with the current components, we will use WW_i so WWs

WWs := [decomp[x] : x in [<3, 4, 4>,<4, 3, 4>, <4, 4, 3>]];
id_U := IdentityHomomorphism(UAlg);

// Computation 13.13 (a) The identity map on U has 1-dim spaces of (scalar) extensions on the WW_i
extensions_WWs := [phi where bool, phi := HasInducedMap(A, WWs[i], id_U): i in [1..3]];
assert forall{x: x in extensions_WWs |Type(x) eq AlgMat};// so that the identity map extends on each WW_i
assert forall{ ext: ext in extensions_WWs| Dimension(ext) eq 1};
assert forall{ ext: ext in extensions_WWs| IsIdentity(ext.1)};
// Hence the WW_is admit extensions which are scalars multiples of the identity map.

// Computation 13.13 (b). The WWs generate A.

time assert Subalgebra(A, &cat[ Basis(W): W in WWs]) eq AA; 

// Computation 13.14

// At this stage we recycled the use of u. The previous one is no longer necessary.
u := A!U.Random({1..Dimension(U)});
w_s := [A!WWs[i].Random({1..Dimension(WWs[i])}): i in [1..#WWs]];// These are w_1, w_2 and w_3.

// Computation 13.14 (a) (u, w_i*w_i) nonzero
assert forall{w: w in w_s| Frobenius(w*w, u) ne 0};

// Computation 13.14 (b) (w_1*w_2, w_3) nonzero
assert Frobenius(w_s[1]*w_s[2], w_s[3]) ne 0;


