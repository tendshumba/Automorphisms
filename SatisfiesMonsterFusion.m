SatisfiesMonsterFusion:=function(u)/*For this version to work we really have to input u as an element of the axial algebra we have. We assume that you enter u that is actually an idempotent*/
  A:=Parent(u);/*This is the axial algebra in question. */
d:=Dimension(A);
F:=BaseField(A);
axes:=&join[x:x in Axes(A)];/*The function Axes is required so load "Axes.m"*/;
X,_,_:=SubAlg(axes,"a");/*load SubAlgRevised.1*/
X:=[A!x:x in Basis(X)];/*these have to be axial algebra elements.*/
admat:=Matrix(Rationals(),[Eltseq(u*A.i):i in [1..d]]);
Eigs:=Eigenvalues(admat);
Evals:=[x[1]:x in Eigs];
mults:=[x[2]:x in Eigs];
if forall(x){x:x in Evals|x in [1,0,1/4,1/32]} eq false then
  printf "the eigenvalue %o is not in [1,0,1/4,1/32]\n",x;
  return false;
end if;
if &+[x:x in mults] lt d then
   print " Multiplities do not add up.\n";
   return false;
end if;
/*In the calculation these matrices are used multiple times. Precompute them. Should surely speed things up as dimension grow.*/
f0:=fmu(0);
f0_mat:=PolynomialAtMat(f0,admat);
f4:=fmu(1/4);
f4_mat:=PolynomialAtMat(f4,admat);
f32:=fmu(1/32);
f32_mat:=PolynomialAtMat(f32,admat);
f0_0:=Polynomial(Rationals(),[0,1]);
f0_0_mat:=PolynomialAtMat(f0_0,admat);
f0_4:=Polynomial(Rationals(),[-1/4,1]);
f0_4_mat:=PolynomialAtMat(f0_4,admat);
f0_32:=Polynomial(Rationals(),[-1/32,1]);
f0_32_mat:=PolynomialAtMat(f0_32,admat);
f4_4:=Polynomial(Rationals(),[0,-1,1]);
f4_4_mat:=PolynomialAtMat(f4_4,admat);
f4_32:=Polynomial(Rationals(),[-1/32,1]);
f4_32_mat:=PolynomialAtMat(f4_32,admat);
f32_32:=&*[Polynomial(Rationals(),[-x,1]):x in [1,0,1/4]];
f32_32_mat:=PolynomialAtMat(f32_32,admat);
bools:=[];
Append(~bools,forall{x :x in [y:y in CartesianPower([1..#X],2)|y[1] le y[2] ]|(VecToMat((A!Eltseq((VecToMat(X[x[1]]-FrobFormAtElements(X[x[1]],u,U)*u))*f0_mat))*(A!Eltseq((VecToMat(X[x[2]]-FrobFormAtElements(X[x[2]],u,U)*u))*f0_mat))))*f0_0_mat eq VecToMat(A!0)});
Append(~bools,forall{<x,y>:x,y in X|(VecToMat((A!Eltseq((VecToMat(x-FrobFormAtElements(x,u,U)*u))*f0_mat))*(A!Eltseq((VecToMat(y-FrobFormAtElements(y,u,U)*u))*f4_mat))))*f0_4_mat eq VecToMat(A!0)});
Append(~bools,forall{<x,y>:x,y in X|(VecToMat((A!Eltseq((VecToMat(x-FrobFormAtElements(x,u,U)*u))*f0_mat))*(A!Eltseq((VecToMat(y-FrobFormAtElements(y,u,U)*u))*f32_mat))))*f0_32_mat eq VecToMat(A!0)});
Append(~bools,forall{<x,y>:x,y in X|(VecToMat((A!Eltseq((VecToMat(x-FrobFormAtElements(x,u,U)*u))*f4_mat))*(A!Eltseq((VecToMat(y-FrobFormAtElements(y,u,U)*u))*f4_mat))))*f4_4_mat eq VecToMat(A!0)});
Append(~bools,forall{<x,y>:x,y in X|(VecToMat((A!Eltseq((VecToMat(x-FrobFormAtElements(x,u,U)*u))*f4_mat))*(A!Eltseq((VecToMat(y-FrobFormAtElements(y,u,U)*u))*f32_mat))))*f4_32_mat eq VecToMat(A!0)});
Append(~bools,forall{<x,y>:x,y in X|(VecToMat((A!Eltseq((VecToMat(x-FrobFormAtElements(x,u,U)*u))*f32_mat))*(A!Eltseq((VecToMat(y-FrobFormAtElements(y,u,U)*u))*f32_mat))))*f32_32_mat eq VecToMat(A!0)});
return forall{x:x in bools|x eq true}; 
end function;
