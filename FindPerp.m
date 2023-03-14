FindPerp:=function(A,V,M:bool:=false,form:=IdentityMatrix(BaseField(A),Dimension(A)))
	basV:=Basis(V);basM:=Basis(M);
	if form eq IdentityMatrix(BaseField(A),Dimension(A)) then 
		bool,U:=HasFrobeniusForm(A);
	end if;
		if bool eq false then 
		return "fail";
	else
	m:=#basV;k:=#basM;
	F:=BaseField(A);
	B:=ZeroMatrix(F,k,m);
	for j:=1 to k do
	       for i:=1 to m do
		      B[j][i]+:=FrobFormAtElements(A!basV[i],A!basM[j],U); 
		end for;
	end for;
		_,sol:=Solution(Transpose(B),Vector(F,[0*tt:tt in [1..k]]));
//		print Ncols(B),Nrows(B),m;
		if Dimension(sol) ne 0 then 
			bas:=[ToBigVec(A,V,sol.i):i in [1..Dimension(sol)]];
			return sub<A`W|[A`W!Eltseq(bas[i]):i in [1..#bas]]>;
		else 
			return sol;
		end if; 
	end if;
end function;
