/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ AxMat(BaseField(A),Dimension(A))-->boolean, axl alg elment or _ depending +
+ on whether boolean is true or false.                                     +
+                                                                          +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/

IsInducedFromAxisMat:=function(A,mat:one:=A!0,form:=IdentityMatrix(BaseField(A),Dimension(A)))
	/*we assume that the matrix is an automorphism, this will not be checked.*/
	eigs:=[x[1]:x in Eigenvalues(mat)];
	if -1 notin eigs then
		print "-1 is not an eigenvalue";
		return "false",_;
	end if;
	Space:=Eigenspace(mat,-1);
	_,ann:=AnnihilatorOfSpace(A,Basis(Space));
	if Dimension(ann) eq 0 then
		print "The dimension of the annhilator is 0";
		return "false",_;
	end if;
	if one eq A!0 then
		id_bool,one:=HasIdentityAlg(A);
		if id_bool eq true then
			one:=A!one;
		end if;
	end if;
	ax:=FindAllIdempotents(A,sub<A`W|A`W!Eltseq(one)>+ann:length:=1,one:=one, form :=form);
	if #ax eq 0 then
		return "false",_;
	else
		ax:=[x:x in ax|HasMonsterFusion(x)];
		if #ax eq 0 then
			return "false",_;
		elif #ax gt 0 then
			return "true",ax;
		end if;
	end if;
	end function;
